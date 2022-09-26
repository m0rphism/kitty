module KitTheory.GenericsDerive where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.ActionsClass hiding (⟦_⟧)
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Actions
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Named.Substitution
open import ReflectionLib.Categorical
open import ReflectionLib.Algorithms.Fin
open import ReflectionLib.Algorithms.Nat

open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; length; drop; zip; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Function using (_∘_; _$_; case_of_)

open import KitTheory.Prelude using (_∋_)
open import KitTheory.Modes
open import KitTheory.Generics
open import KitTheory.Iso

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ
  F : Functor' ℓ
  VM TM : Set

-- Helpers ---------------------------------------------------------------------

_by_ : (A : Set ℓ) → A → A
A by a = a

FreshTC = FreshT {0ℓ} TC

subst-pi : Type' → Term' → Type'
subst-pi (pi a (abs x b)) t' = (b [ x ↦ t' ])
subst-pi t                t' = t

split-term-ctors : List Name → FreshTC (Name × List Name)
split-term-ctors []       = liftTC $ failStr "No variable constructor found"
split-term-ctors (c ∷ cs) = return (c , cs)

type→name : Type' → TC Name
type→name (def nm args) = return nm
type→name t = failStr "Type is not a Name."

_isTCon_ : Type' → Name → Bool
def nm args isTCon nm' = primQNameEquality nm nm' 
_           isTCon _   = false 

splitRec : Telescope' → Name → Telescope' × Telescope'
splitRec []                      nm = [] , []
splitRec (b@(x , arg i t) ∷ tel) nm =
  let tel-rec , tel = splitRec tel nm in
  if t isTCon nm then (b ∷ tel-rec , tel)
                else (tel-rec , b ∷ tel)

foldrM' : {T : Functor' ℓ} {{_ : Traversable ℓ T}}
          {F : Functor' ℓ'} {{_ : Monad ℓ' F}}
        → T A → F B → (A → B → F B) → F B
foldrM' ta b0 f = foldrM f b0 ta

unterm : Name → Term' → Maybe (Term' × Term')
unterm Term-nm (def f [ argᵥ µ ; argᵥ M ]) =
  if primQNameEquality f Term-nm
    then just (µ , M)
    else nothing
unterm Term-nm _ = nothing

cong-Σ : {A : Set ℓ₁} {B : A → Set ℓ₂} {x y : A} {u : B x} {v : B y} →
      (p : x ≡ y) → subst B p u ≡ v → (x , u) ≡ (y , v)
cong-Σ refl refl = refl

cong-× : {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} {u v : B} →
      x ≡ y → u ≡ v → (x , u) ≡ (y , v)
cong-× refl refl = refl

uip : ∀ {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl

-- Deriving Desc ---------------------------------------------------------------

-- TODO: rewrite `■ ++ µ` to `■` and then `µ` to `[]`
deriveDesc : Name → Name → Name → TC ⊤
deriveDesc modes-nm Term-nm desc-nm = runFreshT do
  modes  ← unquoteTC {A = Modes} (def modes-nm [])
  Term-def ← getDefinition Term-nm
  _ , term-cons ← split-term-ctors (ctors Term-def)
  clauses ← forM (enumerate term-cons) λ (i , c) → do
    c-ty ← getType' c
    let c-ty = subst-pi c-ty (con (quote List.List.[]) [])
    let (c-tel , c-ret) = pi→tel c-ty
    desc ← foldrM'
      c-tel
      (case c-ret of λ where
        (def f [ µ ; M ]) → pure (con (quote `■) [ M ])
        _                 → liftTC $ failStr "Unexpected constructor type")
      λ where
        (x , arg i arg-ty) desc → case unterm Term-nm arg-ty of λ where
          (just (µ , M)) → do
            pure (con (quote `X) [ argᵥ µ ; argᵥ M ; argᵥ desc ])
          nothing → do
            desc ← unquoteTC' desc
            a ← unquoteTC' arg-ty
            quoteTC' (`σ {𝕄 = modes} a (λ _ → desc))
    pure $ clause [] [ argᵥ (fin-pat' i) ] desc
  f ← unquoteTC' (pat-lam clauses [])
  desc ← quoteNormTC' (`σ {𝕄 = modes} (Fin (length term-cons)) f)
  defdecFun'
    (argᵥ desc-nm)
    (def (quote Desc) [ argᵥ (def modes-nm []) ])
    [ clause [] [] desc ]

-- Derving To ------------------------------------------------------------------

deriveTo : Name → Name → Name → Name → TC ⊤
deriveTo modes-nm Term-nm desc-nm to-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  var-c , term-cs ← split-term-ctors $ ctors ty
  modes  ← unquoteTC {A = Modes} (def modes-nm [])
  Term ← unquoteTC' {A = Scoped modes} (def Term-nm [])
  d ← unquoteTC' (def desc-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con var-c [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con (quote `var) [ argₕ unknown ; argₕ unknown ; argᵥ (var "x" []) ])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    c-ty ← getType' c
    let c-tel , c-ret = pi→tel c-ty
    let c-tel' = List.drop 1 c-tel
    `µ ← case List.head c-tel of λ where
      (just (x , _)) → pure x
      nothing        → liftTC $ failStr "No µ found."
    let ps = tel→patterns c-tel'
    let t = foldr
          (λ { (x , arg i tx) t → case unterm Term-nm tx of λ where
            (just (µ , M)) → con (quote _,_) [ argᵥ (def to-nm [ argᵥ (var x []) ]) ; argᵥ t ]
            nothing        → con (quote _,_) [ argᵥ (var x []) ; argᵥ t ]
          })
          (con (quote refl) [])
          c-tel'
    pure $ clause
      c-tel
      [ argᵥ (con c (argₕ (var `µ) ∷ ps)) ]
      (con (quote `con) [ (argᵥ (con (quote _,_) [ argᵥ (fin-con' i) ; argᵥ t ])) ])
  to-ty ← quoteTC' (∀ {µ} {M} → Term µ M → Tm modes d µ M)
  defdecFun'
    (argᵥ to-nm)
    to-ty
    (var-clause ∷ term-clauses)

-- Deriving From ---------------------------------------------------------------

deriveFrom : Name → Name → Name → Name → TC ⊤
deriveFrom modes-nm Term-nm desc-nm from-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  var-c , term-cs ← split-term-ctors $ ctors ty
  modes  ← unquoteTC {A = Modes} (def modes-nm [])
  Term ← unquoteTC' {A = Scoped modes} (def Term-nm [])
  d ← unquoteTC' (def desc-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con (quote `var) [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con var-c [ argᵥ (var "x" []) ])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    c-ty ← getType' c
    let c-tel , c-ret = pi→tel c-ty
    let c-tel' = List.drop 1 c-tel
    `µ ← case List.head c-tel of λ where
      (just (x , _)) → pure x
      nothing        → liftTC $ failStr "No µ found."
    let ts = List.map (λ { (x , arg i tx) → case unterm Term-nm tx of λ where
            (just (µ , M)) → argᵥ (def from-nm [ argᵥ (var x []) ])
            nothing        → argᵥ (var x [])
          }) c-tel'
    let p = foldr
          (λ { (x , arg i tx) p → con (quote _,_) [ argᵥ (var x) ; argᵥ p ] })
          (con (quote refl) [])
          c-tel'
    let c-tel'' = List.map
          (λ { (x , arg i t) → case unterm Term-nm t of λ where
            (just (µ , M)) → (x , arg i (def (quote Tm) [ argᵥ (def modes-nm []) ; argᵥ (def desc-nm []) ; argᵥ µ ; argᵥ M ]))
            nothing        → (x , arg i t)
          })
          c-tel
    pure $ clause
      c-tel''
      [ argᵥ (con (quote `con)
        [ argₕ (var `µ)
        ; argᵥ (con (quote _,_) [ argᵥ (fin-pat' i) ; argᵥ p ])
        ])
      ]
      (con c ts)
  from-ty ← quoteTC' (∀ {µ} {M} → Tm modes d µ M → Term µ M)
  defdecFun' (argᵥ from-nm) from-ty (var-clause ∷ term-clauses)

-- Deriving n-ary cong ---------------------------------------------------------

-- cong₂ : ∀ {a : Level} {A : Set a}
--           {b : Level} {B : Set b}
--           {c : Level} {C : Set c}
--           (f : A → B → C)
--           {x y : A}
--           {u v : B}
--         → x ≡ y
--         → u ≡ v
--         → f x u ≡ f y v
-- cong₂ f refl refl = refl

cong-n : ℕ → Name → FreshT TC ⊤
cong-n n nm = do
  levels    ← fresh-ids n "ℓ"
  sets      ← fresh-ids n "A"
  out-level ← fresh-id "ℓ"
  out-set   ← fresh-id "A"
  let all-levels = levels ++ [ out-level ]
  let all-sets   = sets ++ [ out-set ]
  let level-tel  = map (λ ℓ → (ℓ , argₕ (def (quote Level) []))) all-levels
  let set-tel    = map (λ (ℓ , A) → (A , argₕ (agda-sort (set (var ℓ []))))) (zip all-levels all-sets)
  f ← fresh-id "f"
  let f-ty  = tel→pi (map (λ A → ("_" , argᵥ (var A []))) sets) (var out-set [])
  let f-tel = [ f , argᵥ f-ty ]
  args-x ← fresh-ids (length sets) "x"
  args-y ← fresh-ids (length sets) "y"
  let args-x-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-x sets)
  let args-y-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-y sets)
  let eq-tel = map
        (λ (x , y) → ("_", argᵥ (def (quote _≡_) [ argᵥ (var x []) ; argᵥ (var y []) ])))
        (zip args-x args-y)
  let eq-res = def (quote _≡_) [ argᵥ (var f (map (λ x → argᵥ (var x [])) args-x))
                               ; argᵥ (var f (map (λ y → argᵥ (var y [])) args-y)) ]
  let tel = level-tel ++ set-tel ++ f-tel ++ args-x-tel ++ args-y-tel ++ eq-tel
  let cong-ty = tel→pi tel eq-res
  let cong-clause = clause
        (level-tel ++ set-tel ++ f-tel)
        (List.map (λ x → argₕ (var x)) all-levels ++
        List.map (λ x → argₕ (var x)) all-sets ++
        argᵥ (var f) ∷ List.map (λ _ → argᵥ (con (quote refl) [])) eq-tel)
        (con (quote refl) [])
  defdecFun' (argᵥ nm) cong-ty [ cong-clause ]

-- Deriving from∘to ------------------------------------------------------------

deriveFromToClause : Name → Name → FreshT TC Clause'
deriveFromToClause from∘to-nm con-nm = do
  con-ty ← getType' con-nm
  let tel , ret-ty = pi→tel con-ty
  ret-nm ← liftTC $ type→name ret-ty
  let tel-rec , tel-non-rec = splitRec tel ret-nm
  let rec-ids = map proj₁ tel-rec
  let non-rec-ids = map proj₁ tel-non-rec
  cong-name ← freshName "cong-n"
  cong-n (length rec-ids) cong-name
  let cong-fun = tel→lam tel-rec $ con con-nm $
                  List.map (λ{ (x , arg i t) → arg i (var x [])}) tel
  return $ clause
    tel
    [ argᵥ (con con-nm (tel→patterns tel)) ]
    (def cong-name (argᵥ cong-fun ∷ List.map (λ x → argᵥ (def from∘to-nm [ argᵥ (var x []) ])) rec-ids))

deriveFromTo : Name → Name → Name → Name → Name → Name → TC ⊤
deriveFromTo modes-nm Term-nm desc-nm to-nm from-nm from∘to-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
  modes ← unquoteTC {A = Modes} (def modes-nm [])
  Term  ← unquoteTC {A = Scoped modes} (def Term-nm [])
  d     ← unquoteTC {A = Desc modes} (def desc-nm [])
  from  ← unquoteTC {A = ∀ {µ M} → Tm modes d µ M → Term µ M} (def from-nm [])
  to    ← unquoteTC {A = ∀ {µ M} → Term µ M → Tm modes d µ M} (def to-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con var-c [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con (quote refl) [])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    deriveFromToClause from∘to-nm c
  from∘to-ty ← quoteTC' (∀ {µ} {M} → (x : Term µ M) → from (to x) ≡ x)
  defdecFun' (argᵥ from∘to-nm) from∘to-ty (var-clause ∷ term-clauses)

-- Deriving to∘from ------------------------------------------------------------

deriveToFromClause : Name → Name → Name → Name → Name → ℕ → FreshT TC Clause'
deriveToFromClause modes-nm Term-nm desc-nm to∘from-nm con-nm con-i = do
  c-ty ← getType' con-nm
  let c-tel , c-ret = pi→tel c-ty
  let c-tel' = List.drop 1 c-tel
  `µ ← case List.head c-tel of λ where
    (just (x , _)) → pure x
    nothing        → liftTC $ failStr "No µ found."
  -- Same as `from`
  let p = foldr
        (λ { (x , arg i tx) p → con (quote _,_) [ argᵥ (var x) ; argᵥ p ] })
        (con (quote refl) [])
        c-tel'
  -- Same as `from`
  let c-tel'' = List.map
        (λ { (x , arg i t) → case unterm Term-nm t of λ where
          (just (µ , M)) → (x , arg i (def (quote Tm) [ argᵥ (def modes-nm []) ; argᵥ (def desc-nm []) ; argᵥ µ ; argᵥ M ]))
          nothing        → (x , arg i t)
        })
        c-tel

  let e = foldr
            (λ { (x , arg i t) e → case unterm Term-nm t of λ where
              (just (µ , M)) → def (quote cong-×) [ argᵥ (def to∘from-nm [ argᵥ (var x []) ]) ; argᵥ e ]
              nothing        → def (quote cong-×) [ argᵥ (con (quote refl) []) ; argᵥ e ]
            })
            (con (quote refl) [])
            c-tel'

  ret-nm ← liftTC $ type→name c-ret
  let tel-rec , tel-non-rec = splitRec c-tel ret-nm
  let rec-ids = map proj₁ tel-rec
  let non-rec-ids = map proj₁ tel-non-rec
  return $ clause
    c-tel''
    [ argᵥ (con (quote `con)
      [ argₕ (var `µ)
      ; argᵥ (con (quote _,_) [ argᵥ (fin-pat' con-i) ; argᵥ p ]) ])
    ]
    (def (quote cong)
      [ argᵥ (con (quote `con) [])
      ; argᵥ (def (quote cong-Σ)
        [ argᵥ (con (quote refl) [])
        ; argᵥ e
        ])
      ])

import ReflectionLib.Standard.Pretty as PP

deriveToFrom : Name → Name → Name → Name → Name → Name → TC ⊤
deriveToFrom modes-nm Term-nm desc-nm to-nm from-nm to∘from-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
  modes ← unquoteTC {A = Modes} (def modes-nm [])
  Term  ← unquoteTC {A = Scoped modes} (def Term-nm [])
  d     ← unquoteTC {A = Desc modes} (def desc-nm [])
  from  ← unquoteTC {A = ∀ {µ M} → Tm modes d µ M → Term µ M} (def from-nm [])
  to    ← unquoteTC {A = ∀ {µ M} → Term µ M → Tm modes d µ M} (def to-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_)
                [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con (quote `var) [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con (quote refl) [])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    deriveToFromClause modes-nm Term-nm desc-nm to∘from-nm c i
  to∘from-ty ← quoteTC' (∀ {µ} {M} → (x : Tm modes d µ M) → to (from x) ≡ x)
  defdecFun' (argᵥ to∘from-nm) to∘from-ty (var-clause ∷ term-clauses)

-- Deriving the Isomorphism ----------------------------------------------------

deriveIso : Name → Name → Name → TC ⊤
deriveIso modes-nm Term-nm Iso-nm = do
  printAST "–– deriveIso –––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––"
  desc-nm    ← freshName "d"
  to-nm      ← freshName "to"
  from-nm    ← freshName "from"
  from∘to-nm ← freshName "from∘to"
  to∘from-nm ← freshName "to∘from"
  deriveDesc   modes-nm Term-nm desc-nm
  deriveTo     modes-nm Term-nm desc-nm to-nm
  deriveFrom   modes-nm Term-nm desc-nm from-nm
  deriveFromTo modes-nm Term-nm desc-nm to-nm from-nm from∘to-nm
  deriveToFrom modes-nm Term-nm desc-nm to-nm from-nm to∘from-nm
  modes    ← unquoteTC {A = Modes} (def modes-nm [])
  Term     ← unquoteTC {A = Scoped modes} (def Term-nm [])
  d        ← unquoteTC {A = Desc modes} (def desc-nm [])
  iso-ty   ← quoteTC (∀ {µ} {M} → (Term µ M) ≃ Tm modes d µ M)
  defdecFun
    (argᵥ Iso-nm)
    iso-ty
    [ clause [] [] (con (quote iso)
      [ argᵥ (def to-nm [])
      ; argᵥ (def from-nm [])
      ; argᵥ (def from∘to-nm [])
      ; argᵥ (def to∘from-nm [])
      ])
    ]

deriveIso' : (𝕄 : Modes)
           → Scoped 𝕄
           → Name
           → TC ⊤
deriveIso' modes Term Iso-nm = do
  modes-nm    ← type→name =<< runFreshT (quoteTC' modes)
  Term-nm     ← type→name =<< runFreshT (quoteTC' Term)
  deriveIso modes-nm Term-nm Iso-nm

-- Example ---------------------------------------------------------------------

private module STLC where

  data VarMode : Set where
    𝕧 : VarMode

  data TermMode : Set where
    𝕥 : TermMode

  m→M : VarMode → TermMode
  m→M 𝕧 = 𝕥

  𝕄 : Modes
  𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

  data _⊢_ : List VarMode → TermMode → Set where
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
    `λ_ : ∀ {µ} → (𝕧 ∷ µ) ⊢ 𝕥 → µ ⊢ 𝕥
    _·_ : ∀ {µ} → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕥

  unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  open FromIso 𝕄 Iso

  -- xx = {!_⋯ₛ_!}


  -- unquoteDecl Iso = deriveIso (quote 𝕄) (quote _⊢_) Iso
  -- unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso
  -- unquoteDecl STLC    = deriveDesc   (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) STLC
  -- unquoteDecl to      = deriveTo     (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) to
  -- unquoteDecl from    = deriveFrom   (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) from
  -- unquoteDecl from∘to = deriveFromTo (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) (quote to) (quote from) from∘to
  -- unquoteDecl to∘from = deriveToFrom (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) (quote to) (quote from) to∘from

  -- Iso' : ∀ {µ} {M} → (µ ⊢ M) ≃ Tm STLC µ M
  -- Iso' = iso to from from∘to to∘from

  -- xx = {!Iso!}

  -- unquoteDecl cong₃ = runFreshT (cong-n 3 cong₃)

  -- STLC' : Desc
  -- STLC' = `σ (Fin 2) λ where
  --   zero       → `X (𝕧 ∷ []m) 𝕥 (`■ 𝕥)
  --   (suc zero) → `X []m 𝕥 (`X []m 𝕥 (`■ 𝕥))
  --   (suc (suc ()))

  -- to' : ∀ {µ M} → (µ ⊢ M) → Tm STLC µ M
  -- to' (` x)     = `var x
  -- to' (`λ e)    = `con (zero , to' e , refl)
  -- to' (e₁ · e₂) = `con (suc zero , to' e₁ , to' e₂ , refl)

  -- from' : ∀ {µ M} → Tm STLC µ M → (µ ⊢ M)
  -- from' (`var x)                           = ` x
  -- from' (`con (zero , e , refl))           = `λ (from' e)
  -- from' (`con (suc zero , e₁ , e₂ , refl)) = from' e₁ · from' e₂

  -- from∘to' : ∀ {µ M} → (a : µ ⊢ M) → from (to a) ≡ a
  -- from∘to' (` x)     = refl
  -- from∘to' (`λ e)    = cong `λ_ (from∘to' e)
  -- from∘to' (e₁ · e₂) = cong₂ _·_ (from∘to' e₁) (from∘to' e₂)

  -- -- TODO: make deriving work for dependent constructors...
  -- to∘from' : ∀ {µ M} → (a : Tm STLC µ M) → to (from a) ≡ a
  -- to∘from' (`var x)                           = refl
  -- to∘from' (`con (zero , e , refl))           = cong `con (cong-Σ refl (cong-× (to∘from' e) refl))
  -- to∘from' (`con (suc zero , e₁ , e₂ , refl)) = cong `con (cong-Σ refl (cong-× (to∘from' e₁) (cong-× (to∘from' e₂) refl)))
  -- -- to∘from' (`con (zero , e , refl))           = cong `con (cong-Σ refl (
  -- --                                               cong-Σ (to∘from' e) uip))
  -- -- to∘from' (`con (suc zero , e₁ , e₂ , refl)) = cong `con (cong-Σ refl (
  -- --                                               cong-Σ (to∘from' e₁) (
  -- --                                               cong-Σ {!to∘from' e₂!} {!!})))

  -- -- -- STLC-correct : STLC ≡ STLC'
  -- -- -- STLC-correct = refl

  -- -- -- to-correct : ∀ {µ M} (t : µ ⊢ M) → to t ≡ to' t
  -- -- -- to-correct (` x) = refl
  -- -- -- to-correct (`λ t) rewrite to-correct t = refl
  -- -- -- to-correct (t₁ · t₂) rewrite to-correct t₁ |  to-correct t₂ = refl

  -- -- -- from-correct : ∀ {µ M} (t : Tm STLC µ M) → from t ≡ from' t
  -- -- -- from-correct (`var x) = refl
  -- -- -- from-correct (`con (zero , t , refl)) rewrite from-correct t = refl
  -- -- -- from-correct (`con (suc zero , t₁ , t₂ , refl)) rewrite from-correct t₁ | from-correct t₂ = refl

