-- Causes ReflectionLib.print* to print into the "*Agda Debug*" buffer.
{-# OPTIONS -vreflection-debug:10 #-}

module ReflectionLib.ExamplesFresh where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.Substitution
open import ReflectionLib.Standard.ActionsClass hiding (⟦_⟧)
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Actions
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Categorical
open import ReflectionLib.Algorithms.Fin using (fin-pat; fin-con)

open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; length; drop; zip; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Function using (_∘_; _$_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  F : Functor' ℓ

_by_ : (A : Set ℓ) → A → A
A by a = a

-- Domain ----------------------------------------------------------------------

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
xs ∋ x = x ∈ xs

data VarMode : Set where
  𝕧 : VarMode
data TermMode : Set where
  𝕥 : TermMode

m→M : VarMode → TermMode
m→M 𝕧 = 𝕥

Scoped : Set₁
Scoped = List VarMode → TermMode → Set

data Desc : Set₁ where
  `σ : (A : Set) → (A → Desc) → Desc
  `X : List VarMode → TermMode → Desc → Desc
  `■ : TermMode → Desc

⟦_⟧ : Desc → Scoped → Scoped
⟦ `σ A d     ⟧ X µ M = Σ[ a ∈ A ] (⟦ d a ⟧ X µ M)
⟦ `X µ' M' d ⟧ X µ M = X (µ' ++ µ) M' × ⟦ d ⟧ X µ M
⟦ `■ M'      ⟧ X µ M = M ≡ M'

data Tm (d : Desc) : Scoped where
  `var : ∀ {µ m} → µ ∋ m → Tm d µ (m→M m)
  `con : ∀ {µ M} → ⟦ d ⟧ (Tm d) µ M → Tm d µ M

-- Helpers ---------------------------------------------------------------------

subst-pi : Type → Term → Type
subst-pi (pi a (abs x b)) t' = (b [ 0 ↦ t' ])
subst-pi t                t' = t

drop-pi : ℕ → Type → Type
drop-pi zero    t                = t
drop-pi (suc n) (pi a (abs x b)) = drop-pi n b
drop-pi (suc n) t                = t

split-term-ctors : List Name → TC (Name × List Name)
split-term-ctors []       = failStr "No variable constructor found"
split-term-ctors (c ∷ cs) = return (c , cs)

[]m : List VarMode
[]m = []

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

-- Deriving Desc ---------------------------------------------------------------

argDesc : Name → Term → Type → TC Term
argDesc ty-id desc arg-ty@(def f (µ ∷ M ∷ [])) with primQNameEquality f ty-id
... | true = do
  -- µ ← extract-µ (arg-val µ)
  return (con (quote `X) (µ ∷ M ∷ argᵥ desc ∷ []))
... | false = do
  desc ← unquoteTC desc
  a ← unquoteTC arg-ty
  quoteTC (`σ a (λ _ → desc))
argDesc ty-id desc arg-ty = do
  desc ← unquoteTC desc
  a ← unquoteTC arg-ty
  quoteTC (`σ a (λ _ → desc))

deriveCtorDesc : Name → Type → TC Term
deriveCtorDesc ty-id (def f (µ ∷ M ∷ [])) with primQNameEquality f ty-id
... | true  = return (con (quote `■) (M ∷ []))
... | false = failStr "Unexpected constructor type"
deriveCtorDesc ty-id (def f args) = failStr "Unexpected type arity"
deriveCtorDesc ty-id (pi a (abs _ b)) = do
  desc ← deriveCtorDesc ty-id b
  argDesc ty-id desc (arg-val a)
deriveCtorDesc ty-id _ = failStr "Unexpected type in constructor argument"

deriveDesc : (ty-id desc-id : Name) → TC ⊤
deriveDesc ty-id desc-id = do
  ty ← getDefinition ty-id
  let cs = drop 1 (ctors ty)
  clauses ← forM (enumerate cs) λ (i , ctor) → do
    cty ← getType ctor
    -- Remove the leading `∀ {µ} →` of all constructors and replace
    -- the `µ` with `[]`. TODO: this may create `µ' ++ []` in `Desc`...
    let cty = subst-pi cty (quoteTerm []m)
    desc ← deriveCtorDesc ty-id cty
    return (clause [] (argᵥ (fin-pat i) ∷ []) desc)
  f ← unquoteTC (pat-lam clauses [])
  desc ← quoteNormTC (`σ (Fin (length cs)) f)
  defdecFun (argᵥ desc-id) (quoteTerm Desc) ((clause [] [] desc) ∷ [])

-- Derving To ------------------------------------------------------------------

deriveToClause' : (ty-id desc-id to-id : Name) → Type → TC (Telescope × List (Arg Pattern) × Term)
deriveToClause' ty-id desc-id to-id (pi (argᵥ a@(def ty-id' (µ ∷ M ∷ []))) (abs x b))
 with primQNameEquality ty-id ty-id'
... | true = do
  tel' , ps' , t' ← deriveToClause' ty-id desc-id to-id b
  return $
    (x , argᵥ a) ∷ tel' ,
    argᵥ (var (length ps')) ∷ ps' ,
    con (quote _,_) (argᵥ (def to-id (argᵥ (var (length ps') []) ∷ [])) ∷ argᵥ t' ∷ [])
... | false = do
  tel' , ps' , t' ← deriveToClause' ty-id desc-id to-id b
  return $
    (x , argᵥ a) ∷ tel' ,
    argᵥ (var (length ps')) ∷ ps' ,
    con (quote _,_) (argᵥ (var (length ps') []) ∷ argᵥ t' ∷ [])
deriveToClause' ty-id desc-id to-id (pi a (abs x b)) = do
  tel' , ps' , t' ← deriveToClause' ty-id desc-id to-id b
  return $
    (x , a) ∷ tel' ,
    arg (arg-inf a) (var (length ps')) ∷ ps' ,
    con (quote _,_) ( argᵥ (var (length ps') [])
                    ∷ argᵥ t'
                    ∷ [])
deriveToClause' ty-id desc-id to-id t = do
  return $ [] , [] , con (quote refl) []

deriveToClause : (ty-id desc-id to-id con-id : Name) → ℕ → TC Clause
deriveToClause ty-id desc-id to-id con-id con-ix = do
  con-ty ← getType con-id
  let con-ty = drop-pi 1 con-ty
  tel , ps , t ← deriveToClause' ty-id desc-id to-id con-ty
  return $ clause
    (("µ" , argₕ (quoteTerm (List VarMode))) ∷ tel)
    (argᵥ (con con-id (argₕ (var (length ps)) ∷ ps)) ∷ [])
    (con (quote `con)
      ((argᵥ (con (quote _,_)
        (argᵥ (fin-con con-ix) ∷
         argᵥ t ∷
         []))) ∷
       []))

deriveTo : (ty-id desc-id to-id : Name) → TC ⊤
deriveTo ty-id desc-id to-id = do
  ty ← getDefinition ty-id
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
  Term ← unquoteTC {A = List VarMode → TermMode → Set} (def ty-id [])
  d ← unquoteTC (def desc-id [])
  let var-clause = clause
        (("µ" , argₕ (quoteTerm (List VarMode))) ∷
         ("m" , argₕ (quoteTerm VarMode)) ∷
         ("x" , argᵥ (def (quote _∋_)
                (argₕ unknown ∷ argₕ unknown ∷ argᵥ (var 1 []) ∷ argᵥ (var 0 []) ∷ []))) ∷
         [])
        (argᵥ (con var-c (argₕ (var 2) ∷ argₕ (var 1) ∷ argᵥ (var 0) ∷ [])) ∷ [])
        (con (quote `var) (argₕ unknown ∷ argₕ unknown ∷ argᵥ (var 0 []) ∷ []))
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    deriveToClause ty-id desc-id to-id c i
  to-ty ← quoteTC (∀ {µ : List VarMode} {M : TermMode} → Term µ M → Tm d µ M)
  defdecFun
    (argᵥ to-id)
    to-ty
    (var-clause ∷ term-clauses)

-- Deriving From ---------------------------------------------------------------

deriveFromClause' : (ty-id desc-id from-id : Name) → Type → TC (Telescope × Pattern × List (Arg Term))
deriveFromClause' ty-id desc-id from-id (pi (argᵥ a@(def ty-id' (µ ∷ M ∷ []))) (abs x b))
 with primQNameEquality ty-id ty-id'
... | true = do
  tel' , p' , ts' ← deriveFromClause' ty-id desc-id from-id b
  return $
    -- FIXME: using µ here is probably not correct (µ vs µ' ++ µ)
    (x , argᵥ (def (quote Tm) (argᵥ (def desc-id []) ∷ µ ∷ M ∷ []))) ∷ tel' ,
    con (quote _,_) (argᵥ (var (length ts')) ∷ argᵥ p' ∷ []) ,
    argᵥ (def from-id (argᵥ (var (length ts') []) ∷ [])) ∷ ts'
... | false = do
  tel' , p' , ts' ← deriveFromClause' ty-id desc-id from-id b
  return $
    (x , argᵥ a) ∷ tel' ,
    con (quote _,_) ( argᵥ (var (length ts'))
                    ∷ argᵥ p'
                    ∷ []) ,
    argᵥ (var (length ts') []) ∷ ts'
deriveFromClause' ty-id desc-id from-id (pi a (abs x b)) = do
  tel' , p' , ts' ← deriveFromClause' ty-id desc-id from-id b
  return $
    (x , a) ∷ tel' ,
    con (quote _,_) ( argᵥ (var (length ts'))
                    ∷ argᵥ p'
                    ∷ []) ,
    arg (arg-inf a) (var (length ts') []) ∷ ts'
deriveFromClause' ty-id desc-id from-id t = do
  return $ [] , con (quote refl) [] , []

deriveFromClause : (ty-id desc-id from-id con-id : Name) → ℕ → TC Clause
deriveFromClause ty-id desc-id from-id con-id con-ix = do
  con-ty ← getType con-id
  let con-ty = drop-pi 1 con-ty
  tel , p , ts ← deriveFromClause' ty-id desc-id from-id con-ty
  return $ clause
    (("µ" , argₕ (quoteTerm (List VarMode))) ∷ tel)
    (argᵥ (con (quote `con)
      ( argₕ (var (length ts)) ∷
        argᵥ (con (quote _,_) (argᵥ (fin-pat con-ix) ∷ argᵥ p ∷ [])) ∷ [])
    ) ∷ [])
    (con con-id ts )

deriveFrom : (ty-id desc-id from-id : Name) → TC ⊤
deriveFrom ty-id desc-id from-id = do
  ty ← getDefinition ty-id
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
  Term ← unquoteTC {A = List VarMode → TermMode → Set} (def ty-id [])
  d ← unquoteTC (def desc-id [])
  let var-clause = clause
        (("µ" , argₕ (quoteTerm (List VarMode))) ∷
         ("m" , argₕ (quoteTerm VarMode)) ∷
         ("x" , argᵥ (def (quote _∋_)
                (argₕ unknown ∷ argₕ unknown ∷ argᵥ (var 1 []) ∷ argᵥ (var 0 []) ∷ []))) ∷
         [])
        (argᵥ (con (quote `var) (argₕ (var 2) ∷ argₕ (var 1) ∷ argᵥ (var 0) ∷ [])) ∷ [])
        (con var-c (argₕ unknown ∷ argₕ unknown ∷ argᵥ (var 0 []) ∷ []))
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    deriveFromClause ty-id desc-id from-id c i
  from-ty ← quoteTC (∀ {µ : List VarMode} {M : TermMode} → Tm d µ M → Term µ M)
  defdecFun
    (argᵥ from-id)
    from-ty
    (var-clause ∷ term-clauses)

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
  levels ← fresh-ids n "ℓ"
  sets   ← fresh-ids n "A"
  out-level ← fresh-id "ℓ"
  out-set   ← fresh-id "A"
  let all-levels = levels ++ out-level ∷ []
  let all-sets   = sets ++ out-set ∷ []
  let level-tel = map (λ ℓ → (ℓ , argₕ (def (quote Level) []))) all-levels
  let set-tel = map (λ (ℓ , A) → (A , argₕ (agda-sort (set (var ℓ []))))) (zip all-levels all-sets)
  f ← fresh-id "f"
  let f-ty = tel→pi (map (λ A → ("_" , argᵥ (var A []))) sets) (var out-set [])
  let f-tel = (f , argᵥ f-ty) ∷ []
  args-x ← fresh-ids (length sets) "x"
  args-y ← fresh-ids (length sets) "y"
  let args-x-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-x sets)
  let args-y-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-y sets)
  let eq-tel = map
        (λ (x , y) → ("_", argᵥ (def (quote _≡_) (argᵥ (var x []) ∷ argᵥ (var y []) ∷ []))))
        (zip args-x args-y)
  let eq-res = def (quote _≡_) (argᵥ (var f (map (λ x → argᵥ (var x [])) args-x)) ∷
                                argᵥ (var f (map (λ y → argᵥ (var y [])) args-y)) ∷ [])
  let tel = level-tel ++ set-tel ++ f-tel ++ args-x-tel ++ args-y-tel ++ eq-tel
  let cong-ty = tel→pi tel eq-res
  let cong-clause = clause
        (level-tel ++ set-tel ++ f-tel)
        (List.map (λ x → argₕ (var x)) all-levels ++
         List.map (λ x → argₕ (var x)) all-sets ++
         argᵥ (var f) ∷ List.map (λ _ → argᵥ (con (quote refl) [])) eq-tel)
        (con (quote refl) [])
  defdecFun'
    (argᵥ nm)
    cong-ty
    (cong-clause ∷ [])

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
    (argᵥ (con con-nm (tel→patterns tel)) ∷ [])
    (def cong-name (argᵥ cong-fun ∷ List.map (λ x → argᵥ (def from∘to-nm (argᵥ (var x []) ∷ []))) rec-ids))

deriveFromTo : (ty-id desc-id to-id from-id from∘to-id : Name) → TC ⊤
deriveFromTo ty-id desc-id to-id from-id from∘to-id = runFreshT $ do
  ty ← getDefinition ty-id
  let cs = ctors ty
  var-c , term-cs ← liftTC $ split-term-ctors cs
  Term ← unquoteTC {A = List VarMode → TermMode → Set} (def ty-id [])
  d ← unquoteTC {A = Desc} (def desc-id [])
  from ← unquoteTC {A = ∀ {µ M} → Tm d µ M → Term µ M} (def from-id [])
  to ← unquoteTC {A = ∀ {µ M} → Term µ M → Tm d µ M} (def to-id [])
  let var-clause = clause
        (("µ" , argₕ (quoteTerm (List VarMode))) ∷
         ("m" , argₕ (quoteTerm VarMode)) ∷
         ("x" , argᵥ (def (quote _∋_)
                (argₕ unknown ∷ argₕ unknown ∷ argᵥ (var 1 []) ∷ argᵥ (var 0 []) ∷ []))) ∷
         [])
        (argᵥ (con var-c (argₕ (var 2) ∷ argₕ (var 1) ∷ argᵥ (var 0) ∷ [])) ∷ [])
        (con (quote refl) [])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    c' ← deriveFromToClause from∘to-id c
    liftTC $ to-debruijn c'
  from-ty ← quoteTC (∀ {µ : List VarMode} {M : TermMode} → (x : Term µ M) → from (to x) ≡ x)
  defdecFun
    (argᵥ from∘to-id)
    from-ty
    (var-clause ∷ term-clauses)

-- Deriving the Isomorphism ----------------------------------------------------

deriveIso : (ty-id desc-id to-id from-id from∘to-id : Name) → TC ⊤
deriveIso ty-id desc-id to-id from-id from∘to-id = do
  printAST "–– deriveIso –––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––"
  deriveDesc ty-id desc-id
  deriveTo ty-id desc-id to-id
  deriveFrom ty-id desc-id from-id
  deriveFromTo ty-id desc-id to-id from-id from∘to-id

-- Example ---------------------------------------------------------------------

data _⊢_ : List VarMode → TermMode → Set where
  `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
  `λ_ : ∀ {µ} → (𝕧 ∷ µ) ⊢ 𝕥 → µ ⊢ 𝕥
  _·_ : ∀ {µ} → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕥

unquoteDecl STLC to from from∘to = deriveIso (quote _⊢_) STLC to from from∘to

-- unquoteDecl cong₃ = runFreshT (cong-n 3 cong₃)

-- xx = {!from∘to!}

STLC' : Desc
STLC' = `σ (Fin 2) λ where
  zero       → `X (𝕧 ∷ []m) 𝕥 (`■ 𝕥)
  (suc zero) → `X []m 𝕥 (`X []m 𝕥 (`■ 𝕥))
  (suc (suc ()))

-- to' : ∀ {µ M} → (µ ⊢ M) → Tm STLC µ M
-- to' (` x)     = `var x
-- to' (`λ e)    = `con (zero , to' e , refl)
-- to' (e₁ · e₂) = `con (suc zero , to' e₁ , to' e₂ , refl)

-- from∘to' : ∀ {µ M} → (a : µ ⊢ M) → from (to a) ≡ a
-- from∘to' (` x)     = refl
-- from∘to' (`λ e)    = cong `λ_ (from∘to' e)
-- from∘to' (e₁ · e₂) = cong₂ _·_ (from∘to' e₁) (from∘to' e₂)


-- from' : ∀ {µ M} → Tm STLC µ M → (µ ⊢ M)
-- from' (`var x)                           = ` x
-- from' (`con (zero , e , refl))           = `λ (from' e)
-- from' (`con (suc zero , e₁ , e₂ , refl)) = from' e₁ · from' e₂

-- STLC-correct : STLC ≡ STLC'
-- STLC-correct = refl

-- to-correct : ∀ {µ M} (t : µ ⊢ M) → to t ≡ to' t
-- to-correct (` x) = refl
-- to-correct (`λ t) rewrite to-correct t = refl
-- to-correct (t₁ · t₂) rewrite to-correct t₁ |  to-correct t₂ = refl

-- from-correct : ∀ {µ M} (t : Tm STLC µ M) → from t ≡ from' t
-- from-correct (`var x) = refl
-- from-correct (`con (zero , t , refl)) rewrite from-correct t = refl
-- from-correct (`con (suc zero , t₁ , t₂ , refl)) rewrite from-correct t₁ | from-correct t₂ = refl
