-- Causes ReflectionLib.print* to print into the "*Agda Debug*" buffer.
{-# OPTIONS -vreflection-debug:10 #-}

module ReflectionLib.Examples where

open import ReflectionLib.Standard.Syntax renaming (⟦_⟧ to ⟦_⟧')
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.Substitution
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Pretty
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Named.Actions

open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length; drop; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Primitive using (Level)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Function using (_∘_; _$_)

arg-val : ∀ {ℓ} {A : Set ℓ} → Arg A → A
arg-val (arg _ v) = v

arg-inf : ∀ {ℓ} {A : Set ℓ} → Arg A → ArgInfo
arg-inf (arg i _) = i

defdecFun : Arg Name → Type → List Clause → TC ⊤
defdecFun a t cs = do
  declareDef a t
  defineFun (arg-val a) cs

defdecFun' : Arg Name → Type → List Clause → TC ⊤
defdecFun' a t cs = do
  e ← quoteTC (a , t , cs)
  declareDef (argᵥ (arg-val a)) (quoteTerm (Arg Name × Type × List Clause))
  let c = clause [] [] e
  defineFun (arg-val a) (c ∷ [])

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ

mapM : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → (A → TC B) → List A → TC (List B)
mapM f [] = return []
mapM f (x ∷ xs) = do
  y ← f x 
  ys ← mapM f xs
  return (y ∷ ys)

forM : List A → (A → TC B) → TC (List B)
forM xs f = mapM f xs

normaliseTC : A → TC A
normaliseTC x = do
  x ← quoteTC x
  x ← normalise x
  x ← unquoteTC x
  return x

quoteNormTC : A → TC Term
quoteNormTC x = withNormalisation true (quoteTC x)

_by_ : (A : Set ℓ) → A → A
A by a = a



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



-- FIXME: In Desc we don't quantify over µ, however in Term we do.
-- This quantification needs to be detected and removed, or translation to named.
-- Otherwise dependency of constructor pi's needs to be captured as
-- dependency of desc sigmas.

-- mutual

--   {-# TERMINATING #-}
--   extract-µ' : Arg Term → TC (Arg Term)
--   extract-µ' a = do
--     a ← extract-µ (arg-val a)
--     return (argᵥ a)

--   extract-µ : Term → TC Term
--   extract-µ (var x args) = quoteTC {A = List VarMode} []
--   extract-µ (con c args) = do args' ← mapM extract-µ' args; return (con c args')
--   extract-µ (def f args) = do args' ← mapM extract-µ' args; return (def f args')
--   extract-µ unknown = return unknown
--   extract-µ _ = failStr "Unexpected µ"

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

enumerate : List A → List (ℕ × A) 
enumerate xs = f 0 xs where
  f : ℕ → List A → List (ℕ × A) 
  f n []       = []
  f n (x ∷ xs) = (n , x) ∷ f (suc n) xs

fin-pat : ℕ → Pattern
fin-pat zero = con (quote Fin.zero) []
fin-pat (suc x) = con (quote Fin.suc) (argᵥ (fin-pat x) ∷ [])

fin-con : ℕ → Term
fin-con zero = con (quote Fin.zero) []
fin-con (suc x) = con (quote Fin.suc) (argᵥ (fin-con x) ∷ [])

[]m : List VarMode
[]m = []

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

fold-ℕ : A → (ℕ → A → A) → ℕ → A
fold-ℕ a f zero    = a
fold-ℕ a f (suc n) = f n (fold-ℕ a f n)

fold-List : A → (B → List B → A → A) → (List B) → A
fold-List a f []       = a
fold-List a f (b ∷ bs) = f b bs (fold-List a f bs)

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

cong-n : ℕ → TC Name
cong-n n = do
  nm ← freshName "cong-n"
  let cong-ty = {!!}
  let cong-ty = fold-ℕ cong-ty
                       (λ n t → pi (argₕ (var (2 * n + 1) [])) (abs "x₁" (
                                pi (argₕ (var (2 * n + 2) [])) (abs "x₂" t))))
                       (2 * n)
  let cong-ty = pi (argᵥ (fold-ℕ (var 0 []) (λ n t → var (2 * suc n) []) n)) (abs "f" cong-ty)
  let cong-ty = fold-ℕ cong-ty
                       (λ n t → pi (argₕ (quoteTerm Level)) (abs "ℓ" (
                                pi (argₕ (agda-sort (set (var 0 [])))) (abs "A" t))))
                       (suc n)
  let cong-clause = {!!}
  defdecFun
    (argᵥ nm)
    cong-ty
    cong-clause
  return nm

-- Deriving from∘to ------------------------------------------------------------

pi-unchain : Type → Telescope × Type
pi-unchain (pi a (abs x b)) = let tel , t = pi-unchain b in
                              (x , a) ∷ tel , t
pi-unchain t                = [] , t

pi-tel : Type → Telescope
pi-tel t = proj₁ (pi-unchain t)

pi-arity : Type → ℕ
pi-arity t = length (pi-tel t)

lam-n : ℕ → Term → Term
lam-n zero    t = t
lam-n (suc n) t = lam visible (abs "x" (lam-n n t))

data VarType : Set where
  rec other : VarType

buildCongLam : List VarType → ℕ → Name → List (Arg Term) → Term
buildCongLam []           n t args = def t args
buildCongLam (rec   ∷ xs) n t args = lam visible (abs "x"
                                       (buildCongLam xs (suc n) t (wk args ++ (argᵥ (var 0 []) ∷ []))))
buildCongLam (other ∷ xs) n t args = buildCongLam xs (suc n) t (args ++ (argᵥ (var n []) ∷ []))

deriveFromToBody : Name → Name → List ℕ → TC Term
deriveFromToBody from∘to-id con-id rec-vars = do
  con-cong ← cong-n (length rec-vars)
  con-ty ← getType con-id
  let con-arity = pi-arity con-ty
  let rec-var-calls = map (λ x → argᵥ (def from∘to-id (argᵥ (var x []) ∷ []))) rec-vars
  let rec-■ = lam-n (length rec-vars) (def con-id [])
  return $ def con-cong (argᵥ rec-■ ∷ rec-var-calls)

deriveFromTo : (ty-id desc-id to-id from-id from∘to-id : Name) → TC ⊤
deriveFromTo ty-id desc-id to-id from-id from∘to-id = do
  ty ← getDefinition ty-id
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
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
  -- term-clauses ← forM (enumerate term-cs) λ (i , c) → do
  --   c' ← deriveFromClause ty-id desc-id from-id c i
  --   -- printAST c
  --   -- printAST c'
  --   return c'
  let term-clauses = []
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

-- xx = {!to!}

STLC' : Desc
STLC' = `σ (Fin 2) λ where
  zero       → `X (𝕧 ∷ []m) 𝕥 (`■ 𝕥)
  (suc zero) → `X []m 𝕥 (`X []m 𝕥 (`■ 𝕥))
  (suc (suc ()))

to' : ∀ {µ M} → (µ ⊢ M) → Tm STLC µ M
to' (` x)     = `var x
to' (`λ e)    = `con (zero , to' e , refl)
to' (e₁ · e₂) = `con (suc zero , to' e₁ , to' e₂ , refl)

from∘to' : ∀ {µ M} → (a : µ ⊢ M) → from (to a) ≡ a
from∘to' (` x)     = refl
from∘to' (`λ e)    = cong `λ_ (from∘to' e)
from∘to' (e₁ · e₂) = cong₂ _·_ (from∘to' e₁) (from∘to' e₂)


from' : ∀ {µ M} → Tm STLC µ M → (µ ⊢ M)
from' (`var x)                           = ` x
from' (`con (zero , e , refl))           = `λ (from' e)
from' (`con (suc zero , e₁ , e₂ , refl)) = from' e₁ · from' e₂

-- STLC-correct : STLC ≡ STLC'
-- STLC-correct = refl

to-correct : ∀ {µ M} (t : µ ⊢ M) → to t ≡ to' t
to-correct (` x) = refl
to-correct (`λ t) rewrite to-correct t = refl
to-correct (t₁ · t₂) rewrite to-correct t₁ |  to-correct t₂ = refl

from-correct : ∀ {µ M} (t : Tm STLC µ M) → from t ≡ from' t
from-correct (`var x) = refl
from-correct (`con (zero , t , refl)) rewrite from-correct t = refl
from-correct (`con (suc zero , t₁ , t₂ , refl)) rewrite from-correct t₁ | from-correct t₂ = refl
