module ReflectionLib.Named.Rewrite where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Named.Syntax
open import Data.List using (List; _∷_ ; []; concat)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Product using (Σ; _×_; _,_)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Function using (id)

data HoleType : Set → Set₁ where
  instance `Name          : HoleType Name
  instance `Var           : HoleType String
  instance `Term          : HoleType Term'
  instance `Pattern       : HoleType Pattern'
  instance `Clause        : HoleType Clause'
  instance `Sort          : HoleType Sort'
  instance `Literal       : HoleType Literal
  instance `Definition    : HoleType Definition'
  instance `ArgInfo       : HoleType ArgInfo
  instance `Modality      : HoleType Modality
  instance `Quantity      : HoleType Quantity
  instance `Relevance     : HoleType Relevance
  instance `Visibility    : HoleType Visibility
  instance `Fixity        : HoleType Fixity
  instance `Precedence    : HoleType Precedence
  instance `Associativity : HoleType Associativity
  instance `Meta          : HoleType Meta
  instance ``Arg          : ∀ {A} ⦃ _ : HoleType A ⦄ → HoleType (Arg A)
  instance ``List         : ∀ {A} ⦃ _ : HoleType A ⦄ → HoleType (List A)
  instance ``Abs          : ∀ {A} ⦃ _ : HoleType A ⦄ → HoleType (Abs A)
  instance ``Product      : ∀ {A B} ⦃ _ : HoleType A ⦄ ⦃ _ : HoleType B ⦄ → HoleType (A × B)

pattern `Arg     t     = ``Arg     ⦃ t ⦄
pattern `List    t     = ``List    ⦃ t ⦄
pattern `Abs     t     = ``Abs     ⦃ t ⦄
pattern `Product t₁ t₂ = ``Product ⦃ t₁ ⦄ ⦃ t₂ ⦄

private variable
  ℓ ℓ' ℓ₁ ℓ₂ : Level
  A B C      : Set ℓ

private
  infixl 0 _on_or_
  _on_or_ : (A → Maybe B) → A → (A → B) → B
  f on a or g = maybe id (g a) (f a)
  {-# INLINE _on_or_ #-} -- this makes the termination checker shut up \o/

-- TODO: monadic rewrite
-- recurses into the AST and matches/replaces
mutual
  rw : (∀ {A} ⦃ t₁ : HoleType A ⦄ → A → Maybe A)
     → (∀ {B} ⦃ t₂ : HoleType B ⦄ → B → B)
  rw f ⦃ `Name ⦄          t = f on t or id
  rw f ⦃ `Var ⦄           t = f on t or id
  rw f ⦃ `Term ⦄          t = f on t or λ where
                                (var x args)      → var (rw f x) (rw f args)
                                (con c args)      → con (rw f c) (rw f args)
                                (def d args)      → def (rw f d) (rw f args)
                                (lam v t)         → lam (rw f v) (rw f t)
                                (pat-lam cs args) → pat-lam (rw f cs) (rw f args)
                                (pi a b)          → pi (rw f a) (rw f b)
                                (agda-sort s)     → agda-sort (rw f s)
                                (lit l)           → lit (rw f l)
                                (meta a b)        → meta (rw f a) (rw f b)
                                unknown           → unknown
  rw f ⦃ `Pattern ⦄       t = f on t or λ where
                                (con c ps) → con (rw f c) (rw f ps)
                                (dot t)    → dot (rw f t)
                                (var x)    → var (rw f x)
                                (lit l)    → lit (rw f l)
                                (proj x)   → proj (rw f x)
                                (absurd x) → absurd (rw f x)
  rw f ⦃ `Clause ⦄        t = f on t or λ where
                                (clause tel ps t)      → clause (rw f tel) (rw f ps) (rw f t)
                                (absurd-clause tel ps) → absurd-clause (rw f tel) (rw f ps)
  rw f ⦃ `Arg T ⦄         t = f on t or λ where
                                (arg i t) → arg (rw f i) (rw f t)
  rw f ⦃ `List T ⦄        t = f on t or rw* f
  rw f ⦃ `Sort ⦄          t = f on t or λ where
                                (set t)     → set (rw f t)
                                (lit n)     → lit n
                                (prop t)    → prop (rw f t)
                                (propLit n) → propLit n
                                (inf n)     → inf n
                                unknown     → unknown
  rw f ⦃ `Literal ⦄       t = f on t or id
  rw f ⦃ `Definition ⦄    t = f on t or λ where
                                (function cs)       → function (rw f cs)
                                (data-type pars cs) → data-type pars (rw f cs)
                                (record-type c fs)  → record-type (rw f c) (rw f fs)
                                (data-cons d)       → data-cons (rw f d)
                                axiom               → axiom
                                prim-fun            → prim-fun
  rw f ⦃ `Abs T ⦄         t = f on t or λ where
                                (abs x t) → abs (rw f x) (rw f t)
  rw f ⦃ `ArgInfo ⦄       t = f on t or λ where
                                (arg-info v m) → arg-info (rw f v) (rw f m)
  rw f ⦃ `Modality ⦄      t = f on t or λ where
                                (modality r q) → modality (rw f r) (rw f q)
  rw f ⦃ `Quantity ⦄      t = f on t or id
  rw f ⦃ `Relevance ⦄     t = f on t or id
  rw f ⦃ `Visibility ⦄    t = f on t or id
  rw f ⦃ `Fixity ⦄        t = f on t or λ where
                                (fixity prec assoc) → fixity (rw f prec) (rw f assoc)
  rw f ⦃ `Precedence ⦄    t = f on t or id
  rw f ⦃ `Associativity ⦄ t = f on t or id
  rw f ⦃ `Meta ⦄          t = f on t or id
  rw f ⦃ `Product T₁ T₂ ⦄ t = f on t or λ where
                                (t₁ , t₂) → rw f t₁ , rw f t₂

  rw* : (∀ {A} ⦃ t₁ : HoleType A ⦄ → A → Maybe (A))
      → (∀ {B} ⦃ t₂ : HoleType B ⦄ → List B → List B)
  rw* f []       = []
  rw* f (t ∷ ts) = rw f t ∷ rw* f ts
