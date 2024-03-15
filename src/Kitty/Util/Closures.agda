module Kitty.Util.Closures where

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module SymmetricClosure {ℓ₁ ℓ₂} (A : Set ℓ₁) (R : A → A → Set ℓ₂) where
  infix 3 Sym
  data Sym : A → A → Set (ℓ₁ ⊔ ℓ₂) where
    fwd : ∀ {a₁ a₂} → R a₁ a₂ → Sym a₁ a₂  
    bwd : ∀ {a₁ a₂} → R a₂ a₁ → Sym a₁ a₂  

  sym : ∀ {a₁ a₂} → Sym a₁ a₂ → Sym a₂ a₁
  sym (fwd r) = bwd r
  sym (bwd r) = fwd r

  map-Sym :
    ∀ {f : A → A}
      (F : ∀ {a a' : A} → R a a' → R (f a) (f a'))
      {a a' : A}
    → Sym a a'
    → Sym (f a) (f a')
  map-Sym F (fwd r₁₂) = fwd (F r₁₂)
  map-Sym F (bwd r₂₁) = bwd (F r₂₁)

module SymmetricClosure₂
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} (C : (a : A) → B a → Set ℓ₃)
    (R : ∀ {a} → {b : B a} → C a b → C a b → Set ℓ₄) where

  module _ {a : A} {b : B a} where
    open SymmetricClosure (C a b) (R {a} {b}) public hiding (map-Sym; fwd; bwd)

  -- We need to import them directly, otherwise they can't be used as patterns.
  open SymmetricClosure public using (fwd; bwd)

  -- Generalized form of `SymmetricClosure.map-Sym` allowing `F` to change indices.
  map-Sym :
    ∀ {a} {a'} {b : B a} {b' : B a'}
      {f : C a b → C a' b'}
      (F : ∀ {c₁ c₂ : C a b} → R c₁ c₂ → R (f c₁) (f c₂))
      {c₁ c₂ : C a b}
    → Sym c₁ c₂
    → Sym (f c₁) (f c₂)
  map-Sym F (fwd r₁₂) = fwd (F r₁₂)
  map-Sym F (bwd r₂₁) = bwd (F r₂₁)

module ReflexiveTransitiveClosure {ℓ₁ ℓ₂} (A : Set ℓ₁) (R : A → A → Set ℓ₂) where
  infix 3 ReflTrans
  data ReflTrans : A → A → Set (ℓ₁ ⊔ ℓ₂) where
    refl : ∀ {a} → ReflTrans a a
    step : ∀ {a₁ a₂ a₃} → R a₁ a₂ → ReflTrans a₂ a₃ → ReflTrans a₁ a₃

  trans : ∀ {a₁ a₂ a₃} → ReflTrans a₁ a₂ → ReflTrans a₂ a₃ → ReflTrans a₁ a₃
  trans refl           r₁₁ = r₁₁
  trans (step r₁₂ r₂₃) r₃₄ = step r₁₂ (trans r₂₃ r₃₄)

  embed : ∀ {a₁ a₂} → R a₁ a₂ → ReflTrans a₁ a₂
  embed r₁₂ = step r₁₂ refl

  map-ReflTrans :
    ∀ (f : A → A)
      (F : ∀ {a a' : A} → R a a' → R (f a) (f a'))
      {a a' : A}
    → ReflTrans a a'
    → ReflTrans (f a) (f a')
  map-ReflTrans f F refl = refl
  map-ReflTrans f F (step r₁₂ r₂₃) = step (F r₁₂) (map-ReflTrans f F r₂₃)

  module Symmetric (R-sym : ∀ {a₁ a₂} → R a₁ a₂ → R a₂ a₁) where
    sym : ∀ {a₁ a₂} → ReflTrans a₁ a₂ → ReflTrans a₂ a₁
    sym refl = refl
    sym (step r₁₂ r₂₃) = trans (sym r₂₃) (embed (R-sym r₁₂))

  -- module Reasoning where
  infixr  2  _⟨_⟩_  _*⟨_⟩_
  infix   3  _∎

  _∎ : ∀ a → ReflTrans a a
  a ∎ = refl

  _⟨_⟩_ : ∀ (a₁ : A) {a₂ a₃ : A}
    → R a₁ a₂
    → ReflTrans a₂ a₃
    → ReflTrans a₁ a₃
  a₁ ⟨ p ⟩ q = step p q

  _*⟨_⟩_ : ∀ (a₁ : A) {a₂ a₃ : A}
    → ReflTrans a₁ a₂
    → ReflTrans a₂ a₃
    → ReflTrans a₁ a₃
  a₁ *⟨ p ⟩ q = trans p q

  _≡R⟨_⟩_ : ∀ (a₁ : A) {a₂ a₃ : A}
    → a₁ ≡ a₂
    → ReflTrans a₂ a₃
    → ReflTrans a₁ a₃
  a₁ ≡R⟨ refl ⟩ q = q


module ReflexiveTransitiveClosure₂
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} (C : (a : A) → B a → Set ℓ₃)
    (R : ∀ {a} → {b : B a} → C a b → C a b → Set ℓ₄) where

  module _ {a : A} {b : B a} where
    open ReflexiveTransitiveClosure (C a b) (R {a} {b}) public hiding (map-ReflTrans; refl; step)

  -- We need to import them directly, otherwise they can't be used as patterns.
  open ReflexiveTransitiveClosure public using (refl; step)

  -- Generalized form of `ReflexiveTransitiveClosure.map-ReflTrans` allowing `F` to change indices.
  map-ReflTrans :
    ∀ {a} {a'} {b : B a} {b' : B a'}
      {f : C a b → C a' b'}
      (F : ∀ {c₁ c₂ : C a b} → R c₁ c₂ → R (f c₁) (f c₂))
      {c₁ c₂ : C a b}
    → ReflTrans c₁ c₂
    → ReflTrans (f c₁) (f c₂)
  map-ReflTrans F refl = refl
  map-ReflTrans F (step r₁₂ r₂₃) = step (F r₁₂) (map-ReflTrans F r₂₃)

module ReflexiveTransitiveSymmtetricClosure₂
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} (C : (a : A) → B a → Set ℓ₃)
    (R : ∀ {a} → {b : B a} → C a b → C a b → Set ℓ₄) where

  open SymmetricClosure₂ C R public using (fwd; bwd)
  open SymmetricClosure₂ C R using (Sym; map-Sym) renaming (sym to sym')
  open ReflexiveTransitiveClosure₂ C Sym public hiding (map-ReflTrans; module Symmetric) renaming (ReflTrans to ReflTransSym)
  open ReflexiveTransitiveClosure₂ C Sym using (map-ReflTrans; module Symmetric)
  module _ {a : A} {b : B a} where
    open Symmetric {a} {b} sym' public

  map-ReflTransSym :
    ∀ {a} {a'} {b : B a} {b' : B a'}
      {f : C a b → C a' b'}
      (F : ∀ {c₁ c₂ : C a b} → R c₁ c₂ → R (f c₁) (f c₂))
      {c₁ c₂ : C a b}
    → ReflTransSym c₁ c₂
    → ReflTransSym (f c₁) (f c₂)
  map-ReflTransSym F = map-ReflTrans (map-Sym F)

module SymmetricClosure₃
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} (D : (a : A) → (b : B a) → C a b → Set ℓ₄)
    (R : ∀ {a} → {b : B a} → {c : C a b} → D a b c → D a b c → Set ℓ₅) where

  module _ {a : A} {b : B a} {c : C a b} where
    open SymmetricClosure (D a b c) (R {a} {b} {c}) public hiding (map-Sym; fwd; bwd)

  -- We need to import them directly, otherwise they can't be used as patterns.
  open SymmetricClosure public using (fwd; bwd)

  -- Generalized form of `SymmetricClosure.map-Sym` allowing `F` to change indices.
  map-Sym :
    ∀ {a} {a'} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
      {f : D a b c → D a' b' c'}
      (F : ∀ {d₁ d₂ : D a b c} → R d₁ d₂ → R (f d₁) (f d₂))
      {d₁ d₂ : D a b c}
    → Sym d₁ d₂
    → Sym (f d₁) (f d₂)
  map-Sym F (fwd r₁₂) = fwd (F r₁₂)
  map-Sym F (bwd r₂₁) = bwd (F r₂₁)

module ReflexiveTransitiveClosure₃
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} (D : (a : A) → (b : B a) → C a b → Set ℓ₄)
    (R : ∀ {a} → {b : B a} → {c : C a b} → D a b c → D a b c → Set ℓ₅) where

  module _ {a : A} {b : B a} {c : C a b} where
    open ReflexiveTransitiveClosure (D a b c) (R {a} {b} {c}) public hiding (map-ReflTrans; refl; step)

  -- We need to import them directly, otherwise they can't be used as patterns.
  open ReflexiveTransitiveClosure public using (refl; step)

  -- Generalized form of `ReflexiveTransitiveClosure.map-ReflTrans` allowing `F` to change indices.
  map-ReflTrans :
    ∀ {a} {a'} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
      {f : D a b c → D a' b' c'}
      (F : ∀ {d₁ d₂ : D a b c} → R d₁ d₂ → R (f d₁) (f d₂))
      {d₁ d₂ : D a b c}
    → ReflTrans d₁ d₂
    → ReflTrans (f d₁) (f d₂)
  map-ReflTrans F refl = refl
  map-ReflTrans F (step r₁₂ r₂₃) = step (F r₁₂) (map-ReflTrans F r₂₃)

module ReflexiveTransitiveSymmtetricClosure₃
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} (D : (a : A) → (b : B a) → C a b → Set ℓ₄)
    (R : ∀ {a} → {b : B a} → {c : C a b} → D a b c → D a b c → Set ℓ₅) where

  open SymmetricClosure₃ D R public using (fwd; bwd)
  open SymmetricClosure₃ D R using (Sym; map-Sym) renaming (sym to sym')
  open ReflexiveTransitiveClosure₃ D Sym public hiding (map-ReflTrans; module Symmetric) renaming (ReflTrans to ReflTransSym)
  open ReflexiveTransitiveClosure₃ D Sym using (map-ReflTrans; module Symmetric)
  module _ {a : A} {b : B a} {c : C a b} where
    open Symmetric {a} {b} {c} sym' public

  map-ReflTransSym :
    ∀ {a} {a'} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
      {f : D a b c → D a' b' c'}
      (F : ∀ {d₁ d₂ : D a b c} → R d₁ d₂ → R (f d₁) (f d₂))
      {d₁ d₂ : D a b c}
    → ReflTransSym d₁ d₂
    → ReflTransSym (f d₁) (f d₂)
  map-ReflTransSym F = map-ReflTrans (map-Sym F)

-- TODO: Other direction

-- data _↪*'_ : µ ⊢ M → µ ⊢ M → Set where
--   refl :
--     t ↪*' t
--   step :
--     t₁ ↪*'  t₂ →
--     t₂ ↪ t₃ →
--     t₁ ↪*' t₃

-- ↪*'-trans :
--     t₁ ↪*' t₂ →
--     t₂ ↪*' t₃ →
--     t₁ ↪*' t₃
-- ↪*'-trans = {!!}

-- ↪*-to-↪*' :
--     t₁ ↪* t₂ →
--     t₁ ↪*' t₂
-- ↪*-to-↪*' refl = refl
-- ↪*-to-↪*' (step x y) = ↪*'-trans (step refl x) (↪*-to-↪*' y)

-- ↪*'-to-↪* :
--     t₁ ↪*' t₂ →
--     t₁ ↪* t₂
-- ↪*'-to-↪* refl = refl
-- ↪*'-to-↪* (step y x) = ↪*-trans (↪*'-to-↪* y) (step x refl)
