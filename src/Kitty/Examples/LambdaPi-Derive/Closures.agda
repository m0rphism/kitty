module Kitty.Examples.LambdaPi-Derive.Closures where

open import Level using (_⊔_)

module SymmetricClosure {ℓ₁ ℓ₂} {A : Set ℓ₁} (R : A → A → Set ℓ₂) where
  data Sym : A → A → Set ℓ₂ where
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

module SymmetricClosure₂ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
                         (R : ∀ {a} → {b : B a} → C a b → C a b → Set ℓ₄) where
  module _ {a : A} {b : B a} where
    open SymmetricClosure {A = C a b} (R {a} {b}) public hiding (map-Sym; fwd; bwd)

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

module ReflexiveTransitiveClosure {ℓ₁ ℓ₂} {A : Set ℓ₁} (R : A → A → Set ℓ₂) where
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
