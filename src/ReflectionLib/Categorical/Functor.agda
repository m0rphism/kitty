module ReflectionLib.Categorical.Functor where

open import Agda.Primitive using (Setω; Level; _⊔_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B : Set ℓ

Functor' : Level → Setω
Functor' ℓ' = ∀ {ℓ} → Set ℓ → Set (ℓ ⊔ ℓ')

record Functor ℓ (F : Functor' ℓ) : Setω where
  infixl 5 _<$>_  _<$_

  field
    map : (A → B) → (F A → F B)

  _<$>_ : (A → B) → (F A → F B)
  _<$>_ = map

  _<$_ : B → (F A → F B)
  b <$ fa = map (λ _ → b) fa

open Functor {{...}} public
