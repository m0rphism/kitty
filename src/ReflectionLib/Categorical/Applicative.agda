module ReflectionLib.Categorical.Applicative where

open import Agda.Primitive using (Setω; Level; _⊔_)

open import ReflectionLib.Categorical.Functor

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C S S' : Set ℓ
    F M : ∀ {ℓ} → Set ℓ → Set (ℓ ⊔ ℓ₂)

record Applicative ℓ (F : Functor' ℓ) : Setω where
  infixl 5 _<*>_  _<*_  _*>_

  field
    {{applicative-is-functor}} : Functor ℓ F
    pure : A → F A
    _<*>_ : F (A → B) → (F A → F B)

  _<*_ : F A → F B → F A
  fa <* fb = (λ a _ → a) <$> fa <*> fb

  _*>_ : F A → F B → F B
  fa *> fb = (λ _ b → b) <$> fa <*> fb

open Applicative {{...}} public
