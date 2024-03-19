module ReflectionLib.Categorical.MonadTrans where

open import Agda.Primitive using (Setω; Level; _⊔_)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Monad

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

record MonadTrans ℓ₁ ℓ₂ (T : Functor' ℓ₁ → Functor' ℓ₂) : Setω where
  field
    {{monadtrans-is-monads}} : {F : Functor' ℓ₁} {{_ : Monad ℓ₁ F}} → Monad ℓ₂ (T F)
    lift                     : {F : Functor' ℓ₁} {{_ : Monad ℓ₁ F}} → F A → T F A

open MonadTrans {{...}} public

