module ReflectionLib.Categorical.Foldable where

open import Agda.Primitive using (Setω; Level; _⊔_)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.Monoid

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
    A B C M : Set ℓ

record Foldable ℓ (F : Functor' ℓ) : Setω where
  field
    foldr : (A → B → B) → B → F A → B

  foldMap : {{_ : Monoid M}} → (A → M) → F A → M
  foldMap f = foldr (λ a m → f a ⊗ m) 1M

open Foldable {{...}} public
