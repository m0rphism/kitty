module ReflectionLib.Categorical.Traversable where

open import Agda.Primitive using (Setω; Level; _⊔_)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.Monoid
open import ReflectionLib.Categorical.Foldable

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
    A B C M : Set ℓ

record Traversable ℓ (T : Functor' ℓ) : Setω where
  field
    {{traversable-is-foldable}} : Foldable ℓ T
    traverse : {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
             → (A → F B) → T A → F (T B)

  sequence : {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
           → T (F A) → F (T A)
  sequence = traverse (λ a → a)

  foldrM : {F : Functor' ℓ'} {{_ : Monad ℓ' F}}
         → (A → B → F B) → F B → T A → F B
  foldrM {{M}} f b0 ta = foldr (λ a fb → _>>=_ {{M}} fb (f a)) b0 ta

  mapA : ∀ {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
        → (A → F B) → T A → F (T B)
  mapA = traverse

  mapM : ∀ {F : Functor' ℓ'} {{_ : Monad ℓ' F}}
        → (A → F B) → T A → F (T B)
  mapM = traverse

  forA : ∀ {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
      → T A → (A → F B) → F (T B)
  forA xs f = mapA f xs

  forM : ∀ {F : Functor' ℓ'} {{_ : Monad ℓ' F}}
      → T A → (A → F B) → F (T B)
  forM xs f = mapM f xs

open Traversable {{...}} public
