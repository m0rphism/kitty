module ReflectionLib.Categorical.Monad where

open import Agda.Primitive using (Setω; Level; _⊔_)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

record Monad ℓ (F : Functor' ℓ) : Setω where
  infixl 5  _>>=_  _=<<_  _>>_  _<<_  _>=>_  _<=<_

  field
    {{monad-is-applicative}} : Applicative ℓ F
    _>>=_ : F A → (A → F B) → F B

  return : A → F A
  return = pure

  _=<<_ : (A → F B) → F A → F B
  f =<< fa = fa >>= f

  _>>_ : F A → F B → F B
  _>>_ = _*>_

  _<<_ : F A → F B → F A
  _<<_ = _<*_

  _>=>_ : (A → F B) → (B → F C) → (A → F C)
  (f >=> g) x = f x >>= g

  _<=<_ : (B → F C) → (A → F B) → (A → F C)
  f <=< g = g >=> f

  join : F (F A) → F A
  join ffa = ffa >>= λ x → x

open Monad {{...}} public

