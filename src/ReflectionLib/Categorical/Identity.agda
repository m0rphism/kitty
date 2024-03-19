module ReflectionLib.Categorical.Identity where

open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.Monoid
open import ReflectionLib.Categorical.Foldable
open import ReflectionLib.Categorical.Traversable

private variable
  ℓ ℓ₁ ℓ₂ ℓ' : Level
  A B : Set ℓ

record Identity {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkIdentity
  field
    runIdentity : A

open Identity public

instance
  Identity-Functor : Functor 0ℓ Identity
  Identity-Functor = record { map = λ f x → mkIdentity (f (runIdentity x)) }

  Identity-Applicative : Applicative 0ℓ Identity
  Identity-Applicative = record
    { pure  = mkIdentity
    ; _<*>_ = λ ff fx → mkIdentity (runIdentity ff (runIdentity fx))
    }

  Identity-Monad : Monad 0ℓ Identity
  Identity-Monad = record { _>>=_ = λ x f → mkIdentity (runIdentity (f (runIdentity x))) }

  Identity-Monoid : {{_ : Monoid A}} → Monoid (Identity A)
  Identity-Monoid = record
    { 1M = mkIdentity 1M
    ; _⊗_ = λ ix iy → mkIdentity (runIdentity ix ⊗ runIdentity iy)
    }

  Identity-Foldable : Foldable 0ℓ Identity
  Identity-Foldable = record { foldr = λ f b0 x → f (runIdentity x) b0 }

  Identity-Traversable : Traversable 0ℓ Identity
  Identity-Traversable = record { traverse = λ f x → map mkIdentity (f (runIdentity x)) }
