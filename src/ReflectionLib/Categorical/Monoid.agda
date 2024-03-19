module ReflectionLib.Categorical.Monoid where

record Monoid {ℓ} (A : Set ℓ) : Set ℓ where
  infixl 5  _⊗_
  field
    1M  : A
    _⊗_ : A → A → A

open Monoid {{...}} public
