module Kitty.Term.Prelude where

open import Data.List using (List; _∷_; _++_)
open import Data.List.Membership.Propositional public using (_∈_)

open import Data.List using (List; []) public

-- List Membership -------------------------------------------------------------

infix  4  _∋_

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set _
xs ∋ x = x ∈ xs

infixl 5 _▷_ _▷▷_

pattern _▷_ xs x = x ∷ xs

_▷▷_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

