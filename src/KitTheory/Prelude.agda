module KitTheory.Prelude where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

infix  4  _∋_

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set _
xs ∋ x = x ∈ xs

infixr 5 _,_

pattern _,_ xs x = x ∷ xs
