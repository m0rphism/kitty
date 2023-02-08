module Kitty.Util.Star where

open import Data.List using (List; []; _∷_; _++_)
open import Level using (_⊔_)

-- Star-Lists and Folds --------------------------------------------------------

data Star {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) : List B → A → A → Set (ℓ₁ ⊔ ℓ₂) where
  [] : ∀ {x} → Star R [] x x
  _∷_ : ∀ {x y z b bs} → R b x y → Star R bs y z → Star R (b ∷ bs) x z

infixr 5 _∷[_]_
pattern _∷[_]_  f b fs = _∷_ {b = b} f fs

fold-star : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b x y → T y) →
  T a → Star R bs a b → T b
fold-star f ta [] = ta
fold-star f ta (rab ∷ rbc) = fold-star f (f _ _ _ ta rab) rbc

fold-star' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b y x → T y) →
  T a → Star R bs b a → T b
fold-star' f ta [] = ta
fold-star' f ta (rab ∷ rbc) = f _ _ _ (fold-star' f ta rbc) rab
