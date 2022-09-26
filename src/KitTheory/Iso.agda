module KitTheory.Iso where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iso
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ a → from (to a) ≡ a
    to∘from : ∀ b → to (from b) ≡ b
