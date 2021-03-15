module KitTheory.Modes where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

infix  4  _∋_

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set _
xs ∋ x = x ∈ xs

record Modes : Set₁ where
  field
    VarMode  : Set
    TermMode : Set
    m→M      : VarMode → TermMode

  Stuff : Set → Set₁
  Stuff StuffMode = List VarMode → StuffMode → Set

record Terms (𝕄 : Modes) : Set₁ where
  open Modes 𝕄 public
  field
    _⊢_ : List VarMode → TermMode → Set
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
