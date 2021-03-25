module KitTheory.Modes where

open import Data.List using (List)
open import KitTheory.Prelude

record Modes : Set₁ where
  field
    VarMode  : Set
    TermMode : Set
    m→M      : VarMode → TermMode

  Stuff : Set → Set₁
  Stuff StuffMode = List VarMode → StuffMode → Set

record Terms (𝕄 : Modes) : Set₁ where
  open Modes 𝕄
  field
    _⊢_ : List VarMode → TermMode → Set
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
