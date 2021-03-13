open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Everything
    (VarMode  : Set)
    (TermMode : Set)
    (m→M      : VarMode → TermMode)
    (_⊢_      : List VarMode → TermMode → Set)
    (`_       : ∀ {µ m} → m ∈ µ → µ ⊢ m→M m)
  where

open import KitTheory.Kit           VarMode TermMode m→M _⊢_ `_ public
open import KitTheory.Compose       VarMode TermMode m→M _⊢_ `_ public
open import KitTheory.ComposeLemmas VarMode TermMode m→M _⊢_ `_ public
open import KitTheory.Types         VarMode TermMode m→M _⊢_ `_ public
