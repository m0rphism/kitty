open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Everything
    (VarKind  : Set)
    (TermKind : Set)
    (k→K      : VarKind → TermKind)
    (_⊢_      : List VarKind → TermKind → Set)
    (`_       : ∀ {κ k} → k ∈ κ → κ ⊢ k→K k)
  where

open import KitTheory.Kit           VarKind TermKind k→K _⊢_ `_ public
open import KitTheory.Compose       VarKind TermKind k→K _⊢_ `_ public
open import KitTheory.ComposeLemmas VarKind TermKind k→K _⊢_ `_ public
open import KitTheory.Types         VarKind TermKind k→K _⊢_ `_ public
