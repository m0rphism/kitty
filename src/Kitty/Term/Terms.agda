module Kitty.Term.Terms where

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Kitty.Term.Prelude

data SortTy : Set where
  Var NoVar : SortTy

record Terms : Set₁ where
  field
    Sort        : SortTy → Set
    _⊢_         : ∀ {st} → List (Sort Var) → Sort st → Set
    `_          : ∀ {S s} → S ∋ s → S ⊢ s
    `-injective : ∀ {S s} {x₁ x₂ : S ∋ s} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂

  Scoped : SortTy → Set₁
  Scoped st = List (Sort Var) → Sort st → Set

  AllScoped : Set₁
  AllScoped = ∀ {st} → Scoped st

  VarScoped : Set₁
  VarScoped = Scoped Var

  SortCtx : Set
  SortCtx = List (Sort Var)

  module DeBruijn-Notation where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_; _<_; _≤?_; z≤n; s≤s)
    open import Data.List using (length)
    open import Data.List.Relation.Unary.Any using (here; there)
    open import Relation.Nullary.Decidable using (True; toWitness)

    lookup : ∀ {A : Set} → {S : List A} → {n : ℕ} → (p : n < length S) → A
    lookup {_} {(_ ▷ A)} {zero}    (s≤s z≤n)  =  A
    lookup {_} {(S ▷ _)} {(suc n)} (s≤s p)    =  lookup {S = S} p

    count : ∀ {A} {S : List A} → {n : ℕ} → (p : n < length S) → S ∋ lookup {S = S} p
    count {_} {_ ▷ _} {zero}    (s≤s z≤n)  =  here refl
    count {_} {S ▷ _} {(suc n)} (s≤s p)    =  there (count p)

    infix  99 #_

    #_ : ∀ {S : List (Sort Var)}
      → (n : ℕ)
      → {n∈S : True (suc n ≤? length S)}
        --------------------------------
      → S ⊢ lookup {S = S} (toWitness n∈S)
    #_ n {n∈S}  =  ` count (toWitness n∈S)

  open DeBruijn-Notation public using (#_)

mkTerms :
  ∀ (Sort        : SortTy → Set)
    (_⊢_         : ∀ {st} → List (Sort Var) → Sort st → Set)
    (`_          : ∀ {S s} → S ∋ s → S ⊢ s)
    (`-injective : ∀ {S s} {x₁ x₂ : S ∋ s} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂)
  → Terms
mkTerms Sort _⊢_ `_ `-injective = record
  { Sort        = Sort
  ; _⊢_         = _⊢_
  ; `_          = `_
  ; `-injective = `-injective
  }

