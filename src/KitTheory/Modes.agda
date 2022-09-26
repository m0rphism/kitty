module KitTheory.Modes where

open import Data.List using (List)
open import KitTheory.Prelude

record Modes : Set₁ where
  field
    VarMode  : Set
    TermMode : Set
    m→M      : VarMode → TermMode

record Terms (𝕄 : Modes) : Set₁ where
  open Modes 𝕄
  field
    _⊢_ : List VarMode → TermMode → Set
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m

  module DeBruijn-Notation where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_; _<_; _≤?_; z≤n; s≤s)
    open import Data.List using (length)
    open import Data.List.Relation.Unary.Any using (here; there)
    open import Relation.Nullary.Decidable using (True; toWitness)

    lookup : ∀ {A : Set} → {µ : List A} → {n : ℕ} → (p : n < length µ) → A
    lookup {_} {(_ ▷ A)} {zero}    (s≤s z≤n)  =  A
    lookup {_} {(µ ▷ _)} {(suc n)} (s≤s p)    =  lookup {µ = µ} p

    count : ∀ {A} {µ : List A} → {n : ℕ} → (p : n < length µ) → µ ∋ lookup {µ = µ} p
    count {_} {_ ▷ _} {zero}    (s≤s z≤n)  =  here refl
    count {_} {µ ▷ _} {(suc n)} (s≤s p)    =  there (count p)

    infix  9 #_

    #_ : ∀ {µ : List VarMode}
      → (n : ℕ)
      → {n∈µ : True (suc n ≤? length µ)}
        --------------------------------
      → µ ⊢ m→M (lookup {µ = µ} (toWitness n∈µ))
    #_ n {n∈µ}  =  ` count (toWitness n∈µ)

  open DeBruijn-Notation public using (#_)

