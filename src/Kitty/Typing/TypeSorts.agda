open import Kitty.Term.Terms

module Kitty.Typing.TypeSorts (𝕋 : Terms) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax; proj₂)
open import Kitty.Term.Prelude
open import Kitty.Util.List public

open Terms 𝕋

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx
    ℓ ℓ₁ ℓ₂ : Level

record TypeSorts : Set₁ where
  field
    ↑ᵗ : ∀ {st} → Sort st → ∃[ st' ] Sort st'

  infix  3  _∶⊢_

  _∶⊢_ : ∀ {mt} → SortCtx → Sort mt → Set
  S ∶⊢ s = S ⊢ proj₂ (↑ᵗ s)
