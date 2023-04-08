module Kitty.Util.List where

open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; module ≡-Reasoning)
open ≡-Reasoning

depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

-- We need to drop one extra using `suc`, because otherwise the types in a
-- context are allowed to use themselves.
drop-∈ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
drop-∈ = drop ∘ suc ∘ depth

drop-∈-▷▷ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs₁ xs₂ : List A} →
  (∋x : xs₂ ∋ x) →
  drop-∈ ∋x (xs₁ ▷▷ xs₂) ≡ xs₁ ▷▷ drop-∈ ∋x xs₂
drop-∈-▷▷ {xs₂ = xs₂ ▷ x} (here px)  = refl
drop-∈-▷▷ {xs₂ = xs₂ ▷ x} (there ∋x) = drop-∈-▷▷ ∋x
