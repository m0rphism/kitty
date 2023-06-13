open import Kitty.Term.Terms

module Kitty.Term.Kit (𝕋 : Terms) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude

open Terms 𝕋

private variable
  st : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : List (Sort Var)

-- Required for proving that `Kᵣ ≢ Kₛ`
data KitTag : Set where
  instance K-Ren K-Sub : KitTag

record Kit (_∋/⊢_ : VarScoped) : Set₁ where
  field
    id/`             : ∀ {s} → S ∋ s → S ∋/⊢ s
    `/id             : ∀ {s} → S ∋/⊢ s → S ⊢ s
    id/`/id          : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x

    id/`-injective  : ∀ {S s} {x₁ x₂ : S ∋ s} → id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
    `/id-injective  : ∀ {S s} {x/t₁ x/t₂ : S ∋/⊢ s} → `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂

    wk               : ∀ s' {s} → S ∋/⊢ s → (S ▷ s') ∋/⊢ s
    wk-id/`          : ∀ s' (x : S ∋ s) → wk s' (id/` x) ≡ id/` (there x)
    kit-tag          : KitTag

  -- Weakening

  wk* : ∀ {s} S' → S ∋/⊢ s → (S ▷▷ S') ∋/⊢ s
  wk* []       x = x
  wk* (S' ▷ s) x = wk s (wk* S' x)

  -- wk' : S –→ (S ▷ s)
  -- wk' _ x = wk _ (id/` x)

  -- wk'* : S –→ (S ▷▷ S')
  -- wk'* _ x = wk* _ (id/` x)

_∋/⊢[_]_ :
  ∀ {_∋/⊢_ : VarScoped} →
  List (Sort Var) → (K : Kit _∋/⊢_) → Sort Var → Set
_∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s

Kᵣ : Kit _∋_
Kit.id/`             Kᵣ = λ x → x
Kit.`/id             Kᵣ = `_
Kit.id/`/id          Kᵣ = λ x → refl
Kit.wk               Kᵣ = λ _ x → there x
Kit.wk-id/`          Kᵣ = λ _ x → refl
Kit.kit-tag          Kᵣ = K-Ren
Kit.id/`-injective   Kᵣ = λ eq → eq
Kit.`/id-injective   Kᵣ = λ eq → `-injective eq

open Kit ⦃ … ⦄
