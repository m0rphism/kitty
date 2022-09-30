module Kitty.Experimental.Examples.SystemF-Kits.Soundness-Bigstep where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Experimental.Examples.SystemF-Kits.Definitions hiding (Value; Neutral)

infix   3  _⇓_

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : List Modeᵥ → Set where
    `ˣ_   : µ ∋ 𝕖  →  Neutral µ
    _·_ : Neutral µ → Value µ → Neutral µ
    _∙_ : Neutral µ → µ ⊢ 𝕥 → Neutral µ

  data Value : List Modeᵥ → Set where
    λx_     : Value (µ ▷ 𝕖)  →  Value µ
    Λα_     : Value (µ ▷ 𝕥)  →  Value µ
    neutral : Neutral µ → Value µ

variable
  v v₁ v₂ v' : Value µ
  n n₁ n₂ n' : Neutral µ

mutual
  ιᵥ : Value µ → µ ⊢ 𝕖
  ιᵥ (λx v) = λx (ιᵥ v)
  ιᵥ (Λα v) = Λα (ιᵥ v)
  ιᵥ (neutral x) = ιₙ x

  ιₙ : Neutral µ → µ ⊢ 𝕖
  ιₙ (`ˣ x) = `ˣ x
  ιₙ (n · v) = ιₙ n · ιᵥ v
  ιₙ (n ∙ t) = ιₙ n ∙ t

data _⇓_ : µ ⊢ 𝕖 → Value µ → Set where
  ⇓-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    e ⇓ v →
    λx e ⇓ λx v
  ⇓-Λ : ∀ {e₂ : µ ⊢ 𝕖} →
    e ⇓ v →
    Λα e ⇓ Λα v
  ⇓-· : ∀ {e₂ : µ ⊢ 𝕖} →
    e₁ ⇓ λx v₁ →
    e₂ ⇓ v₂ →
    ιᵥ v₁ ⋯ ⦅ ιᵥ v₂ ⦆ ⇓ v →
    e₁ · e₂ ⇓ v
  ⇓-∙ : ∀ {e₁ : µ ⊢ 𝕖} →
    e₁ ⇓ Λα v₁ →
    ιᵥ v₁ ⋯ ⦅ t₂ ⦆ ⇓ v →
    e₁ ∙ t₂ ⇓ v


-- Soundness -------------------------------------------------------------------

open import Kitty.Experimental.Examples.SystemF-Kits.SubjectReduction

soundness :
  Γ ⊢ e ∶ t →
  e ⇓ v →
  Γ ⊢ ιᵥ v ∶ t
soundness (τ-λ ⊢e) (⇓-λ e⇓v) = τ-λ (soundness ⊢e e⇓v)
soundness (τ-Λ ⊢e) (⇓-Λ e⇓v) = τ-Λ (soundness ⊢e e⇓v)
soundness (τ-· {t₂ = t₂} ⊢e₁ ⊢e₂) (⇓-· e₁⇓v₁ e₂⇓v₂ e⇓v) with soundness ⊢e₁ e₁⇓v₁
... | τ-λ ⊢e = soundness (subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (sub₁-pres-⊢ ⊢e (soundness ⊢e₂ e₂⇓v₂))) e⇓v
soundness (τ-∙ ⊢e₁) (⇓-∙ e₁⇓v₁ e⇓v) with soundness ⊢e₁ e₁⇓v₁
... | τ-Λ ⊢e = soundness (sub₁-pres-⊢ ⊢e τ-𝕥) e⇓v
