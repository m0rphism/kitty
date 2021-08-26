module Examples.ISession.Typing where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)

open import Examples.ISession.Definitions
open import Examples.ISession.Substitution

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  τ-Type :
    Γ ⊢ Type ∶ Kind
  τ-Session :
    Γ ⊢ Session ∶ Kind
  τ-State :
    Γ ⊢ State ∶ Kind
  τ-Shape :
    Γ ⊢ Shape ∶ Kind
  τ-Dom :
    Γ ⊢ t ∶ Shape →
    Γ ⊢ Dom t ∶ Kind
  τ-` : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕧 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
--   τ-λ : ∀ {Γ : Ctx µ} →
--     Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
--     Γ ⊢ λx e ∶ t₁ ⇒ t₂
--   τ-Λ :
--     Γ ,, ★ ⊢ e ∶ t₂ →
--     Γ ⊢ Λα e ∶ ∀α t₂
--   τ-· :
--     Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--     Γ ⊢ e₂ ∶ t₁ →
--     Γ ⊢ e₁ · e₂ ∶ t₂
--   τ-∙ : ∀ {Γ : Ctx µ} →
--     Γ ⊢ e ∶ ∀α t₂ →
--     Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
--   τ-𝕥 :
--     Γ ⊢ t ∶ ★
--   τ-𝕜 :
--     Γ ⊢ ★ ∶ ★

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
