module Kitty.Examples.SystemF-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Kitty.Examples.SystemF-Derive.Definitions
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open TypingKit ⦃ … ⦄

_⊢⋯_ :
  ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
    ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x                              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ t₁ t₂ _))
                                                 (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢τ                                 ⊢⋯ ⊢ϕ = ⊢τ

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁))         β-Λ          = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
subject-reduction (⊢λ ⊢e)                      (ξ-λ e↪e')    = ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e)                      (ξ-Λ e↪e')    = ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
