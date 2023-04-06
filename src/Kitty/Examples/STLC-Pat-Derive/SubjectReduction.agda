module Kitty.Examples.STLC-Pat-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Kitty.Examples.STLC-Pat-Derive.Definitions
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢-` }
open IKit ⦃ … ⦄

_⊢⋯_ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢-` ∋x                              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢-λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢-· ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢-tt                                ⊢⋯ ⊢ϕ = ⊢-tt
⊢-, ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢-, (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢-inj₁ ⊢e                           ⊢⋯ ⊢ϕ = ⊢-inj₁ (⊢e ⊢⋯ ⊢ϕ)
⊢-inj₂ ⊢e                           ⊢⋯ ⊢ϕ = ⊢-inj₂ (⊢e ⊢⋯ ⊢ϕ)
⊢-match ⊢e₁ ⊢cs exhaustive          ⊢⋯ ⊢ϕ = {!!}
⊢-clause-[]                         ⊢⋯ ⊢ϕ = ⊢-clause-[]
⊢-clause-∷ ⊢p ⊢e ⊢cs                ⊢⋯ ⊢ϕ = ⊢-clause-∷ (⊢p ⊢⋯ ⊢ϕ) {!⊢e ⊢⋯ ?!} (⊢cs ⊢⋯ ⊢ϕ)
⊢-ttᵖ                               ⊢⋯ ⊢ϕ = {!!}
⊢-`ᵖ                                ⊢⋯ ⊢ϕ = {!!}
⊢-,ᵖ ⊢p₁ ⊢p₂                        ⊢⋯ ⊢ϕ = {!!}
⊢-inj₁ᵖ ⊢p                          ⊢⋯ ⊢ϕ = {!!}
⊢-inj₂ᵖ ⊢p                          ⊢⋯ ⊢ϕ = {!!}

-- open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

-- subject-reduction :
--   Γ ⊢ e ∶ t →
--   e ↪ e' →
--   Γ ⊢ e' ∶ t
-- subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆)
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁))         β-Λ          = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆
-- subject-reduction (⊢λ ⊢e)                      (ξ-λ e↪e')    = ⊢λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢Λ ⊢e)                      (ξ-Λ e↪e')    = ⊢Λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
