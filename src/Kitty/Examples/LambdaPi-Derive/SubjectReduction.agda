module Kitty.Examples.LambdaPi-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)

-- ⊢↪* :
--     t ↪* t' →
--     Γ ⊢ e ∶ t →
--     Γ ⊢ e ∶ t'
-- ⊢↪* refl ⊢e = ⊢e
-- ⊢↪* (step t↪t' t'↪*t'') ⊢e = ⊢↪* t'↪*t'' (⊢↪ t↪t' ⊢e)

↪-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ ϕ ↪ t' ⋯ ϕ
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(λx _)}       {.(λx _)}       (ξ-λ t↪t')  = ξ-λ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(∀[x∶ _ ] _)} {.(∀[x∶ _ ] _)} (ξ-∀₁ t↪t') = ξ-∀₁ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(∀[x∶ _ ] _)} {.(∀[x∶ _ ] _)} (ξ-∀₂ t↪t') = ξ-∀₂ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(_ · _)}      {.(_ · _)}      (ξ-·₁ t↪t') = ξ-·₁ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(_ · _)}      {.(_ · _)}      (ξ-·₂ t↪t') = ξ-·₂ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ}
    {.((λx e₁) · e₂)}
    {.(e₁ ⋯ ⦅ e₂ ⦆ₛ)}
    (β-λ {e₁ = e₁} {e₂ = e₂}) =
  subst (((λx e₁) · e₂) ⋯ ϕ ↪_)
        (sym (dist-⦅⦆ₛ-⋯ e₁ e₂ ϕ))
        (β-λ {e₁ = e₁ ⋯ (ϕ ↑ 𝕖)} {e₂ = e₂ ⋯ ϕ})

_⊢⋯_ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x      ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ ⊢t₁ ⊢e  ⊢⋯ ⊢ϕ = ⊢λ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢∀ ⊢t₁ ⊢t₂ ⊢⋯ ⊢ϕ = ⊢∀ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢t₂ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
_⊢⋯_ {Γ₂ = Γ₂} {e = e₁ · e₂} {ϕ = ϕ} (⊢· {t₁ = t₁} {t₂ = t₂} ⊢e₁ ⊢e₂) ⊢ϕ =
  Γ₂ ⊢ e₁ · e₂ ⋯ ϕ ∶ t₂ ⋯ₛ ⦅ t₁ ⦆ₛ ⋯ ϕ
    by subst (Γ₂ ⊢ (e₁ · e₂) ⋯ ϕ ∶_)
             ((t₂ ⋯ (ϕ ↑ 𝕖)) ⋯ₛ ⦅ t₁ ⋯ ϕ ⦆ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ t₂ t₁ ϕ) ⟩
              t₂ ⋯ₛ ⦅ t₁ ⦆ₛ ⋯ ϕ             ∎)
             (⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ))
⊢★         ⊢⋯ ⊢ϕ = ⊢★
⊢↪ t↪t' ⊢e ⊢⋯ ⊢ϕ = ⊢↪ (↪-⋯ t↪t') (⊢e ⊢⋯ ⊢ϕ)

open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

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
