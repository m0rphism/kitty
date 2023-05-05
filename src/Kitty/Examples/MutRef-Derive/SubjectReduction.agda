module Kitty.Examples.MutRef-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Kitty.Examples.MutRef-Derive.Definitions
open import Kitty.Typing.IKit compose-traversal ctx-repr iterms
open import Data.List.Properties using (++-identityʳ)
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
⊢` ∋x                              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢· ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢new ⊢e                            ⊢⋯ ⊢ϕ = ⊢new (⊢e ⊢⋯ ⊢ϕ)
⊢get ⊢e                            ⊢⋯ ⊢ϕ = ⊢get (⊢e ⊢⋯ ⊢ϕ)
⊢≔ ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢≔ (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)

open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

subject-reduction : ∀ {Σ : Ctx µ} {σ : µ →ₛ µ} {σ' : µ' →ₛ µ'} →
  Σ ⊢⟨ σ , e ⟩∶ t →
  ⟨ σ , e ⟩↪⟨ σ' , e' ⟩ →
  Σ[ Σ' ∈ Ctx µ' ] Σ' ⊢⟨ σ' , e' ⟩∶ t
subject-reduction {Σ = Σ} (⊢⟨⟩ ⊢σ (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)) β-λ = Σ , ⊢⟨⟩ ⊢σ (subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆))
subject-reduction {Σ = Σ} (⊢⟨⟩ {t = t} ⊢σ ⊢e) β-new = Σ ▶ wk*' _ t ,
                                                      ⊢⟨⟩ {!⊢σ ∋↑/⊢↑ ?!} (⊢` {!refl!})
subject-reduction {Σ = Σ} (⊢⟨⟩ ⊢σ (⊢get (⊢` {x = x} ⊢x))) β-* = Σ , ⊢⟨⟩ ⊢σ {!⊢σ x _ !}
subject-reduction {Σ = Σ} (⊢⟨⟩ ⊢σ ⊢e) β-≔ = {!!}
subject-reduction {Σ = Σ} (⊢⟨⟩ ⊢σ ⊢e) (ξ-·₁ e↪e') = {!!}
subject-reduction {Σ = Σ} (⊢⟨⟩ ⊢σ ⊢e) (ξ-·₂ e↪e') = {!!}

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
