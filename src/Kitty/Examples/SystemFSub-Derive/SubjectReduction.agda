module Kitty.Examples.SystemFSub-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.SystemFSub-Derive.Definitions
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open TypingKit ⦃ … ⦄

-- Substitution of type vars needs to respect constraints:
--   (` α ∶⊑ t) ∈ Γ₁  →  Γ₂ ⊢ ϕ _ α ⊑ t 
_⊑ₐ⋯_ :
  ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ IK : TypingKit K W C₁ C₂ ⦄
    ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ t₁ ⊑ₐ t₂ →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (t₁ ⋯ ϕ) ⊑ₐ (t₂ ⋯ ϕ)
⊑ₐ-` {x = x} t₁⊑t₂ y t₂⊑t₃ ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-` (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ) {!⊢ϕ _ _ y!} (t₂⊑t₃ ⊑ₐ⋯ ⊢ϕ)
⊑ₐ-𝟙                       ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-𝟙
⊑ₐ-⇒ t₁⊑t₂ t₁⊑t₃           ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-⇒ (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ) (t₁⊑t₃ ⊑ₐ⋯ ⊢ϕ)
⊑ₐ-∀ t₁⊑t₂                 ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-∀ (t₁⊑t₂ ⊑ₐ⋯ (⊢ϕ ∋↑/⊢↑ _))
⊑ₐ-refl-var                ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-refl

_⊑⋯_ :
  ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ IK : TypingKit K W C₁ C₂ ⦄
    ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ t₁ ⊑ t₂ →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (t₁ ⋯ ϕ) ⊑ (t₂ ⋯ ϕ)
t₁⊑t₂ ⊑⋯ ⊢ϕ = ⊑ₐ→⊑ ((⊑→⊑ₐ t₁⊑t₂) ⊑ₐ⋯ ⊢ϕ)

_⊢⋯_ :
  ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ IK : TypingKit K W C₁ C₂ ⦄
    ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ {t₂ = t₂} ⊢e    ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ {t₂ = t₂} ⊢e    ⊢⋯ ⊢ϕ = ⊢Λ (subst (_ ⊢ _ ∶_) {!!} (⊢e ⊢⋯ ((⊢ϕ ∋↑/⊢↑ _) ∋↑/⊢↑ _)))
⊢· ⊢e₁ ⊢e₂         ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e ⊢⋯ ⊢ϕ = {!!}
⊢tt                ⊢⋯ ⊢ϕ = ⊢tt
⊢τ                 ⊢⋯ ⊢ϕ = ⊢τ
⊢⊑ ⊢e t₁⊑t₂        ⊢⋯ ⊢ϕ = ⊢⊑ (⊢e ⊢⋯ ⊢ϕ) (t₁⊑t₂ ⊑⋯ ⊢ϕ)
-- ⊢Λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
-- ⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ t₁ t₂ _))
--                                                  (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

wkn-pres-↪ : {e e' : S ⊢ s'} →
  e ↪ e' →
  e ⋯ᵣ wkn ↪ e' ⋯ᵣ wkn {s = s}
wkn-pres-↪ {s = s} {e = e} {e' = e'} e↪e' with #e ← e ⋯ᵣ wkn {s = s} in eq-e | #e' ← e' ⋯ᵣ wkn {s = s} in eq-e' with e↪e' | eq-e | eq-e'
... | β-λ {e₁ = e₁} {e₂ = e₂} | refl | refl = subst ((λx (e₁ ⋯ wkn {s = s} ↑ _)) · (e₂ ⋯ wkn {s = s}) ↪_)
                                                     (e₁ ⋯ᵣ (wkn ↑ 𝕖) ⋯ₛ ⦅ e₂ ⋯ wkn ⦆'ₛ ≡⟨ {!!} ⟩
                                                      e₁ ⋯ₛ ⦅ e₂ ⦆'ₛ ⋯ᵣ wkn ∎)
                                                     β-λ
... | β-Λ        | eq-e | eq-e' = {!!}
... | ξ-λ e↪e''  | eq-e | eq-e' = {!!}
... | ξ-Λ e↪e''  | eq-e | eq-e' = {!!}
... | ξ-·₁ e↪e'' | eq-e | eq-e' = {!!}
... | ξ-·₂ e↪e'' | eq-e | eq-e' = {!!}
... | ξ-∙₁ e↪e'' | eq-e | eq-e' = {!!}

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢e)              (ξ-λ e↪e')  = ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e)              (ξ-Λ e↪e')  = ⊢Λ (subject-reduction ⊢e (wkn-pres-↪ e↪e'))
subject-reduction (⊢· ⊢e₁ ⊢e₂)         β-λ         = {!!}
subject-reduction (⊢· ⊢e₁ ⊢e₂)         (ξ-·₁ e↪e') = ⊢· (subject-reduction ⊢e₁ e↪e') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)         (ξ-·₂ e↪e') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e↪e')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e) β-Λ         = {!!}
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e) (ξ-∙₁ e↪e') = ⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (subject-reduction ⊢e e↪e')
subject-reduction (⊢⊑ ⊢e t⊑t')         e↪e'        = ⊢⊑ (subject-reduction ⊢e e↪e') t⊑t'

-- subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (⊢Λ ⊢e₁))    β-Λ          = {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ!}
