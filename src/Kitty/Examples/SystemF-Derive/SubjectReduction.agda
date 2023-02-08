module Kitty.Examples.SystemF-Derive.SubjectReduction where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.SystemF-Derive.Definitions

open import Kitty.Typing.ITerms terms kit-traversal kit-homotopy kit-assoc kit-assoc-lemmas kit-type

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = τ-` }

open import Kitty.Typing.IKit terms kit-traversal kit-homotopy kit-assoc kit-assoc-lemmas kit-type iterms

open IKit ⦃ … ⦄

open WkDistKit ⦃ … ⦄

_⊢⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦃ WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦄ ⦃ IK : IKit 𝕂 WK ⦄
         {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
       Γ₁ ⊢ e ∶ t →
       Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
       Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
τ-` ∋x                              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
τ-λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
τ-Λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = τ-Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
τ-· ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = τ-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
τ-∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆-⋯ₛ t₁ t₂ _))
                                                  (τ-∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
τ-τ                                 ⊢⋯ ⊢ϕ = τ-τ

ikit-traversal : IKitTraversal
ikit-traversal = record { _⊢⋯_ = _⊢⋯_ }

open IKitTraversal ikit-traversal public hiding (_⊢⋯_)

instance
  _ = ikitᵣ
  _ = ikitₛ

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂)  β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (⊢e₁ ⊢⋯ ⊢⦅ ⊢e₂ ⦆)
subject-reduction (τ-∙ ⊢t₁ ⊢t₂ (τ-Λ ⊢e₁))        β-Λ          = ⊢e₁ ⊢⋯ ⊢⦅ ⊢t₂ ⦆
subject-reduction (τ-λ ⊢e)                      (ξ-λ e↪e')    = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-Λ ⊢e)                      (ξ-Λ e↪e')    = τ-Λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (τ-∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = τ-∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
