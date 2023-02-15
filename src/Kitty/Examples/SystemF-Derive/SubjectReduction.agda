module Kitty.Examples.SystemF-Derive.SubjectReduction where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.SystemF-Derive.Definitions

open import Kitty.Typing.ITerms terms kit-traversal kit-homotopy kit-assoc kit-assoc-lemmas kit-type

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open import Kitty.Typing.IKit terms kit-traversal kit-homotopy kit-assoc kit-assoc-lemmas kit-type iterms

open IKit ⦃ … ⦄

open WkDistKit ⦃ … ⦄

_⊢⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦃ WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦄ ⦃ IK : IKit 𝕂 WK ⦄
         {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
       Γ₁ ⊢ e ∶ t →
       Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
       Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x                              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ {t₂ = t₂} ⊢e                    ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂                         ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ = subst (_ ⊢ _ ∶_) (sym {!dist-⦅⦆-⋯ₛ t₁ t₂ _!})
                                                 (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢τ                                 ⊢⋯ ⊢ϕ = ⊢τ

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
subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (⊢e₁ ⊢⋯ ⊢⦅ ⊢e₂ ⦆)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁))         β-Λ          = ⊢e₁ ⊢⋯ ⊢⦅ ⊢t₂ ⦆
subject-reduction (⊢λ ⊢e)                      (ξ-λ e↪e')    = ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e)                      (ξ-Λ e↪e')    = ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
