module Kitty.Examples.STLC-Derive.SubjectReduction where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.STLC-Derive.Definitions

open import Kitty.Typing.ITerms compose-traversal ctx-repr

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = τ-`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }

open import Kitty.Typing.IKit compose-traversal ctx-repr iterms

open IKit ⦃ … ⦄

_⊢⋯_ :
  ∀ {M'} {_∋/⊢_ : Scoped M'} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
    ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
τ-` ∋x           ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
τ-λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
τ-· ⊢e₁ ⊢e₂      ⊢⋯ ⊢ϕ = τ-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)

itraversal : ITraversal
itraversal = record { _⊢⋯_ = _⊢⋯_ }

open ITraversal itraversal public hiding (_⊢⋯_)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂)  β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (τ-λ ⊢e)                      (ξ-λ e↪e')    = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
