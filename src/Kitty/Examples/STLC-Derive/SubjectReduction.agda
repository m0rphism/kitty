module Kitty.Examples.STLC-Derive.SubjectReduction where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.STLC-Derive.Definitions

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
τ-` ∋x           ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
τ-λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
τ-· ⊢e₁ ⊢e₂      ⊢⋯ ⊢ϕ = τ-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)

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
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂)  β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (τ-λ ⊢e)                      (ξ-λ e↪e')    = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
