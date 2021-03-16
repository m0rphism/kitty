module Examples.LambdaPi-Kits.SubjectReduction where

open import Examples.LambdaPi-Kits.Definitions

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢t₁ t₁⇓t₁' ⊢e₁) ⊢e₂ t₂⋯t₁⇓t₃) β-λ           = {!!}
subject-reduction (τ-λ ⊢t₁ t₁⇓t₁' ⊢e)                     (ξ-λ e↪e')    = τ-λ ⊢t₁ t₁⇓t₁' (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂ t₂⋯t₁⇓t₃
subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂') t₂⋯t₁⇓t₃
subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₁ t₁↪t₁') = τ-Π (subject-reduction ⊢t₁ t₁↪t₁') {!⊢t₂!}
subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₂ t₂↪t₂') = τ-Π ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
