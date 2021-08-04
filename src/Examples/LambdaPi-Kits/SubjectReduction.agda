module Examples.LambdaPi-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Examples.LambdaPi-Kits.Definitions
open import Examples.LambdaPi-Kits.EvalLemmas
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (_++_; [])
open import Data.Product renaming (_,_ to _,×_)

subst-pres-ty : {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ e₁ ∶ τ₁ →
  Γ₂ ⊢* σ ∶ Γ₁ →
  ⟦ τ₁ ⟧ ⋯ σ ⇓ τ →
  Γ ⊢ e₁ ⋯ σ ∶ τ
subst-pres-ty = {!!}

⊢*id :
  Γ ⊢* idₛ ∶ Γ
⊢*id {Γ = Γ} x =
  wk-telescope Γ x ,×
  (subst (_⇓ wk-telescope Γ x) (sym (⋯-idₛ ⟦ wk-telescope Γ x ⟧)) (⇓-refl-val _)) ,×
  τ-` refl

⊢*-ext : {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {σ : µ₁ →ₛ µ₂} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ σ ∶ τ →
  ⟦ τ' ⟧ ⋯ σ ⇓ τ →
  Γ₂ ⊢* σ ,ₖ (e ⋯ σ) ∶ Γ₁ ,, τ'
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (here refl) =
  τ ,×
  -- {!!} ,×
  -- Goal: ⟦ τ' ⟧ ⋯ wk ⋯ (σ ,ₛ (e ⋯ σ)) ⇓ τ
  subst (λ h → h ⋯ (σ ,ₖ (e ⋯ σ)) ⇓ τ) (⋯-⟦⟧-comm τ' wk)
    (subst (_⇓ τ) (wk-cancels-,ₛ {!⟦ τ' ⟧!} {!!} {!!}) {!!})
    ,×
  -- subst (_⇓ τ) {!wk-cancels-,ₛ !} {!!} ,×
  ⊢e
⊢*-ext ⊢σ ⊢e τ'σ⇓τ (there x) = {!!}

subst-pres-ty₁ : {Γ : Ctx µ} →
  Γ ,, τ₂ ⊢ e₁ ∶ τ₁ →
  Γ ⊢ e₂ ∶ τ₂ →
  ⟦ τ₁ ⟧ ⋯ ⦅ e₂ ⦆ ⇓ τ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ τ
subst-pres-ty₁ {τ₂ = τ₂} {τ₁ = τ₁} {e₂ = e₂} {Γ = Γ} ⊢e₁ ⊢e₂ τ₁e₂⇓τ =
  subst-pres-ty ⊢e₁ (subst (λ h → Γ ⊢* ⦅ h ⦆ ∶ Γ ,, τ₂) (⋯-idₛ e₂) {!⊢*-ext {!!} {!!} {!!}!}) τ₁e₂⇓τ
  -- subst-pres-ty ⊢e₁ (subst (λ h → Γ ⊢* ⦅ h ⦆ ∶ Γ ,, τ₂) (⋯-idₛ e₂) (⊢*-ext ⊢*id (subst (_ ⊢_∶ _) (sym (⋯-idₛ e₂)) ⊢e₂) (subst (_⇓ _) (⋯-idₛ ⟦ _ ⟧) (⇓-refl-val _)))) τ₁e₂⇓τ
subst-pres-ty₁ {e₂ = e₂} ⊢e₁ ⊢e₂ τ₁e₂⇓τ = subst-pres-ty ⊢e₁ {!⊢*-ext ⊢*id (subst (_ ⊢_∶ _) (sym (⋯-idₛ e₂)) ⊢e₂)!} τ₁e₂⇓τ

subject-reduction :
  Γ ⊢ e ∶ τ →
  e ⇓ v →
  Γ ⊢ ⟦ v ⟧ ∶ τ
subject-reduction (τ-λ ⊢t₁ t₁⇓τ₁ ⊢e) (⇓-λ e⇓v) =
  τ-λ ⊢t₁ t₁⇓τ₁ (subject-reduction ⊢e e⇓v )
subject-reduction (τ-Π t₁⇓τ₃ ⊢t₁ ⊢t₂) (⇓-Π t₁⇓τ₁ t₂⇓τ₂)
    with ⇓-deterministic t₁⇓τ₁ t₁⇓τ₃
... | refl =
  τ-Π (⇓-refl-val _) (subject-reduction ⊢t₁ t₁⇓τ₁) (subject-reduction ⊢t₂ t₂⇓τ₂)
subject-reduction ⊢e ⇓-` = ⊢e
subject-reduction (τ-· {τ₂ = τ₂} ⊢e₁ ⊢e₂ τ₂e₂⇓τ) (⇓-·ᵥ e₁⇓λv₁ e₂⇓v₂ v₁v₂⇓v)
    with subject-reduction ⊢e₁ e₁⇓λv₁ | subject-reduction ⊢e₂ e₂⇓v₂
... | τ-λ ⊢t₁ t₁⇓τ₁ ⊢v₁ | ⊢v₂ =
  subject-reduction (subst-pres-ty₁ ⊢v₁ ⊢v₂ (eval-subst-eval₁ ⟦ τ₂ ⟧ τ₂e₂⇓τ e₂⇓v₂)) v₁v₂⇓v
subject-reduction (τ-· {τ₂ = τ₂} ⊢e₁ ⊢e₂ τ₂e₂⇓τ) (⇓-·ₙ e₁⇓n e₂⇓v₂) =
  τ-· (subject-reduction ⊢e₁ e₁⇓n) (subject-reduction ⊢e₂ e₂⇓v₂) (eval-subst-eval₁ ⟦ τ₂ ⟧ τ₂e₂⇓τ e₂⇓v₂)
subject-reduction ⊢e ⇓-★ = ⊢e
