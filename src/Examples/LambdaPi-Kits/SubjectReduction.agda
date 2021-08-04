module Examples.LambdaPi-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Examples.LambdaPi-Kits.Definitions
open import Examples.LambdaPi-Kits.EvalLemmas
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (_++_; [])
open import Data.Product renaming (_,_ to _,×_)

infixr 1 _by_
_by_ : (T : Set) → T → T
T by t = t

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
  Γ₂ ⊢ e ∶ τ →
  ⟦ τ' ⟧ ⋯ σ ⇓ τ →
  Γ₂ ⊢* σ ,ₖ e ∶ Γ₁ ,, τ'
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (here refl) =
  let Γx⋯σ⇓τ =
        ⟦ wk-telescope (Γ₁ ,, τ') (here refl) ⟧ ⋯ (σ ,ₖ e) ⇓ τ
          by
        ⟦ τ' ValueSubst.⋯ wk ⟧ ⋯ (σ ,ₛ e) ⇓ τ
          by subst (λ h → h ⋯ (σ ,ₖ e) ⇓ τ) (⋯-⟦⟧-comm τ' wk) (
        ⟦ τ' ⟧ ⋯ wk ⋯ (σ ,ₛ e) ⇓ τ
          by subst (_⇓ τ) (sym (wk-cancels-,ₛ ⟦ τ' ⟧ σ e)) (
        ⟦ τ' ⟧ ⋯ σ  ⇓ τ
          by τ'σ⇓τ))
  in τ ,× Γx⋯σ⇓τ ,× ⊢e
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (there x) with ⊢σ x
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (there x) | τ₁' ,× ⇓τ₁' ,× ⊢' =
  let Γx⋯σ⇓τ =
        ⟦ wk-telescope (Γ₁ ,, τ') (there x) ⟧ ⋯ (σ ,ₛ e) ⇓ τ₁'
          by
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ValueSubst.⋯ wk ⟧ ⋯ (σ ,ₛ e) ⇓ τ₁'
          by subst (λ h → h ⋯ (σ ,ₖ e) ⇓ τ₁') (⋯-⟦⟧-comm (ValueSubst.wk-drop-∈ x (Γ₁ x)) wk) (
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ wk ⋯ (σ ,ₛ e) ⇓ τ₁'
          by subst (_⇓ τ₁') (sym (wk-cancels-,ₛ ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ σ e)) (
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ σ ⇓ τ₁'
          by
        ⇓τ₁'))
  in τ₁' ,× Γx⋯σ⇓τ ,× ⊢'

subst-pres-ty₁ : {Γ : Ctx µ} →
  Γ ,, τ₂ ⊢ e₁ ∶ τ₁ →
  Γ ⊢ e₂ ∶ τ₂ →
  ⟦ τ₁ ⟧ ⋯ ⦅ e₂ ⦆ ⇓ τ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ τ
subst-pres-ty₁ {τ₂ = τ₂} {τ₁ = τ₁} {e₂ = e₂} {Γ = Γ} ⊢e₁ ⊢e₂ τ₁e₂⇓τ =
  let ⊢* = ⊢*-ext ⊢*id ⊢e₂ (subst (_⇓ τ₂) (sym (⋯-idₛ ⟦ τ₂ ⟧)) (⇓-refl-val τ₂))
  in subst-pres-ty ⊢e₁ ⊢* τ₁e₂⇓τ

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
