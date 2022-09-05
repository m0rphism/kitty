module Examples.LambdaPi-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Examples.LambdaPi-Kits.Definitions
open import Examples.LambdaPi-Kits.EvalLemmas
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (_++_; [])
open import Data.Product renaming (_,_ to _,×_)

ren-pres-⊢ : {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ e ∶ τ →
  Γ₂ ⊢ e ⋯ ρ ∶ τ ⋯ᵥ ρ
ren-pres-⊢ ope (τ-` refl)                     = τ-` (ope-pres-telescope _ ope)
ren-pres-⊢ ope (τ-λ ⊢t₁ t₁⇓τ₁ ⊢e)  rewrite ↑≡ = τ-λ (ren-pres-⊢ ope ⊢t₁) (ren-pres-⇓ _ t₁⇓τ₁) (ren-pres-⊢ (ope-keep ope) ⊢e)
ren-pres-⊢ {τ = τ} {ρ = ρ} ope (τ-· {τ₁ = τ₁} {τ₂ = τ₂} {e₂ = e₂} ⊢e₁ ⊢e₂ τ₂e₂⇓τ) =
  let X = ⟦ τ₂ ⋯ᵥ ρ ↑ᵥ 𝕥 ⟧ ⋯ ⦅ e₂ ⋯ ρ ⦆ ⇓ τ ⋯ᵥ ρ
            by subst (λ ■ → ■ ⋯ ⦅ e₂ ⋯ ρ ⦆ ⇓ τ ⋯ᵥ ρ) (⋯-⟦⟧-comm τ₂ (ρ ↑ᵥ 𝕥)) (
          ⟦ τ₂ ⟧ ⋯ ρ ↑ᵥ 𝕥 ⋯ ⦅ e₂ ⋯ ρ ⦆ ⇓ τ ⋯ᵥ ρ
            by subst (λ ■ → ⟦ τ₂ ⟧ ⋯ ■ ρ 𝕥 ⋯ ⦅ e₂ ⋯ ρ ⦆ ⇓ τ ⋯ᵥ ρ) ↑≡ (
          ⟦ τ₂ ⟧ ⋯ ρ ↑ 𝕥 ⋯ₛ ⦅ e₂ ⋯ ρ ⦆ ⇓ τ ⋯ᵥ ρ
            by  subst (λ ■ → ■ ⇓ τ ⋯ᵥ ρ) (dist-⦅⦆ₛ-⋯ᵣ ⟦ τ₂ ⟧ e₂ ρ) (
          ⟦ τ₂ ⟧ ⋯ ⦅ e₂ ⦆ ⋯ ρ ⇓ τ ⋯ᵥ ρ
            by ren-pres-⇓ _ τ₂e₂⇓τ)))
  in τ-· (ren-pres-⊢ ope ⊢e₁) (ren-pres-⊢ ope ⊢e₂) X
ren-pres-⊢ ope (τ-Π t₁⇓τ₁ ⊢t₁ ⊢t₂) rewrite ↑≡ = τ-Π (ren-pres-⇓ _ t₁⇓τ₁) (ren-pres-⊢ ope ⊢t₁) (ren-pres-⊢ (ope-keep ope) ⊢t₂)
ren-pres-⊢ ope τ-★                            = τ-★

wk-pres-⊢ : {Γ : Ctx µ₁} {τ₂ : Value µ₁ 𝕧} →
  Γ ⊢ e ∶ τ₁ →
  _▶_ {m = m} Γ τ₂ ⊢ e ⋯ wk ∶ τ₁ ⋯ᵥ wk
wk-pres-⊢ ⊢e = ren-pres-⊢ (ope-drop ope-id) ⊢e

⊢*-↑ : {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {σ : µ₁ →ₛ µ₂} →
  ⟦ τ₁ ⟧ ⋯ σ ⇓ τ₂ →
  Γ₂      ⊢* σ      ∶ Γ₁       →
  Γ₂ ▶ τ₂ ⊢* σ ↑ₛ m ∶ Γ₁ ▶ τ₁
⊢*-↑ {τ₁ = τ₁} {τ₂ = τ₂} {σ = σ} τ₁σ⇓τ₂ ⊢σ (here refl) =
  let X =
        ⟦ τ₁ ⋯ᵥ wk ⟧ ⋯ σ ↑ₛ 𝕥 ⇓ τ₂ ⋯ᵥ wk
          by subst (λ ■ → ■ ⋯ σ ↑ₛ 𝕥 ⇓ τ₂ ⋯ᵥ wk) (⋯-⟦⟧-comm τ₁ wk) (
        ⟦ τ₁ ⟧ ⋯ wk ⋯ σ ↑ₛ 𝕥 ⇓ τ₂ ⋯ᵥ wk
          by subst (λ ■ → ■ ⇓ τ₂ ⋯ᵥ wk) (sym (dist-↑-sub ⟦ τ₁ ⟧ σ)) (
        ⟦ τ₁ ⟧ ⋯ σ ⋯ wk ⇓ τ₂ ⋯ᵥ wk
          by ren-pres-⇓ wk (
        ⟦ τ₁ ⟧ ⋯ σ ⇓ τ₂
          by τ₁σ⇓τ₂)))
  in τ₂ ⋯ᵥ wk ,× X ,× τ-` refl
⊢*-↑ {τ₁ = τ₁} {τ₂ = τ₂} τ₁σ⇓τ₂ ⊢σ (there x) with ⊢σ x
⊢*-↑ {τ₁ = τ₁} {τ₂ = τ₂} {Γ₁ = Γ₁} {σ = σ} τ₁σ⇓τ₂ ⊢σ (there x) | τ ,× ⇓τ ,× ⊢σx =
  let X = ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⋯ᵥ wk ⟧ ⋯ σ ↑ₛ _ ⇓ τ ⋯ᵥ wk
            by subst (λ ■ → ■ ⋯ σ ↑ₛ _ ⇓ τ ⋯ᵥ wk) (⋯-⟦⟧-comm (ValueSubst.wk-drop-∈ x (Γ₁ x)) wk) (
          ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ wk ⋯ σ ↑ₛ _ ⇓ τ ⋯ᵥ wk
            by subst (λ ■ → ■ ⇓ τ ⋯ᵥ wk) (sym (dist-↑-sub (⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧) σ)) (
          ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ σ ⋯ wk ⇓ τ ⋯ᵥ wk
            by ren-pres-⇓ wk ⇓τ))
  in τ ⋯ᵥ wk ,× X ,× wk-pres-⊢ ⊢σx

-- We need a way to state that Γ only contains well-typed types.
⊢→★ :
  Γ ⊢ e ∶ τ →
  Γ ⊢ ⟦ τ ⟧ ∶ ★
⊢→★ (τ-` refl) = {!!}
⊢→★ (τ-λ ⊢e x ⊢e₁) = {!!}
⊢→★ (τ-· ⊢e ⊢e₁ x) = {!!}
⊢→★ (τ-Π x ⊢e ⊢e₁) = {!!}
⊢→★ τ-★ = {!!}

subst-pres-ty : {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ e₁ ∶ τ₁ →
  Γ₂ ⊢* σ ∶ Γ₁ →
  ⟦ τ₁ ⟧ ⋯ σ ⇓ τ →
  Γ₂ ⊢ e₁ ⋯ σ ∶ τ
subst-pres-ty (τ-` {x = x} refl) ⊢σ τ₁σ⇓τ with ⊢σ x
subst-pres-ty (τ-` {x = _} refl) ⊢σ τ₁σ⇓τ | τ ,× ⇓τ ,× ⊢σx with ⇓-deterministic ⇓τ τ₁σ⇓τ
subst-pres-ty (τ-` {x = _} refl) ⊢σ τ₁σ⇓τ | τ ,× ⇓τ ,× ⊢σx | refl = ⊢σx
subst-pres-ty (τ-λ {t₁ = t₁} ⊢t₁ t₁⇓τ₁ ⊢e) ⊢σ (⇓-Π τ₁σ⇓τ τ₁σ⇓τ₁) =
  τ-λ (subst-pres-ty ⊢t₁ ⊢σ ⇓-★)
      (eval-subst-evalₗ t₁ τ₁σ⇓τ t₁⇓τ₁)
      (subst-pres-ty ⊢e (⊢*-↑ τ₁σ⇓τ ⊢σ) τ₁σ⇓τ₁)
subst-pres-ty (τ-· {τ₁ = τ₁} {τ₂ = τ₂} ⊢e₁ ⊢e₂ τ₃e₂⇓τ₂) ⊢σ τ₁σ⇓τ =
  let ⇓X = eval-subst-evalₗ _ τ₁σ⇓τ τ₃e₂⇓τ₂ in
  {!!}
  -- τ-· {τ₁ = τ₁} {τ₂ = τ₂} ? ? ?
  -- τ-· {τ₁ = τ₁} {τ₂ = τ₂} (subst-pres-ty ⊢e₁ ⊢σ (⇓-Π {!!} {!!}))
  --     (subst-pres-ty ⊢e₂ ⊢σ {!!})
  --     {!⇓X!}
  -- From where do we get  ⟦ τ₁ ⟧ ⋯ σ ⇓ τ₁'  ?
  -- => needs sub-pres-⇓ + ⇓-refl-val τ₁
  -- => needs normalization? ._.
subst-pres-ty (τ-Π x ⊢e₁ ⊢e₂) ⊢σ τ₁σ⇓τ = {!!}
subst-pres-ty τ-★ ⊢σ ⇓-★ = τ-★

subst-pres-ty₁ : {Γ : Ctx µ} →
  Γ ▶ τ₂ ⊢ e₁ ∶ τ₁ →
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
