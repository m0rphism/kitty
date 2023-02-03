module Kitty.Examples.STLC.SubjectReduction where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.STLC.Definitions

∋*-id : ∀ {Γ : Ctx µ} →
  Γ ∋* idᵣ ∶ Γ
∋*-id {Γ = Γ} x =
  wk-telescope Γ (idᵣ _ x) ≡⟨⟩
  wk-telescope Γ x         ≡⟨ sym (⋯-id _) ⟩
  wk-telescope Γ x ⋯ idᵣ   ∎

∋*-keep : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₁ ∶⊢ m→M m} →
   Γ₂            ∋*  ρ      ∶  Γ₁ →
  (Γ₂ ▶ (T ⋯ ρ)) ∋* (ρ ↑ m) ∶ (Γ₁ ▶ T)
∋*-keep {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* (here refl) =
  wk-telescope (Γ₂ ▶ (T ⋯ ρ)) ((ρ ↑ _) _ (here refl)) ≡⟨⟩
  T ⋯ ρ ⋯ wk                                          ≡⟨ sym (dist-↑-ren T ρ) ⟩
  T ⋯ wk ⋯ (ρ ↑ _)                                    ≡⟨⟩
  wk-telescope (Γ₁ ▶ T) (here refl) ⋯ ρ ↑ _           ∎
∋*-keep {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* (there x) =
  wk-telescope (Γ₂ ▶ (T ⋯ ρ)) ((ρ ↑ _) _ (there x)) ≡⟨⟩
  wk-telescope Γ₂ (ρ _ x) ⋯ wk                      ≡⟨ cong (_⋯ wk) (∋* x) ⟩
  wk-telescope Γ₁ x ⋯ ρ ⋯ wk                        ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
  wk-telescope Γ₁ x ⋯ wk ⋯ ρ ↑ _                    ≡⟨⟩
  wk-telescope (Γ₁ ▶ T) (there x) ⋯ ρ ↑ _           ∎

∋*-drop : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₂ ∶⊢ m→M m} →
   Γ₂      ∋*  ρ        ∶ Γ₁ →
  (Γ₂ ▶ T) ∋* (wk ∘ᵣ ρ) ∶ Γ₁
∋*-drop {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* x =
  wk-telescope (Γ₂ ▶ T) ((wk ∘ᵣ ρ) _ x)       ≡⟨⟩
  wk-telescope (Γ₂ ▶ T) (((ρ ↑ _) ∘ᵣ wk) _ x) ≡⟨⟩
  wk-telescope Γ₂ (ρ _ x) ⋯ wk                ≡⟨ cong (_⋯ wk) (∋* x) ⟩
  wk-telescope Γ₁ x ⋯ ρ ⋯ wk                  ≡⟨ ⋯-assoc (wk-telescope Γ₁ x) ρ wk ⟩
  wk-telescope Γ₁ x ⋯ wk ∘ᵣ ρ                 ∎

ope-pres-⊢ : ∀ {e : µ₁ ⊢ 𝕖} {t : µ₁ ∶⊢ 𝕖} {ρ : µ₁ →ᵣ µ₂} →
  Γ₂ ∋* ρ ∶ Γ₁ →
  Γ₁ ⊢ e     ∶ t →
  Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)    = τ-` (ope _)
ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)      = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (ope-pres-⊢ (∋*-keep ope) ⊢e))
ope-pres-⊢                       ope (τ-· ⊢e₁ ⊢e₂) = τ-· (ope-pres-⊢ ope ⊢e₁) (ope-pres-⊢ ope ⊢e₂)

wk-pres-⊢ : ∀ {e : µ ⊢ 𝕖} {t : µ ∶⊢ 𝕖} (t' : µ ∶⊢ 𝕖) →
  Γ₂           ⊢ e      ∶ t →
  Γ₂ ▶[ 𝕖 ] t' ⊢ wk _ e ∶ wk _ t
wk-pres-⊢ {Γ₂ = Γ₂} t' ⊢v = ope-pres-⊢ (∋*-drop {Γ₁ = Γ₂} {Γ₂ = Γ₂} {T = t'} (∋*-id {Γ = Γ₂})) ⊢v

-- ope-pres-⊢ : ∀ {e : µ₁ ⊢ 𝕖} {t : µ₁ ∶⊢ 𝕖} {ρ : µ₁ →ᵣ µ₂} →
--   OPE ρ Γ₁ Γ₂ →
--   Γ₁ ⊢ e     ∶ t →
--   Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
-- ope-pres-⊢               {ρ = ρ} ope (τ-` refl)    = τ-` (ope-pres-telescope _ ope)
-- ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)      = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (ope-pres-⊢ (ope-keep ope) ⊢e))
-- ope-pres-⊢                       ope (τ-· ⊢e₁ ⊢e₂) = τ-· (ope-pres-⊢ ope ⊢e₁) (ope-pres-⊢ ope ⊢e₂)

-- wk-pres-⊢ : ∀ {e : µ ⊢ 𝕖} {t : µ ∶⊢ 𝕖} (t' : µ ∶⊢ 𝕖) →
--   Γ₂           ⊢ e      ∶ t →
--   Γ₂ ▶[ 𝕖 ] t' ⊢ wk _ e ∶ wk _ t
-- wk-pres-⊢ t ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (t : µ₁ ∶⊢ 𝕖) →
  Γ₂           ⊢*  σ      ∶ Γ₁ →
  Γ₂ ▶ (t ⋯ σ) ⊢* (σ ↑ 𝕖) ∶ (Γ₁ ▶ t)
lift-⊢* {σ = σ} t ⊢σ (here refl) = τ-` (sym (dist-↑-sub t σ))
lift-⊢* {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} t ⊢σ (there x) =
  subst ((Γ₂ ▶ (t ⋯ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ (σ ↑ 𝕖) ≡⟨ dist-↑-sub (wk-drop-∈ x (Γ₁ x)) σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ σ ⋯ wk       ∎))
        (wk-pres-⊢ (t ⋯ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {e : µ₁ ⊢ 𝕖} {t : µ₁ ∶⊢ 𝕖} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
sub-pres-⊢                     (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {σ = σ}             (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
sub-pres-⊢                     (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)

_,*_ : ∀ {σ : µ₁ →ₛ µ₂} {t : µ₁ ∶⊢ 𝕖} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  e ∶ t ⋯ σ →
  Γ₂ ⊢* σ ,ₛ e ∶ Γ₁ ▶ t
_,*_ {Γ₂ = Γ₂} {e = e} {t = t} ⊢σ ⊢e (here refl) = subst (Γ₂ ⊢ e ∶_) (sym (wk-cancels-,ₛ t _ _)) ⊢e
_,*_ {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢v (there x) = subst (Γ₂ ⊢ σ _ x ∶_) (sym (wk-cancels-,ₛ (wk-drop-∈ x (Γ₁ x)) _ _)) (⊢σ x)

⊢*-idₛ : Γ ⊢* idₛ ∶ Γ
⊢*-idₛ {Γ = Γ} x rewrite ⋯-idₛ (wk-telescope Γ x) = τ-` refl

sub₁-pres-⊢ : ∀ {Γ : Ctx µ} {e₁ : µ ▷ 𝕖 ⊢ 𝕖} {e₂ : µ ⊢ 𝕖} {t₂ : µ ▷ 𝕖 ∶⊢ 𝕖} {t₁ : µ ∶⊢ 𝕖} →
  Γ ▶ t₁ ⊢ e₁ ∶ t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂ ⋯ ⦅ e₂ ⦆
sub₁-pres-⊢ {Γ = Γ} {e₂ = e₂} ⊢e₁ ⊢e₂ = sub-pres-⊢ ⊢e₁ (⊢*-idₛ ,* subst (Γ ⊢ e₂ ∶_) (sym (⋯-id _)) ⊢e₂)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂)  β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (sub₁-pres-⊢ ⊢e₁ ⊢e₂)
subject-reduction (τ-λ ⊢e)                      (ξ-λ e↪e')    = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')