module Kitty.Examples.STLC.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Examples.STLC.Definitions

ope-pres-⊢ : ∀ {e : µ₁ ⊢ 𝕖} {t : µ₁ ∶⊢ 𝕖} {ρ : µ₁ →ᵣ µ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ e     ∶ t →
  Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (ope-pres-⊢ (ope-keep ope) ⊢e))
ope-pres-⊢                       ope (τ-· ⊢e₁ ⊢e₂)              = τ-· (ope-pres-⊢ ope ⊢e₁) (ope-pres-⊢ ope ⊢e₂)

wk-pres-⊢ : ∀ {e : µ ⊢ 𝕖} {t : µ ∶⊢ 𝕖} (t' : µ ∶⊢ 𝕖) →
  Γ₂         ⊢ e      ∶ t →
  (_▶_ {m = 𝕖} Γ₂ t') ⊢ wk _ e ∶ wk _ t
wk-pres-⊢ t ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (t : µ₁ ∶⊢ 𝕖) →
  Γ₂             ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ▶ (t ⋯ σ)) ⊢* (σ ↑ 𝕖) ∶ (Γ₁ ▶ t)
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

sub₁-pres-⊢ : ∀ {Γ : Ctx µ} {e₁ : 𝕖 ∷ µ ⊢ 𝕖} {e₂ : µ ⊢ 𝕖} {t₂ : µ ▷ 𝕖 ∶⊢ 𝕖} {t₁ : µ ∶⊢ 𝕖} →
  Γ ▶ t₁ ⊢ e₁ ∶ t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂ ⋯ ⦅ e₂ ⦆
sub₁-pres-⊢ {Γ = Γ} {e₂ = e₂} ⊢e₁ ⊢e₂ = sub-pres-⊢ ⊢e₁ (⊢*-idₛ ,* subst (Γ ⊢ e₂ ∶_) (sym (⋯-id _)) ⊢e₂)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂) (β-λ e₂-val)         = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ t₂ _) (sub₁-pres-⊢ ⊢e₁ ⊢e₂)
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁')        = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₁-val e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')

subject-reduction* :
  Γ ⊢ e ∶ t →
  e ↪* e' →
  Γ ⊢ e' ∶ t
subject-reduction* ⊢e ↪*-refl = ⊢e
subject-reduction* ⊢e (↪*-step e₁↪e₂ e₂↪*e₃) = subject-reduction* (subject-reduction ⊢e e₁↪e₂) e₂↪*e₃
