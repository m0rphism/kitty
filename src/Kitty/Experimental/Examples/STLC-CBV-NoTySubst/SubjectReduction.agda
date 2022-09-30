module Kitty.Experimental.Examples.STLC-CBV-NoTySubst.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Definitions

data OPE : µ₁ →ᵣ µ₂ → Ctx µ₁ → Ctx µ₂ → Set where
  ope-id : ∀ {Γ : Ctx µ} →
    OPE idᵣ Γ Γ
  ope-keep  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : Type} →
    OPE  ρ       Γ₁       Γ₂ →
    OPE (ρ ↑ m) (Γ₁ ▶ T) (Γ₂ ▶ T)
  ope-drop  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : Type} {m'} →
    OPE  ρ        Γ₁  Γ₂ →
    OPE (wk {m' = m'} ∘ᵣ ρ) Γ₁ (Γ₂ ▶ T)

ope-pres-telescope : ∀ {ρ : µ₁ →ᵣ µ₂} (x : µ₁ ∋ m) →
  OPE ρ Γ₁ Γ₂ →
  Γ₂ (ρ m x) ≡ Γ₁ x
ope-pres-telescope x ope-id = refl
ope-pres-telescope (here px) (ope-keep ope) = refl
ope-pres-telescope (there x) (ope-keep ope) = ope-pres-telescope x ope
ope-pres-telescope x (ope-drop ope) = ope-pres-telescope x ope

ope-pres-⊢ : ∀ {e : µ₁ ⊢ 𝕖} {t : Type} {ρ : µ₁ →ᵣ µ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ e     ∶ t →
  Γ₂ ⊢ e ⋯ ρ ∶ t
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope )
ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)                   = τ-λ (ope-pres-⊢ (ope-keep ope) ⊢e)
ope-pres-⊢                       ope (τ-· ⊢e₁ ⊢e₂)              = τ-· (ope-pres-⊢ ope ⊢e₁) (ope-pres-⊢ ope ⊢e₂)

wk-pres-⊢ : ∀ {e : µ ⊢ 𝕖} {t : Type} (t' : Type) →
  Γ₂         ⊢ e      ∶ t →
  (_▶_ {m = 𝕖} Γ₂ t') ⊢ wk _ e ∶ t
wk-pres-⊢ t ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (t : Type) →
  Γ₂              ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ▶ t) ⊢* (σ ↑ 𝕖) ∶ (Γ₁ ▶ t)
lift-⊢* {σ = σ} t ⊢σ (here px) = τ-` refl
lift-⊢* {σ = σ} t ⊢σ (there x) = wk-pres-⊢ t (⊢σ x)

sub-pres-⊢ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {e : µ₁ ⊢ 𝕖} {t : Type} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ σ ∶ t
sub-pres-⊢                     (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {σ = σ}             (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢                     (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)

_,*_ : ∀ {σ : µ₁ →ₛ µ₂} {t : Type} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  e ∶ t →
  Γ₂ ⊢* σ ,ₛ e ∶ Γ₁ ▶ t
_,*_ ⊢σ ⊢e (here refl) = ⊢e
_,*_ ⊢σ ⊢v (there x) = ⊢σ x

⊢*-idₛ : Γ ⊢* idₛ ∶ Γ
⊢*-idₛ x = τ-` refl

sub₁-pres-⊢ : ∀ {Γ : Ctx µ} {e₁ : µ ▷ 𝕖 ⊢ 𝕖} {e₂ : µ ⊢ 𝕖} {t₁ t₂ : Type} →
  Γ ▶ t₁ ⊢ e₁ ∶ t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂
sub₁-pres-⊢ {Γ = Γ} {e₂ = e₂} ⊢e₁ ⊢e₂ = sub-pres-⊢ ⊢e₁ (⊢*-idₛ ,* ⊢e₂)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· {t₂ = t₂} (τ-λ ⊢e₁) ⊢e₂) (β-λ e₂-val)         = sub₁-pres-⊢ ⊢e₁ ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁')        = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₁-val e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')

subject-reduction* :
  Γ ⊢ e ∶ t →
  e ↪* e' →
  Γ ⊢ e' ∶ t
subject-reduction* ⊢e ↪*-refl = ⊢e
subject-reduction* ⊢e (↪*-step e₁↪e₂ e₂↪*e₃) = subject-reduction* (subject-reduction ⊢e e₁↪e₂) e₂↪*e₃
