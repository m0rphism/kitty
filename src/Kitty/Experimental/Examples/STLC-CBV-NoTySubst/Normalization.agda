module Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Normalization where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning; inspect; [_])
open import Relation.Nullary using (¬_)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using () renaming (_∋_ to _by_)
open import Data.Product using (_×_; ∃-syntax; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Definitions
open import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.SubjectReduction

-- Definition of the Logical Relation ------------------------------------------

mutual
  SN : Type → [] ⊢ 𝕖 → Set
  SN t e = (∅ ⊢ e ∶ t) × (e ⇓) × SN-Pres t e

  SN-Pres : Type → [] ⊢ 𝕖 → Set
  SN-Pres 𝟘         e = ⊤
  SN-Pres (t₁ ⇒ t₂) e = ∀ e' → SN t₁ e' → SN t₂ (e · e')

-- SN is preserved along ↪* ----------------------------------------------------

↪-val-absurd : e ↪ e' → ¬ Value e
↪-val-absurd () λxe

↪-deterministic :
  e ↪ e₁ →
  e ↪ e₂ →
  e₁ ≡ e₂
↪-deterministic (β-λ _)       (β-λ _)              = refl
↪-deterministic (β-λ val-e₂)  (ξ-·₂ _ e₂↪e₂')      = ⊥-elim (↪-val-absurd e₂↪e₂' val-e₂)
↪-deterministic (ξ-·₁ e₁↪e₁') (ξ-·₁ e₁↪e₂')        = cong (_· _) (↪-deterministic e₁↪e₁' e₁↪e₂')
↪-deterministic (ξ-·₁ e₁↪e₁') (ξ-·₂ val-e₁ e₂↪e₂') = ⊥-elim (↪-val-absurd e₁↪e₁' val-e₁)
↪-deterministic (ξ-·₂ val-e₁ e₂↪e₂') (β-λ val-e₂)  = ⊥-elim (↪-val-absurd e₂↪e₂' val-e₂)
↪-deterministic (ξ-·₂ val-e₁ e₂↪e₂') (ξ-·₁ e₁↪e₁') = ⊥-elim (↪-val-absurd e₁↪e₁' val-e₁)
↪-deterministic (ξ-·₂ val-e₁ e₂↪e₂') (ξ-·₂ val-e₁' e₂↪e₂'') = cong (_ ·_) (↪-deterministic e₂↪e₂' e₂↪e₂'')

↪-pres-⇓-fwd :
  e ↪ e' →
  e ⇓ →
  e' ⇓
↪-pres-⇓-fwd v↪e' (v , ↪*-refl , val-v) = ⊥-elim (↪-val-absurd v↪e' val-v)
↪-pres-⇓-fwd e→e' (v , ↪*-step e↪e'' e''↪*v , val-v)
    with ↪-deterministic e→e' e↪e''
... | refl = v , e''↪*v , val-v

↪-pres-⇓-bwd :
  e ↪ e' →
  e' ⇓ →
  e ⇓
↪-pres-⇓-bwd e→e' (v , e↪*v , val-v) = v , ↪*-step e→e' e↪*v , val-v

mutual
  ↪-pres-SN-fwd :
    e ↪ e' →
    SN t e →
    SN t e'
  ↪-pres-SN-fwd e↪e' (⊢e , e⇓ , e-pres-sn) =
    subject-reduction ⊢e e↪e' ,
    ↪-pres-⇓-fwd e↪e' e⇓ ,
    ↪-pres-SN-Pres-fwd e↪e' e-pres-sn

  ↪-pres-SN-Pres-fwd :
    e ↪ e' →
    SN-Pres t e →
    SN-Pres t e'
  ↪-pres-SN-Pres-fwd {t = 𝟘} e↪e' e-pres-sn = e-pres-sn
  ↪-pres-SN-Pres-fwd {t = t₁ ⇒ t₂} e↪e' e-pres-sn =
    λ { e' sn-e' → ↪-pres-SN-fwd (ξ-·₁ e↪e') (e-pres-sn e' sn-e') }

↪*-pres-SN-fwd :
  e ↪* e' →
  SN t e →
  SN t e'
↪*-pres-SN-fwd ↪*-refl sn = sn
↪*-pres-SN-fwd (↪*-step e₁↪e₂ e₂↪*e₃) sn = ↪*-pres-SN-fwd e₂↪*e₃ (↪-pres-SN-fwd e₁↪e₂ sn)

mutual
  ↪-pres-SN-bwd :
    ∅ ⊢ e ∶ t →
    e ↪ e' →
    SN t e' →
    SN t e
  ↪-pres-SN-bwd ⊢e e↪e' (⊢e' , e'⇓ , e'-pres-sn) =
    ⊢e ,
    ↪-pres-⇓-bwd e↪e' e'⇓ ,
    ↪-pres-SN-Pres-bwd ⊢e e↪e' e'-pres-sn

  ↪-pres-SN-Pres-bwd :
    ∅ ⊢ e ∶ t →
    e ↪ e' →
    SN-Pres t e' →
    SN-Pres t e
  ↪-pres-SN-Pres-bwd {t = 𝟘} ⊢e e↪e' e-pres-sn = e-pres-sn
  ↪-pres-SN-Pres-bwd {t = t₁ ⇒ t₂} ⊢e e↪e' e-pres-sn =
    λ { e' sn-e'@(⊢e' , _) → ↪-pres-SN-bwd (τ-· ⊢e ⊢e') (ξ-·₁ e↪e') (e-pres-sn e' sn-e') }

↪*-pres-SN-bwd :
  ∅ ⊢ e ∶ t →
  e ↪* e' →
  SN t e' →
  SN t e
↪*-pres-SN-bwd ⊢e ↪*-refl sn = sn
↪*-pres-SN-bwd ⊢e (↪*-step e₁↪e₂ e₂↪*e₃) sn =
  ↪-pres-SN-bwd ⊢e e₁↪e₂ (↪*-pres-SN-bwd (subject-reduction ⊢e e₁↪e₂) e₂↪*e₃ sn)

-- SN Substitution -------------------------------------------------------------

SNSub : Ctx µ₁ → µ₁ →ₛ [] → Set
SNSub Γ₁ σ = ∀ x → SN (Γ₁ x) (σ 𝕖 x)

SNSub→⊢* : {σ : µ₁ →ₛ []} →
  SNSub Γ₁ σ →
  ∅ ⊢* σ ∶ Γ₁
SNSub→⊢* snsub x = proj₁ (snsub x)

SNSub-id : SNSub ∅ idₛ
SNSub-id ()

SNSub-ext : {σ : µ₁ →ₛ []} →
  SNSub Γ₁ σ →
  Value e →
  SN t e →
  SNSub (Γ₁ ▶ t) (σ ,ₛ e)
SNSub-ext {Γ₁ = Γ₁} {e = e} {t = t} {σ = σ} SN-σ val-e SN-e (here refl) = SN-e
SNSub-ext {Γ₁ = Γ₁} {e = e} {t = t} {σ = σ} SN-σ val-e SN-e (there x) = SN-σ x

-- Transitive Closures of Congruency Rules -------------------------------------

-- TODO: can we automatically derive those wrappers?
ξ-·₁* :
  e₁ ↪* e₁' →
  (e₁ · e₂) ↪* (e₁' · e₂)
ξ-·₁* ↪*-refl = ↪*-refl
ξ-·₁* (↪*-step e₁↪e₁' e₁'↪*e₁'') = ↪*-step (ξ-·₁ e₁↪e₁') (ξ-·₁* e₁'↪*e₁'')

ξ-·₂* :
  Value e₁ →
  e₂ ↪* e₂' →
  (e₁ · e₂) ↪* (e₁ · e₂')
ξ-·₂* val-e₁ ↪*-refl = ↪*-refl
ξ-·₂* val-e₁ (↪*-step e₂↪e₂' e₂'↪*e₂'') = ↪*-step (ξ-·₂ val-e₁ e₂↪e₂') (ξ-·₂* val-e₁ e₂'↪*e₂'')

-- Strong Normalization --------------------------------------------------------

⊢→SN : {σ : µ₁ →ₛ []} →
  Γ ⊢ e ∶ t →
  SNSub Γ σ →
  SN t (e ⋯ σ)
⊢→SN (τ-` {x = x} refl) SNσ = SNσ x
⊢→SN {σ = σ} (τ-· {e₁ = e₁} {t₁ = t₁} {t₂ = t₂} {e₂ = e₂} ⊢e₁ ⊢e₂) SNσ with ⊢→SN ⊢e₁ SNσ | ⊢→SN ⊢e₂ SNσ
... | (_ , _ , [e₁⋯σ]-pres) | SNe₂ =
  SN t₂ ((e₁ · e₂) ⋯ σ) by (
  SN t₂ ((e₁ ⋯ σ) · (e₂ ⋯ σ)) by (
    [e₁⋯σ]-pres (e₂ ⋯ σ) SNe₂))
⊢→SN {Γ = Γ} {σ = σ} ⊢λe@(τ-λ {t₁ = t₁} {e = e} {t₂ = t₂} ⊢e) SNσ =
  sub-pres-⊢ ⊢λe (SNSub→⊢* {Γ₁ = Γ} {σ = σ} SNσ) , -- TODO: why do we need to specify Γ ?!?!
  (_ , ↪*-refl , λxe) ,
  (SN-Pres (t₁ ⇒ t₂) ((λx e) ⋯ σ) by (
   SN-Pres (t₁ ⇒ t₂) (λx (e ⋯ (σ ↑ 𝕖))) by
  λ { e' SNe'@(⊢e' , (v' , e'↪*v' , val-v') , e'-pres) →
    let SNv' = ↪*-pres-SN-fwd e'↪*v' SNe' in 
    let SN[σ,v] = SNSub-ext SNσ val-v' SNv' in
    let SN[e⋯σ,v] = ⊢→SN ⊢e SN[σ,v] in
    SN t₂ ((λx (e ⋯ σ ↑ 𝕖)) · e') by ↪*-pres-SN-bwd
      (τ-· (sub-pres-⊢ ⊢λe (SNSub→⊢* {Γ₁ = Γ} {σ = σ} SNσ)) ⊢e')
      (let p1 = ((λx e) ⋯ σ) · e' ↪* e ⋯ σ ↑ 𝕖 ⋯ ⦅ v' ⦆ by ↪*-trans (ξ-·₂* λxe e'↪*v') (↪*-step (β-λ val-v') ↪*-refl) in
       ((λx e) ⋯ σ) · e' ↪* e ⋯ (σ ,ₛ v') by subst (_ ↪*_) (⋯↑⋯⦅⦆-is-⋯,ₛ e v' σ) p1)
      (SN t₂ (e ⋯ (σ ,ₛ v')) by SN[e⋯σ,v])
  }))

SN→⇓ :
  SN t e →
  e ⇓
SN→⇓ (_ , e⇓ , _) = e⇓

strong-normalization :
  ∅ ⊢ e ∶ t →
  e ⇓
strong-normalization ⊢e =
  let SN[e⋯id] = ⊢→SN ⊢e SNSub-id in
  let [e⋯id]⇓ = SN→⇓ SN[e⋯id] in
  let e⇓ = subst (_⇓) (⋯-id _) [e⋯id]⇓ in
  e⇓
