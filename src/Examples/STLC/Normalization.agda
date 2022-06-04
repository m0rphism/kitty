module Examples.STLC.Normalization where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning; inspect; [_])
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using () renaming (_∋_ to _by_)
open import Data.Product using (_×_; ∃-syntax; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Examples.STLC.Definitions hiding (_,_)
open import Examples.STLC.SubjectReduction
open import Examples.STLC.Progress

mutual
  SN : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕖 → Set
  SN Γ t e = (Γ ⊢ e ∶ t) × (e ⇓) × SN-Pres Γ t e

  SN-Pres : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕖 → Set
  SN-Pres Γ 𝟘         e = ⊤
  SN-Pres Γ (t₁ ⇒ t₂) e = ∀ e' → SN Γ t₁ e' → SN Γ t₂ (e · e')

mutual
  ↪-neutral-absurd : e ↪ e' → Neutral e → ⊥
  ↪-neutral-absurd (ξ-·₁ e₁↪e₁') (neutral-e₁ · _) = ↪-neutral-absurd e₁↪e₁' neutral-e₁
  ↪-neutral-absurd (ξ-·₂ _ e₂↪e₂') (_ · val-e₂) = ↪-val-absurd e₂↪e₂' val-e₂

  ↪-val-absurd : e ↪ e' → Value e → ⊥
  ↪-val-absurd e↪e' (neutral n) = ↪-neutral-absurd e↪e' n

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
↪-pres-⇓-fwd e→e' (v , ↪*-refl , val-v) = ⊥-elim (↪-val-absurd e→e' val-v)
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
    SN Γ t e →
    SN Γ t e'
  ↪-pres-SN-fwd e↪e' (⊢e , e⇓ , e-pres-sn) =
    subject-reduction ⊢e e↪e' ,
    ↪-pres-⇓-fwd e↪e' e⇓ ,
    ↪-pres-SN-Pres-fwd e↪e' e-pres-sn

  ↪-pres-SN-Pres-fwd :
    e ↪ e' →
    SN-Pres Γ t e →
    SN-Pres Γ t e'
  ↪-pres-SN-Pres-fwd {t = 𝟘} e↪e' e-pres-sn = e-pres-sn
  ↪-pres-SN-Pres-fwd {t = t₁ ⇒ t₂} e↪e' e-pres-sn =
    λ { e' sn-e' → ↪-pres-SN-fwd (ξ-·₁ e↪e') (e-pres-sn e' sn-e') }

↪*-pres-SN-fwd :
  e ↪* e' →
  SN Γ t e →
  SN Γ t e'
↪*-pres-SN-fwd ↪*-refl sn = sn
↪*-pres-SN-fwd (↪*-step e₁↪e₂ e₂↪*e₃) sn = ↪*-pres-SN-fwd e₂↪*e₃ (↪-pres-SN-fwd e₁↪e₂ sn)

mutual
  ↪-pres-SN-bwd :
    Γ ⊢ e ∶ t →
    e ↪ e' →
    SN Γ t e' →
    SN Γ t e
  ↪-pres-SN-bwd ⊢e e↪e' (⊢e' , e'⇓ , e'-pres-sn) =
    ⊢e ,
    ↪-pres-⇓-bwd e↪e' e'⇓ ,
    ↪-pres-SN-Pres-bwd ⊢e e↪e' e'-pres-sn

  ↪-pres-SN-Pres-bwd :
    Γ ⊢ e ∶ t →
    e ↪ e' →
    SN-Pres Γ t e' →
    SN-Pres Γ t e
  ↪-pres-SN-Pres-bwd {t = 𝟘} ⊢e e↪e' e-pres-sn = e-pres-sn
  ↪-pres-SN-Pres-bwd {t = t₁ ⇒ t₂} ⊢e e↪e' e-pres-sn =
    λ { e' sn-e'@(⊢e' , _) → ↪-pres-SN-bwd (τ-· ⊢e ⊢e') (ξ-·₁ e↪e') (e-pres-sn e' sn-e') }

↪*-pres-SN-bwd :
  Γ ⊢ e ∶ t →
  e ↪* e' →
  SN Γ t e' →
  SN Γ t e
↪*-pres-SN-bwd ⊢e ↪*-refl sn = sn
↪*-pres-SN-bwd ⊢e (↪*-step e₁↪e₂ e₂↪*e₃) sn =
  ↪-pres-SN-bwd ⊢e e₁↪e₂ (↪*-pres-SN-bwd (subject-reduction ⊢e e₁↪e₂) e₂↪*e₃ sn)

SNSub : Ctx µ₁ → µ₁ →ₛ µ₂ → Ctx µ₂ → Set
SNSub Γ₁ σ Γ₂ = ∀ x → SN Γ₂ (wk-telescope Γ₁ x ⋯ σ) (σ 𝕖 x) × Value (σ 𝕖 x)

SNSub→⊢* : {σ : µ₁ →ₛ µ₂} →
  SNSub Γ₁ σ Γ₂ →
  Γ₂ ⊢* σ ∶ Γ₁
SNSub→⊢* snsub x with snsub x
... | (⊢σx , _ , _) , _ = ⊢σx

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

mutual
  val→⇓ :
    Value e →
    e ⇓
  val→⇓ λxe         = _ , ↪*-refl , λxe
  val→⇓ (neutral n) with neutral→⇓ n
  ... | e' , e→e' , e'-neutral = e' , e→e' , neutral e'-neutral

  neutral→⇓ :
    Neutral e →
    e ⇓ₙ
  neutral→⇓ `x      = _ , ↪*-refl , `x
  neutral→⇓ (n · v) with neutral→⇓ n | val→⇓ v
  ... | e₁' , e₁↪*e₁' , e₁'-neutral | e₂' , e₂↪*e₂' , e₂'-val =
    let [e₁·e₂]↪*[e₁'·e₂'] = ↪*-trans (ξ-·₁* e₁↪*e₁') (ξ-·₂* (neutral e₁'-neutral) e₂↪*e₂')
    in e₁' · e₂' , [e₁·e₂]↪*[e₁'·e₂'] , e₁'-neutral · e₂'-val

-- TODO: Library extension: we probably can make a `wk-telescope'` which does the subst.
SNSub-ext : {σ : µ₁ →ₛ µ₂} →
  SNSub Γ₁ σ Γ₂ →
  Value e →
  SN Γ₂ (t ⋯ σ) e →
  SNSub (Γ₁ ,, t) (σ ,ₛ e) Γ₂
SNSub-ext {Γ₁ = Γ₁} {Γ₂ = Γ₂} {e = e} {t = t} {σ = σ} sn-σ val-e sn-e (here refl) =
  let sn-e' =
        SN Γ₂ (wk-telescope (Γ₁ ,, t) (here refl) ⋯ (σ ,ₛ e)) ((σ ,ₛ e) 𝕖 (here refl))
          by (
        SN Γ₂ (t ⋯ wk ⋯ (σ ,ₛ e)) e
          by subst (λ ■ → SN Γ₂ ■ e) (sym (wk-cancels-,ₛ t σ e)) (
        SN Γ₂ (t ⋯ σ) e
          by sn-e))
  in sn-e' , val-e
SNSub-ext {Γ₁ = Γ₁} {Γ₂ = Γ₂} {e = e} {t = t} {σ = σ} sn-σ val-e sn-e (there x) with sn-σ x
... | sn-σx , val-σx =
  let sn-σx' =
        SN Γ₂ (wk-telescope (Γ₁ ,, t) (there x) ⋯ (σ ,ₛ e)) ((σ ,ₛ e) 𝕖 (there x))
          by (
        SN Γ₂ (wk-telescope Γ₁ x ⋯ wk ⋯ (σ ,ₛ e)) (σ 𝕖 x)
          by subst (λ ■ → SN Γ₂ ■ (σ 𝕖 x)) (sym (wk-cancels-,ₛ (wk-telescope Γ₁ x) σ e)) (
        SN Γ₂ (wk-telescope Γ₁ x ⋯ σ) (σ 𝕖 x)
          by sn-σx))
  in sn-σx' , val-σx

sub-SN : {σ : µ₁ →ₛ µ₂} →
  SNSub Γ₁ σ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  SN Γ₂ (t ⋯ σ) (e ⋯ σ)
sub-SN {Γ₁ = Γ₁} snsub ⊢e@(τ-` {x = x} refl) with snsub x
... | (⊢σx , σx⇓ , pres-σx) , val-σx = sub-pres-⊢ ⊢e (SNSub→⊢* {Γ₁ = Γ₁} snsub) , σx⇓ , pres-σx
sub-SN snsub (τ-· ⊢e₁ ⊢e₂) with sub-SN snsub ⊢e₁
... | ⊢e₁σ , e₁σ⇓ , e₁σ-pres = e₁σ-pres _ (sub-SN snsub ⊢e₂)
sub-SN {Γ₁ = Γ₁} {Γ₂ = Γ₂} {σ = σ} snsub (τ-λ {t₁ = t₁} {e = e} {t₂ = t₂} ⊢e) =
  let ⊢λx[e⋯σ] = τ-λ (
        Γ₂ ,, (t₁ ⋯ σ) ⊢ e ⋯ σ ↑ₛ 𝕖 ∶ t₂ ⋯ σ ⋯ wk
          by subst (λ ■ → Γ₂ ,, (t₁ ⋯ σ) ⊢ e ⋯ σ ↑ₛ 𝕖 ∶ ■) (dist-↑-sub t₂ σ) (
        Γ₂ ,, (t₁ ⋯ σ) ⊢ e ⋯ σ ↑ₛ 𝕖 ∶ t₂ ⋯ wk ⋯ (σ ↑ₛ 𝕖)
          by sub-pres-⊢ ⊢e (
        Γ₂ ,, (t₁ ⋯ σ) ⊢* σ ↑ₛ 𝕖 ∶ Γ₁ ,, t₁
          by lift-⊢* t₁ (
        Γ₂             ⊢* σ      ∶ Γ₁
          by SNSub→⊢* {Γ₁ = Γ₁} snsub
        ))))
      λx[e⋯σ]·e'-pres-sn = λ { e' sn-e'@(⊢e' , (v' , e'↪*v' , val-v') , e'-pres) →
        let sn-v' = ↪*-pres-SN-fwd e'↪*v' sn-e' in
        SN Γ₂ (t₂ ⋯ σ) ((λx (e ⋯ σ ↑ₛ 𝕖)) · e')
          by ↪*-pres-SN-bwd (τ-· ⊢λx[e⋯σ] ⊢e') (↪*-trans (ξ-·₂* λxe e'↪*v') (↪*-step (β-λ val-v') ↪*-refl)) (
        SN Γ₂ (t₂ ⋯ σ) (e ⋯ σ ↑ₛ 𝕖 ⋯ ⦅ v' ⦆)
          by subst (λ ■ → SN Γ₂ (t₂ ⋯ σ) ■) (sym (⋯↑⋯⦅⦆-is-⋯,ₛ e v' σ)) (
        SN Γ₂ (t₂ ⋯ σ) (e ⋯ (σ ,ₛ v'))
          by subst (λ ■ → SN Γ₂ ■ (e ⋯ (σ ,ₛ v'))) (wk-cancels-,ₛ t₂ σ v') (
        SN Γ₂ (t₂ ⋯ wk ⋯ (σ ,ₛ v')) (e ⋯ (σ ,ₛ v'))
          by sub-SN (SNSub-ext snsub val-v' sn-v') ⊢e)))
        }
  in ⊢λx[e⋯σ] , val→⇓ λxe , λx[e⋯σ]·e'-pres-sn

mutual
  SN-Pres-id :
    SN-Pres Γ (wk-telescope Γ x) (` x)
  SN-Pres-id {Γ = Γ} {x = x} with wk-telescope Γ x | inspect (wk-telescope Γ) x
  ... | 𝟘       | _ = tt
  ... | t₁ ⇒ t₂ | [ ⊢x ] = λ { e' sn-e'@(⊢e' , (e'' , e'→*e'' , val-e'') , e'-pres) →
            SN Γ t₂ (` x · e')
              by ↪*-pres-SN-bwd
                   (τ-· (τ-` ⊢x) ⊢e')
                   (ξ-·₂* (neutral `x) e'→*e'') (
            SN Γ t₂ (` x · e'')
              by ·-pres-SN (neutral `x) (τ-` ⊢x) val-e'' (
            SN Γ t₁ e''
              by ↪*-pres-SN-fwd e'→*e'' sn-e'))
          }

  SNSub-id :
    SNSub Γ idₛ Γ
  SNSub-id {Γ = Γ} x =
    ( (Γ ⊢ idₛ 𝕖 x ∶ wk-telescope Γ x ⋯ idₛ
         by τ-` (sym (⋯-id _)))
    , (idₛ 𝕖 x ⇓
         by val→⇓ (neutral `x))
    , (SN-Pres Γ (wk-telescope Γ x ⋯ idₛ) (idₛ 𝕖 x)
         by subst (λ ■ → SN-Pres Γ ■ (idₛ 𝕖 x)) (sym (⋯-id _)) (
       SN-Pres Γ (wk-telescope Γ x) (idₛ 𝕖 x)
         by SN-Pres-id))
    )
    , (Value (idₛ 𝕖 x)
         by neutral `x)

  -- SN-Pres-neutral :
  --   Γ ⊢ e ∶ t →
  --   Neutral e →
  --   SN-Pres Γ t e
  -- SN-Pres-neutral {t = 𝟘} ⊢e neu-e = tt
  -- -- SN-Pres-neutral {Γ = Γ} {e = ` x} {t = t₁ ⇒ t₂} ⊢e `x = {!!}
  -- -- SN-Pres-neutral {Γ = Γ} {e = e₁ · e₂} {t = t₁ ⇒ t₂} ⊢e (neu-e · x) = {!!}
  -- SN-Pres-neutral {Γ = Γ} {e = e} {t = t₁ ⇒ t₂} ⊢e neu-e =
  --   λ { e' sn-e'@(⊢e' , (e'' , e'→e'' , val-e'') , e'-pres) →
  --     SN Γ t₂ (e · e')
  --       by ↪*-pres-SN-bwd
  --         (Γ ⊢ e · e' ∶ t₂       by τ-· ⊢e ⊢e')
  --         ((e · e') ↪* (e · e'') by ξ-·₂* (neutral neu-e) e'→e'')
  --         (SN Γ t₂ (e · e'')     by
  --           {!!}
  --         )
  --         -- (SN Γ t₂ (e · e'')     by ·-pres-SN val-e ⊢e val-e''
  --         --   (SN Γ t₁ e'' by ↪*-pres-SN-fwd e'→e'' sn-e'))
  --   }

  -- SN-Pres-val :
  --   Γ ⊢ e ∶ t →
  --   Value e →
  --   SN-Pres Γ t e
  -- SN-Pres-val = {!!}
  -- SN-Pres-val {t = 𝟘} ⊢e val-e = tt
  -- SN-Pres-val {Γ = Γ} {e = e} {t = t₁ ⇒ t₂} ⊢e val-e =
  --   λ { e' sn-e'@(⊢e' , (e'' , e'→e'' , val-e'') , e'-pres) →
  --     SN Γ t₂ (e · e')
  --       by ↪*-pres-SN-bwd
  --         (Γ ⊢ e · e' ∶ t₂       by τ-· ⊢e ⊢e')
  --         ((e · e') ↪* (e · e'') by ξ-·₂* val-e e'→e'')
  --         (SN Γ t₂ (e · e'')     by
  --           {!!}
  --         )
  --         -- (SN Γ t₂ (e · e'')     by ·-pres-SN val-e ⊢e val-e''
  --         --   (SN Γ t₁ e'' by ↪*-pres-SN-fwd e'→e'' sn-e'))
  --   }

  ·-pres-SN :
    Value e₁ →
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Value e₂ →
    SN Γ t₁ e₂ →
    SN Γ t₂ (e₁ · e₂)
  ·-pres-SN {Γ = Γ} {t₁ = t₁} {t₂ = t₂} {e₂ = e₂} λxe ⊢e₁@(τ-λ {e = e} ⊢e) val-e₂ sn-e₂@(⊢e₂ , _) =
    let ⊢e₁σ = subject-reduction (τ-· ⊢e₁ ⊢e₂) (β-λ val-e₂) in
    ↪-pres-SN-bwd (τ-· ⊢e₁ ⊢e₂) (β-λ val-e₂) (
      SN Γ t₂ (e ⋯ ⦅ e₂ ⦆)
        by subst (λ ■ → SN Γ ■ (e ⋯ ⦅ e₂ ⦆)) (⋯-id t₂) (
      SN Γ (t₂ ⋯ idₛ) (e ⋯ ⦅ e₂ ⦆)
        by subst (λ ■ → SN Γ ■ (e ⋯ ⦅ e₂ ⦆)) (wk-cancels-,ₛ t₂ idₛ e₂) (
      SN Γ (t₂ ⋯ wk ⋯ ⦅ e₂ ⦆) (e ⋯ ⦅ e₂ ⦆)
        by sub-SN (SNSub-ext SNSub-id val-e₂ (subst (λ ■ → SN Γ ■ e₂) (sym (⋯-id t₁)) sn-e₂)) ⊢e)))
  ·-pres-SN {e₁ = e₁} {Γ = Γ} {t₁ = t₁} {t₂ = t₂} {e₂ = e₂} val-e₁@(neutral neutral-e₁) ⊢e₁ val-e₂
            sn-e₂@(⊢e₂ , e₂⇓@(e₂' , e₂↪*e₂' , val-e₂') , e₂-pres) =
    let val[e₁·e₂] = neutral (neutral-e₁ · val-e₂)
        ⊢[e₁·e₂] = τ-· ⊢e₁ ⊢e₂
    in
    SN Γ t₂ (e₁ · e₂)
      by (Γ ⊢ e₁ · e₂ ∶ t₂       by ⊢[e₁·e₂])
       , ((e₁ · e₂) ⇓            by e₁ · e₂ , ↪*-refl , val[e₁·e₂])
       , (SN-Pres Γ t₂ (e₁ · e₂) by {!SN-Pres-val ⊢[e₁·e₂] val[e₁·e₂]!})

⊢→SN :
  Γ ⊢ e ∶ t →
  SN Γ t e
⊢→SN {t = t₁ ⇒ t₂} (τ-` {x = x} Γx≡t₁⇒t₂) =
  τ-` Γx≡t₁⇒t₂ , (` x , ↪*-refl , neutral `x)  ,
  λ { e' sn-e'@(⊢e' , (e'' , e'→e'' , val-e'') , e'-pres) →
        ↪*-pres-SN-bwd
          (τ-· (τ-` Γx≡t₁⇒t₂) ⊢e')
          (ξ-·₂* (neutral `x) e'→e'')
          (·-pres-SN (neutral `x) (τ-` Γx≡t₁⇒t₂) val-e''
            (↪*-pres-SN-fwd e'→e'' sn-e'))
    }
⊢→SN {t = 𝟘} (τ-` {x = x} Γx≡𝟘) =
  τ-` Γx≡𝟘 , (` x  , ↪*-refl , neutral `x) , tt
⊢→SN (τ-λ ⊢e) =
  τ-λ ⊢e , (_ , ↪*-refl , λxe) ,
  λ { e' sn-e'@(⊢e' , (e'' , e'→e'' , val-e'') , e'-pres) →
        ↪*-pres-SN-bwd
          (τ-· (τ-λ ⊢e) ⊢e')
          (ξ-·₂* λxe e'→e'')
          (·-pres-SN λxe (τ-λ ⊢e) val-e''
            (↪*-pres-SN-fwd e'→e'' sn-e'))
    }
⊢→SN (τ-· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂)
    with ⊢→SN ⊢e₁ | ⊢→SN ⊢e₂
... | _ , e₁⇓ , p | sn₂      = p e₂ sn₂

strong-normalization :
  Γ ⊢ e ∶ t →
  e ⇓
strong-normalization ⊢e with ⊢→SN ⊢e
... | _ , e⇓ , _ = e⇓
