module Examples.LambdaPi-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Examples.LambdaPi-Kits.Definitions
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (_++_; [])
open import Data.Product renaming (_,_ to _,×_)

⊢-Γ-val :
  Γ ⊢ e ∶ t →
  Values Γ
⊢-Γ-val (τ-` Γ-val x) = Γ-val
⊢-Γ-val (τ-λ ⊢e x ⊢e₁) = ⊢-Γ-val ⊢e
⊢-Γ-val (τ-· ⊢e ⊢e₁ x) = ⊢-Γ-val ⊢e
⊢-Γ-val (τ-Π x ⊢e ⊢e₁) = ⊢-Γ-val ⊢e
⊢-Γ-val (τ-★ Γ-val) = Γ-val

mutual
  wk-pres-neutral : ∀ {t : Term (µ' ++ µ) 𝕥} →
    Neutral t →
    Neutral (t ⋯ (wkᵣ {m' = m'} ↑* µ'))
  wk-pres-neutral `x = `x
  wk-pres-neutral (n · v) = wk-pres-neutral n · wk-pres-val v

  wk-pres-val : ∀ {t : Term (µ' ++ µ) 𝕥} →
    Value t →
    Value (t ⋯ (wkᵣ {m' = m'} ↑* µ'))
  wk-pres-val {µ' = µ'} (λ→ v) = λ→ wk-pres-val {µ' = µ' , 𝕥} v
  wk-pres-val {µ' = µ'} (Π v₁ v₂) = Π (wk-pres-val v₁) (wk-pres-val {µ' = µ' , 𝕥} v₂)
  wk-pres-val ★ = ★
  wk-pres-val (neutral x) = neutral (wk-pres-neutral x)

wk-drop-∈-pres-val :
  (x : µ ∋ 𝕥) →
  (t : drop-∈ x µ ∶⊢ 𝕥) →
  Value t →
  Value (wk-drop-∈ x t)
wk-drop-∈-pres-val (here px) t vt = wk-pres-val {µ' = []} vt
wk-drop-∈-pres-val (there x) t vt = wk-pres-val {µ' = []} (wk-drop-∈-pres-val x t vt)

wk-telescope-pres-val :
  Values Γ →
  (x : µ ∋ 𝕥) →
  Value (wk-telescope Γ x)
wk-telescope-pres-val {Γ = Γ} Γ-val x = wk-drop-∈-pres-val x (Γ x) (Γ-val x)

⊢-t-val :
  Γ ⊢ e ∶ t →
  Value t
⊢-t-val (τ-` {Γ = Γ} {x = x} Γ-val p) rewrite (sym p) = wk-telescope-pres-val {Γ = Γ} Γ-val x
⊢-t-val (τ-λ ⊢t₁ (x ,× t₁-val) ⊢e) = Π t₁-val (⊢-t-val ⊢e)
⊢-t-val (τ-· ⊢e₁ ⊢e₂ (x ,× t-val)) = t-val
⊢-t-val (τ-Π x ⊢e ⊢e₁) = ★
⊢-t-val (τ-★ x) = ★

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢t₁ t₁⇓t₁' ⊢e₁) ⊢e₂ t₂⋯t₁⇓t₃) β-λ           = {!!}
subject-reduction (τ-λ ⊢t₁ t₁⇓t₁' ⊢e)                     (ξ-λ e↪e')    = τ-λ ⊢t₁ t₁⇓t₁' (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂ t₂⋯t₁⇓t₃
subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂') t₂⋯t₁⇓t₃
subject-reduction (τ-Π t₁⇓t₁' ⊢t₁ ⊢t₂)                    (ξ-Π₁ t₁↪t₁') = τ-Π {!!} (subject-reduction ⊢t₁ t₁↪t₁') {!⊢t₂!}
subject-reduction (τ-Π t₁⇓t₁' ⊢t₁ ⊢t₂)                    (ξ-Π₂ t₂↪t₂') = τ-Π {!!} ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')

-- subject-reduction :
--   Γ ⊢ e ∶ t →
--   e ↪ e' →
--   Γ ⊢ e' ∶ t
-- subject-reduction (τ-· (τ-λ ⊢t₁ t₁⇓t₁' ⊢e₁) ⊢e₂ t₂⋯t₁⇓t₃) β-λ           = {!!}
-- subject-reduction (τ-λ ⊢t₁ t₁⇓t₁' ⊢e)                     (ξ-λ e↪e')    = τ-λ ⊢t₁ t₁⇓t₁' (subject-reduction ⊢e e↪e')
-- subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₁ e₁↪e₁') = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂ t₂⋯t₁⇓t₃
-- subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₂ e₂↪e₂') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂') t₂⋯t₁⇓t₃
-- subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₁ t₁↪t₁') = τ-Π (subject-reduction ⊢t₁ t₁↪t₁') {!⊢t₂!}
-- subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₂ t₂↪t₂') = τ-Π ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')

-- subject-reduction-t :
--   Values Γ →
--   Γ ⊢ e ∶ t →
--   t ↪ t' →
--   Γ ⊢ e ∶ t'
-- subject-reduction-t Γ-val ⊢e β-λ = {!!}
-- subject-reduction-t Γ-val ⊢e (ξ-λ t↪t') = {!!}
-- subject-reduction-t Γ-val ⊢e (ξ-·₁ t↪t') = {!!}
-- subject-reduction-t Γ-val ⊢e (ξ-·₂ t↪t') = {!!}
-- subject-reduction-t Γ-val ⊢e (ξ-Π₁ t↪t') = {!!}
-- subject-reduction-t Γ-val ⊢e (ξ-Π₂ t↪t') = {!!}

-- subject-reduction :
--   Γ ⊢ e ∶ t →
--   e ↪ e' →
--   t ↪* t' →
--   Γ ⊢ e' ∶ t'
-- subject-reduction (τ-· (τ-λ ⊢t₁ t₁⇓t₁' ⊢e₁) ⊢e₂ t₂⋯t₁⇓t₃) β-λ           t↪*t' = {!!}
-- subject-reduction (τ-λ ⊢t₁ t₁⇓t₁' ⊢e)                     (ξ-λ e↪e')    t↪*t' = {!!} -- τ-λ ⊢t₁ t₁⇓t₁' (subject-reduction ⊢e e↪e' t↪*t')
-- subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₁ e₁↪e₁') t↪*t' = {!!} -- τ-· (subject-reduction ⊢e₁ e₁↪e₁' t↪*t') ⊢e₂ t₂⋯t₁⇓t₃
-- subject-reduction (τ-· ⊢e₁ ⊢e₂ t₂⋯t₁⇓t₃)                  (ξ-·₂ e₂↪e₂') t↪*t' = {!!} -- τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂' t↪*t') t₂⋯t₁⇓t₃
-- subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₁ t₁↪t₁') t↪*t' = {!!} -- τ-Π (subject-reduction ⊢t₁ t₁↪t₁' t↪*t') {!⊢t₂!}
-- subject-reduction (τ-Π ⊢t₁ ⊢t₂)                           (ξ-Π₂ t₂↪t₂') t↪*t' = {!!} -- τ-Π ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂' t↪*t')
