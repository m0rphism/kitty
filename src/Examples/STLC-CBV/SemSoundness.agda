module Examples.STLC-CBV.SemSoundness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning; inspect; [_])
open import Relation.Nullary using (¬_)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (_$_) renaming (_∋_ to _by_)
open import Data.Product using (_×_; ∃-syntax; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; _because_)

open import Examples.STLC-CBV.Definitions hiding (_,_)
open import Examples.STLC-CBV.SubjectReduction
open import Examples.STLC-CBV.Progress

-- Definition of the Logical Relation ------------------------------------------

Red : µ ⊢ 𝕖 → Set
Red e = ∃[ e' ] (e ↪ e')

Irred : µ ⊢ 𝕖 → Set
Irred e = ¬ Red e

Safe : µ ⊢ 𝕖 → Set
Safe e = ∀ e' → e ↪* e' → Value e' ⊎ Red e'

infix 3  _∈𝕍⟦_⟧  _∈𝔼⟦_⟧  _∈𝔾⟦_⟧  _⊧_∶_

mutual

  _∈𝕍⟦_⟧ : [] ⊢ 𝕖 → [] ⊢ 𝕥 → Set
  λx e ∈𝕍⟦ t₁ ⇒ t₂ ⟧ = ∀ v → v ∈𝕍⟦ t₁ ⟧ → (e ⋯ ⦅ v ⦆) ∈𝔼⟦ t₂ ⟧
  _    ∈𝕍⟦ _       ⟧ = ⊥

  _∈𝔼⟦_⟧ : [] ⊢ 𝕖 → [] ⊢ 𝕥 → Set
  e ∈𝔼⟦ t ⟧ = ∀ {e'} → e ↪* e' → Irred e' → e' ∈𝕍⟦ t ⟧

_∈𝔾⟦_⟧ : ∀ {µ} → µ →ₛ [] → Ctx µ → Set
_∈𝔾⟦_⟧ {µ = µ} σ Γ  = (x : µ ∋ 𝕖) → σ 𝕖 x ∈𝕍⟦ wk-telescope Γ x ⋯ σ ⟧ 

idₛ∈𝔾⟦∅⟧ : idₛ ∈𝔾⟦ ∅ ⟧
idₛ∈𝔾⟦∅⟧ ()

_,𝔾_ : ∀ {e} {t} {σ} {Γ : Ctx µ} →
  e ∈𝕍⟦ t ⋯ σ ⟧ →
  σ ∈𝔾⟦ Γ ⟧ →
  (σ ,ₛ e) ∈𝔾⟦ Γ ▶ t ⟧
_,𝔾_ {µ} {e} {t} {σ} {Γ} e∈ σ∈ (here refl) =
    (σ ,ₛ e) 𝕖 (here refl) ∈𝕍⟦ wk-telescope (Γ ▶ t) (here refl) ⋯ (σ ,ₛ e) ⟧
  by (
    e ∈𝕍⟦ t ⋯ wk ⋯ (σ ,ₛ e) ⟧
  by subst (λ ■ → e ∈𝕍⟦ ■ ⟧) (sym (wk-cancels-,ₛ t σ e)) (
    e ∈𝕍⟦ t ⋯ σ ⟧
  by e∈))
_,𝔾_ {µ} {e} {t} {σ} {Γ} e∈ σ∈ (there x) =
    σ 𝕖 x ∈𝕍⟦ wk-telescope (Γ ▶ t) (there x) ⋯ (σ ,ₛ e) ⟧
  by (
    σ 𝕖 x ∈𝕍⟦ wk-telescope Γ x ⋯ wk ⋯ (σ ,ₛ e) ⟧
  by subst (λ ■ → σ 𝕖 x ∈𝕍⟦ ■ ⟧) (sym (wk-cancels-,ₛ (wk-telescope Γ x) σ e)) (
    σ 𝕖 x ∈𝕍⟦ wk-telescope Γ x ⋯ σ ⟧
  by σ∈ x))

-- data _∈𝔾⟦_⟧ : ∀ {µ} → µ →ₛ [] → Ctx µ → Set where
--   [] : idₛ ∈𝔾⟦ ∅ ⟧
--   _∷_ : {σ : µ →ₛ []} {Γ : Ctx µ} {v : [] ⊢ 𝕖} {t : µ ⊢ 𝕥} →
--     v        ∈𝕍⟦ t ⋯ σ  ⟧ →
--     σ        ∈𝔾⟦ Γ      ⟧ →
--     (σ ,ₛ v) ∈𝔾⟦ _,,_ {m = 𝕖} Γ t ⟧

_⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
Γ ⊧ e ∶ t = ∀ σ → σ ∈𝔾⟦ Γ ⟧ → (e ⋯ σ) ∈𝔼⟦ t ⋯ σ ⟧

-- Decidability of Value -------------------------------------------------------

Value? : ∀ (e : [] ⊢ 𝕖) → Dec (Value e)
Value? (λx e)    = yes λxe
Value? (e₁ · e₂) = no λ()

-- unused
Value→Irred : Value e → Irred e
Value→Irred λxe = λ()

-- Decidability of Irred -------------------------------------------------------

cbv-·₁ :
  ¬ Red e₁ →
  ¬ Value e₁ →
  ¬ Red (e₁ · e₂)
cbv-·₁ ¬red-e₁ ¬val-e₁ (_ , β-λ val-e₂) = ¬val-e₁ λxe
cbv-·₁ ¬red-e₁ ¬val-e₁ (_ , ξ-·₁ e₁↪e₁') = ¬red-e₁ (_ , e₁↪e₁')
cbv-·₁ ¬red-e₁ ¬val-e₁ (_ , ξ-·₂ val-e₁ e₂↪e₂') = ¬val-e₁ val-e₁

cbv-·₂ :
  ¬ Red e₁ →
  ¬ Red e₂ →
  ¬ Value e₂ →
  ¬ Red (e₁ · e₂)
cbv-·₂ ¬red-e₁ ¬red-e₂ ¬val-e₂ (_ , β-λ val-e₂) = ¬val-e₂ val-e₂
cbv-·₂ ¬red-e₁ ¬red-e₂ ¬val-e₂ (_ , ξ-·₁ e₁↪e₁') = ¬red-e₁ (_ , e₁↪e₁')
cbv-·₂ ¬red-e₁ ¬red-e₂ ¬val-e₂ (_ , ξ-·₂ val-e₁ e₂↪e₂') = ¬red-e₂ (_ , e₂↪e₂')

Red? : ∀ (e : [] ⊢ 𝕖) → Dec (Red e)
Red? (λx e) = no λ { () }
Red? (e₁ · e₂) with Red? e₁            | Red? e₂
Red? (e₁ · e₂)    | yes (e₁' , e₁↪e₁') | _                  = yes (e₁' · e₂ , ξ-·₁ e₁↪e₁')
Red? (e₁ · e₂)    | no ¬Red-e₁         | yes (e₂' , e₂↪e₂') with Value? e₁
Red? (e₁ · e₂)    | no ¬Red-e₁         | yes (e₂' , e₂↪e₂') | no ¬val-e₁ = no (cbv-·₁ ¬Red-e₁ ¬val-e₁)
Red? (e₁ · e₂)    | no ¬Red-e₁         | yes (e₂' , e₂↪e₂') | yes val-e₁ = yes (e₁ · e₂' , ξ-·₂ val-e₁ e₂↪e₂')
Red? (e₁ · e₂)    | no ¬Red-e₁         | no ¬Red-e₂         with Value? e₁
Red? (e₁ · e₂)    | no ¬Red-e₁         | no ¬Red-e₂         | no ¬val-e₁ = no (cbv-·₁ ¬Red-e₁ ¬val-e₁)
Red? (.(λx _) · e₂) | no ¬Red-e₁       | no ¬Red-e₂         | yes λxe with Value? e₂
Red? (.(λx _) · e₂) | no ¬Red-e₁       | no ¬Red-e₂         | yes λxe | no ¬val-e₂ = no (cbv-·₂ ¬Red-e₁ ¬Red-e₂ ¬val-e₂)
Red? (.(λx _) · e₂) | no ¬Red-e₁       | no ¬Red-e₂         | yes λxe | yes val-e₂ = yes (_ , (β-λ val-e₂))

Irred? : ∀ (e : [] ⊢ 𝕖) → Dec (Irred e)
Irred? e with Red? e
... | yes red  = no (λ ¬red → ¬red red)
... | no irred = yes irred

-- Final Result ----------------------------------------------------------------

𝕍→Value : e ∈𝕍⟦ t ⟧ → Value e
𝕍→Value {λx e} {t₁ ⇒ t₂} e∈𝕍⟦t⟧ = λxe

value-↪* :
  Value e →
  e ↪* e' →
  e' ≡ e
value-↪* val-e ↪*-refl = refl
value-↪* val-e (↪*-step e↪e' e'↪*e'') = ⊥-elim (Value→Irred val-e (_ , e↪e'))

𝕍→𝔼 : e ∈𝕍⟦ t ⟧ → e ∈𝔼⟦ t ⟧
𝕍→𝔼 ∈𝕍 e↪*e' irred-e' with value-↪* (𝕍→Value ∈𝕍 ) e↪*e'
... | refl = ∈𝕍

-- inv-·↪* :
--   e₁ · e₂ ↪* e →
--   Irred e →
--   ∃[ e₁' ] e₁ ↪* e₁' × Irred e₁
-- inv-·↪* ↪*-refl irred = (_ , ↪*-refl , λ red-e₁ → irred (_ , (ξ-·₁ (proj₂ red-e₁))))
-- inv-·↪* (↪*-step ·↪e' e'↪*e'') irred = {!!}

-- inv-·↪* :
--   e₁ · e₂ ↪* e →
--   Irred e →
--   (∃[ e₁' ] e₁ ↪* e₁' × Irred e₁) × 
--   (∃[ e₂' ] e₂ ↪* e₂' × Irred e₂)
-- inv-·↪* ↪*-refl irred = (_ , ↪*-refl , λ red-e₁ → irred (_ , (ξ-·₁ (proj₂ red-e₁))))
--                       , (_ , ↪*-refl , λ red-e₂ → irred (_ , (ξ-·₂ {!!} (proj₂ red-e₂))))
-- inv-·↪* (↪*-step x p) irred = {!!}

-- -- seems way too strong
-- inv-·↪* :
--   e₁ · e₂ ↪* e →
--   Irred e →
--   ∅ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--   ∅ ⊢ e₂ ∶ t₁ →
--   ∃[ e₁' ] ∃[ e₂' ]
--     e₁ ↪* λx e₁' ×
--     e₂ ↪* e₂' ×
--     Irred e₂ ×
--     e₁' ⋯ ⦅ e₂' ⦆ ↪* e
-- inv-·↪* ↪*-refl       irred ⊢e₁ ⊢e₂ = ⊥-elim (irred {!ξ-·₁!})
-- -- inv-·↪* ↪*-refl       irred ⊢e₁ ⊢e₂ = _ , _ , {!!} , {!!} , {!!} , {!!} -- ↪*-refl , λ red-e₁ → irred (_ , (ξ-·₁ (proj₂ red-e₁)))
-- inv-·↪* (↪*-step x p) irred ⊢e₁ ⊢e₂ = {!!}

lemy :
  ∅ ⊢ e₁ ∶ t₁ ⇒ t₂ →
  ∅ ⊢ e₂ ∶ t₁ →
  e₁ ∈𝔼⟦ t₁ ⇒ t₂ ⟧ →
  e₂ ∈𝔼⟦ t₁ ⟧ →
  e₁ · e₂ ↪ e' →
  Irred e' →
  e' ∈𝕍⟦ t₂ ⟧
lemy = {!!}

lemx :
  ∅ ⊢ e₁ ∶ t₁ ⇒ t₂ →
  ∅ ⊢ e₂ ∶ t₁ →
  e₁ ∈𝔼⟦ t₁ ⇒ t₂ ⟧ →
  e₂ ∈𝔼⟦ t₁ ⟧ →
  e₁ · e₂ ↪* e' →
  Irred e' →
  e' ∈𝕍⟦ t₂ ⟧
lemx ⊢e₁ ⊢e₂ e₁∈𝔼 e₂∈𝔼 ↪*-refl irred-e' with progress (τ-· ⊢e₁ ⊢e₂)
... | inj₂ red-[e₁·e₂] = irred-e' red-[e₁·e₂]
lemx ⊢e₁ ⊢e₂ e₁∈𝔼 e₂∈𝔼 (↪*-step [e₁·e₂]↪e' e'↪*e'') irred-e' = lemx {!subject-reduction (τ-· ⊢e₁ ⊢e₂) [e₁·e₂]↪e'!} {!!} {!!} {!!} {!!} {!!}

-- Fundamental Property
⊢→⊧ : ∀ {Γ : Ctx µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
  Γ ⊢ e ∶ t →
  Γ ⊧ e ∶ t

⊢→⊧ {µ} {Γ} {` x} {t} (τ-` refl) =
    Γ ⊧ ` x ∶ t
  by λ σ σ∈𝔾⟦Γ⟧ →
    σ 𝕖 x ∈𝔼⟦ wk-telescope Γ x ⋯ σ ⟧
  by 𝕍→𝔼 (
    σ 𝕖 x ∈𝕍⟦ wk-telescope Γ x ⋯ σ ⟧
  by σ∈𝔾⟦Γ⟧ x)

⊢→⊧ {µ} {Γ} {λx e} {t₁ ⇒ t₂} (τ-λ ⊢e) =
    Γ ⊧ λx e ∶ t₁ ⇒ t₂
  by λ σ σ∈𝔾⟦Γ⟧ →
    λx (e ⋯ σ ↑ₛ 𝕖) ∈𝔼⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧
  by 𝕍→𝔼 (
    λx (e ⋯ σ ↑ₛ 𝕖) ∈𝕍⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧
  by λ v v∈𝕍⟦t₁⋯σ⟧ →
    e ⋯ σ ↑ₛ 𝕖 ⋯ ⦅ v ⦆ ∈𝔼⟦ t₂ ⋯ σ ⟧
  by subst₂ _∈𝔼⟦_⟧ (sym (⋯↑⋯⦅⦆-is-⋯,ₛ e v σ)) (wk-cancels-,ₛ t₂ σ v)
    (e ⋯ (σ ,ₛ v) ∈𝔼⟦ t₂ ⋯ wk ⋯ (σ ,ₛ v) ⟧
  by ⊢→⊧ ⊢e (σ ,ₛ v) (
    σ ,ₛ v ∈𝔾⟦ Γ ▶ t₁ ⟧
  by v∈𝕍⟦t₁⋯σ⟧ ,𝔾 σ∈𝔾⟦Γ⟧)))

⊢→⊧ {µ} {Γ} {e₁ · e₂} {t₂}  (τ-· {t₁ = t₁} ⊢e₁ ⊢e₂) =
    Γ ⊧ e₁ · e₂ ∶ t₂
  by λ σ σ∈𝔾⟦Γ⟧ →
    (e₁ ⋯ σ) · (e₂ ⋯ σ) ∈𝔼⟦ t₂ ⋯ σ ⟧
  by λ {e'} [e₁·e₂]σ↪*e' irred-e' →
    e' ∈𝕍⟦ t₂ ⋯ σ ⟧
  by
    -- let p = e₁ ⋯ σ ∈𝔼⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧ by ⊢→⊧ ⊢e₁ σ σ∈𝔾⟦Γ⟧ in
    -- let q = e₂ ⋯ σ ∈𝔼⟦ (t₁ ⋯ σ) ⟧            by ⊢→⊧ ⊢e₂ σ σ∈𝔾⟦Γ⟧ in
    {!!}
    -- lemx (sub-pres-⊢ ⊢e₁ {!!}) (sub-pres-⊢ ⊢e₂ {!!}) (⊢→⊧ ⊢e₁ σ σ∈𝔾⟦Γ⟧) (⊢→⊧ ⊢e₂ σ σ∈𝔾⟦Γ⟧) [e₁·e₂]σ↪*e' irred-e'


 -- e₁ ⋯ σ ∈𝔼⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧  
 -- e₂ ⋯ σ ∈𝔼⟦ (t₁ ⋯ σ) ⟧
 -- ––––––––––––––––––––––––––––––––
 -- (e₁ ⋯ σ) · (e₂ ⋯ σ) ∈𝔼⟦ t₂ ⋯ σ ⟧

 -- ∀ {e'} → e₁ ⋯ σ ↪* e' → Irred e' → e' ∈𝕍⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧  = (e' ≡ λx e) × (∀ v → v ∈𝕍⟦ t₁ ⋯ σ ⟧ → (e ⋯ ⦅ v ⦆) ∈𝔼⟦ t₂ ⋯ σ ⟧)
 -- ∀ {e'} → e₂ ⋯ σ ↪* e' → Irred e' → e' ∈𝕍⟦ (t₁ ⋯ σ) ⟧
 -- –––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
 -- ∀ {e'} → (e₁ ⋯ σ) · (e₂ ⋯ σ) ↪* e' → Irred e' → e' ∈𝕍⟦ (t₂ ⋯ σ) ⟧


⊧→safe :
  ∅ ⊧ e ∶ t →
  Safe e
⊧→safe {e = e} {t = t} ⊧e e′ e↪*e′ with Red? e′
... | yes red-e′                  = inj₂ red-e′
... | no irred-e′ rewrite ⋯-idₛ e = inj₁
  let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e idₛ idₛ∈𝔾⟦∅⟧ in
  let e∈𝔼⟦t⟧ = subst₂ _∈𝔼⟦_⟧ (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
  let e′∈𝕍⟦t⟧ = e∈𝔼⟦t⟧ e↪*e′ irred-e′ in
  𝕍→Value e′∈𝕍⟦t⟧

safety :
  ∅ ⊢ e ∶ t →
  Safe e
safety {e = e} {t = t} ⊢e =
  ⊧→safe {e = e} {t = t} (⊢→⊧ ⊢e)

-- before generalization from ∅ to Γ:

-- ⊢→⊧ :
--   ∅ ⊢ e ∶ t →
--   e ∈𝔼⟦ t ⟧
-- ⊢→⊧ = {!!}

-- ⊧→safe :
--   e ∈𝔼⟦ t ⟧ →
--   Safe e
-- ⊧→safe ⊧e = {!!}

-- safety :
--   ∅ ⊢ e ∶ t →
--   Safe e
-- safety ⊢e = ⊧→safe (⊢→⊧ ⊢e)
