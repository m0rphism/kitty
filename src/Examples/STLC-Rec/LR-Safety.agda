module Examples.STLC-Rec.LR-Safety where

open import Examples.STLC-Rec.Definitions hiding (_,_)
open import Examples.STLC-Rec.SubjectReduction

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction using (<-rec; <-wellFounded)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-step)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax; ∃-syntax) renaming (proj₁ to π₁; proj₂ to π₂) 
open import Data.Unit.Polymorphic
open import Function using (_$_)
open import Induction
open import Induction.WellFounded as WF using (WfRec)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_)

-- Lemmas ----------------------------------------------------------------------

wk-ih : ∀ {ℓ j k} {P : ℕ → Set ℓ} →
  j ≤ k →
  WfRec _<_ P k →
  WfRec _<_ P j
wk-ih j≤k ih i i<j = ih i (≤-trans i<j j≤k)

k∸j≤k : ∀ k j → k ∸ j ≤ k
k∸j≤k k       zero    = ≤-refl
k∸j≤k zero    (suc j) = ≤-refl
k∸j≤k (suc k) (suc j) = ≤-trans (k∸j≤k k j) (≤-step ≤-refl)

-- TODO: Move to library
module FixPoint-FunExt
  {ℓ ℓ' r : Level}
  {A : Set ℓ'}
  {_<_ : A → A → Set r} (wf : WF.WellFounded _<_)
  (P : A → Set ℓ) (f : ∀ x → WF.WfRec _<_ P x → P x)
  where

  open import Axiom.Extensionality.Propositional renaming (Extensionality to FunExt)

  postulate fun-ext : ∀ {ℓ₁ ℓ₂} → FunExt ℓ₁ ℓ₂

  open WF.FixPoint wf P f
    (λ x IH≡IH′ → cong (f x) $ fun-ext λ y → fun-ext λ y<x → IH≡IH′ y<x)
    public

  unfold-wfRec' : ∀ {x} → WF.All.wfRec wf ℓ P f x ≡ f x (λ y _ → WF.All.wfRec wf ℓ P f y)
  unfold-wfRec' = unfold-wfRec

-- Formalization ---------------------------------------------------------------

Gas : Set
Gas = ℕ

variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ
  k k₁ k₂ k₃ k' k₁' k₂' k₃' : Gas
  j j₁ j₂ j₃ j' j₁' j₂' j₃' : Gas
  i i₁ i₂ i₃ i' i₁' i₂' i₃' : Gas

data _↪^[_]_ : µ ⊢ 𝕖 → Gas → µ ⊢ 𝕖 → Set where
  ↪-refl : e ↪^[ zero ] e
  ↪-step : e₁ ↪ e₂ → e₂ ↪^[ k ] e₃ → e₁ ↪^[ suc k ] e₃

↪^-trans : e₁ ↪^[ k ] e₂ → e₂ ↪^[ k' ] e₃ → e₁ ↪^[ k + k' ] e₃
↪^-trans ↪-refl q = q
↪^-trans (↪-step s p) q = ↪-step s (↪^-trans p q)

-- ↪^→↪* : e₁ ↪^[ k ] e₂ → e₁ ↪* e₂
-- ↪^→↪* p = ?

-- ↪*→↪^ : e₁ ↪* e₂ → ∃[ k ] (e₁ ↪^[ k ] e₂)
-- ↪*→↪^ p = ?

Irred : µ ⊢ 𝕖 → Set
Irred e = ∀ e' → ¬ (e ↪ e')

-- Type of the `_∈𝕍_⟦_⟧` and `_∈𝔼_⟦_⟧` relations, but without the `Gas`-parameter.
RelTy : Set₁
RelTy = ∀ µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set


-- Field accessors for the R𝕍 and R𝔼 components of the induction hypothesis.
R𝕍< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → A)
R𝕍< ih j j<k = π₁ (ih j j<k)
R𝔼< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → B)
R𝔼< ih j j<k = π₂ (ih j j<k)

R𝕍 R𝔼 : ∀ (k : Gas) → (∀ j → j < k → RelTy × RelTy) → RelTy
R𝕍 k ih µ _        (`[ p ] x) = ⊥
R𝕍 k ih µ (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
                              (j≤k : j ≤ k) →
                              R𝕍 j (wk-ih j≤k ih) µ v t₁ →
                              R𝔼 j (wk-ih j≤k ih) µ (e ⋯ ⦅ v ⦆) t₂
R𝕍 k ih µ _        (t₁ ⇒ t₂)  = ⊥
R𝕍 k ih µ _        𝟘          = ⊥
R𝕍 k ih µ (fold v) (µα t)     = ∀ {j} →
                              (j<k : j < k) →
                              R𝕍< ih j j<k µ v (t ⋯ ⦅ µα t ⦆)
R𝕍 k ih µ _        (µα t)     = ⊥
R𝔼 k ih µ e        t          = ∀ {j e'} →
                              (j<k : j < k) →
                              e ↪^[ j ] e' →
                              Irred e' →
                              R𝕍 (k ∸ j) (wk-ih (k∸j≤k k j) ih) µ e' t

R : ∀ (k : Gas) →
  (∀ j → j < k → RelTy × RelTy) →
  RelTy × RelTy
R k ih = R𝕍 k ih , R𝔼 k ih

infix 3 _∈𝕍_⟦_⟧  _∈𝔼_⟦_⟧  _∈𝔾_⟦_⟧  _⊧_∶_

∈𝕍𝔼 : Gas → RelTy × RelTy
∈𝕍𝔼 = <-rec _ R

_∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : ∀ {µ} → µ ⊢ 𝕖 → Gas → µ ∶⊢ 𝕖 → Set
v ∈𝕍 k ⟦ t ⟧ = π₁ (∈𝕍𝔼 k) _ v t
e ∈𝔼 k ⟦ t ⟧ = π₂ (∈𝕍𝔼 k) _ e t

data _∈𝔾_⟦_⟧ : ∀ {µ₁ µ₂} → µ₁ →ₛ µ₂ → Gas → Ctx µ₁ → Set where
  [] : idₛ ∈𝔾 k ⟦ ∅ ⟧
  _∷_ : {σ : µ₁ →ₛ µ₂} {k : Gas} {Γ : Ctx µ₁} {v : µ₂ ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} →
    v        ∈𝕍 k ⟦ t ⋯ σ  ⟧ →
    σ        ∈𝔾 k ⟦ Γ      ⟧ →
    (σ ,ₛ v) ∈𝔾 k ⟦ Γ ,, t ⟧

_⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
Γ ⊧ e ∶ t = ∀ {k σ} →
  σ       ∈𝔾 k ⟦ Γ ⟧ →
  (e ⋯ σ) ∈𝔼 k ⟦ t ⟧

module Unfold-𝕍-𝔼 where

  open import Induction.WellFounded using (module FixPoint)
  open import Data.Nat.Induction using (<-wellFounded; <-rec)

  open FixPoint-FunExt <-wellFounded (λ _ → RelTy × RelTy) R
    renaming (unfold-wfRec to unfold-∈𝕍𝔼'-≡) public

  unfold-∈𝕍𝔼-≡ : {k : Gas} → ∈𝕍𝔼 k ≡ R k (λ j j<k → ∈𝕍𝔼 j)
  unfold-∈𝕍𝔼-≡ = unfold-∈𝕍𝔼'-≡

  unfold-∈𝕍'-≡ : ∀ {k : Gas} → π₁ (∈𝕍𝔼 k) ≡ π₁ (R k (λ j j<k → ∈𝕍𝔼 j))
  unfold-∈𝕍'-≡ = cong π₁ unfold-∈𝕍𝔼-≡

  unfold-∈𝕍-≡ : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    (e ∈𝕍 k ⟦ t ⟧) ≡ R𝕍 k (λ j j<k → ∈𝕍𝔼 j) µ e t
  unfold-∈𝕍-≡ {k = k} rewrite unfold-∈𝕍'-≡ {k} = refl

  fold-∈𝕍 : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    R𝕍 k (λ j j<k → ∈𝕍𝔼 j) µ e t → (e ∈𝕍 k ⟦ t ⟧)
  fold-∈𝕍 p = subst (λ x → x) (sym unfold-∈𝕍-≡) p

  unfold-∈𝕍 : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    (e ∈𝕍 k ⟦ t ⟧) → R𝕍 k (λ j j<k → ∈𝕍𝔼 j) µ e t
  unfold-∈𝕍 p = subst (λ x → x) unfold-∈𝕍-≡ p

  unfold-∈𝔼'-≡ : ∀ {k : Gas} → π₂ (∈𝕍𝔼 k) ≡ π₂ (R k (λ j j<k → ∈𝕍𝔼 j))
  unfold-∈𝔼'-≡ = cong π₂ unfold-∈𝕍𝔼-≡

  unfold-∈𝔼-≡ : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    (e ∈𝔼 k ⟦ t ⟧) ≡ R𝔼 k (λ j j<k → ∈𝕍𝔼 j) µ e t
  -- unfold-𝔼 {k = k} rewrite unfold-𝔼'-≡ {k} = {!refl!}
  unfold-∈𝔼-≡ {k = k} = {!!}

  fold-∈𝔼 : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    R𝔼 k (λ j j<k → ∈𝕍𝔼 j) µ e t → (e ∈𝔼 k ⟦ t ⟧)
  fold-∈𝔼 p = subst (λ x → x) (sym unfold-∈𝔼-≡) p

  unfold-∈𝔼 : ∀ {k : Gas} {µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} →
    (e ∈𝔼 k ⟦ t ⟧) → R𝔼 k (λ j j<k → ∈𝕍𝔼 j) µ e t
  unfold-∈𝔼 p = subst (λ x → x) unfold-∈𝔼-≡ p


open Unfold-𝕍-𝔼

infixr 0 _by_
_by_ : ∀ {ℓ} (A : Set ℓ) → A → A
A by a = a

Monotonicity-𝕍 : Gas → Set
Monotonicity-𝕍 k = (µ : List Modeᵥ) (v : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) (j : ℕ) → v ∈𝕍 k ⟦ t ⟧ → j ≤ k → v ∈𝕍 j ⟦ t ⟧

Monotonicity-𝔼 : Gas → Set
Monotonicity-𝔼 k = (µ : List Modeᵥ) (e : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) (j : ℕ) → e ∈𝔼 k ⟦ t ⟧ → j ≤ k → e ∈𝔼 j ⟦ t ⟧

Monotonicity : Gas → Set
Monotonicity k = Monotonicity-𝕍 k × Monotonicity-𝔼 k

MM : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity k
MM k ih = MM-𝕍 k ih , MM-𝔼 k ih
  where

  MM-𝕍 : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity-𝕍 k
  MM-𝕍 k ih µ (λx e)   (t₁ ⇒ t₂) j λxe∈𝕍k[t₁⇒t₂] j≤k =
    (λx e) ∈𝕍 j ⟦ t₁ ⇒ t₂ ⟧
      by fold-∈𝕍 {e = λx e} {t = t₁ ⇒ t₂} (
    (∀ {i v} → (i≤j : i ≤ j) → R𝕍 i (λ j j<k → ∈𝕍𝔼 j) µ v t₁ → R𝔼 i (λ j j<k → ∈𝕍𝔼 j) µ (e ⋯ ⦅ v ⦆) t₂)
      by λ {i} {v} i≤j R𝕍-v →
    R𝔼 i (λ j j<k → ∈𝕍𝔼 j) µ (e ⋯ ⦅ v ⦆) t₂
      -- by
      --   {! MM-𝕍 k ih!}
      --   {! (λxe∈𝕍k[t₁⇒t₂] {i} {!i<k!} (≤-trans i<j j≤k))!}
      by unfold-∈𝔼 (
    e ⋯ ⦅ v ⦆ ∈𝔼 i ⟦ t₂ ⟧
      by {!MM-𝔼 k ih µ (e ⋯ ⦅ v ⦆) t₂ i!}
      -- by {!λxe∈𝕍k[t₁⇒t₂] {i} {!i<k!} ?!}
    )
      -- by λ {i} {v} i≤j R𝕍-v {i'} {e'} i'<i → {!!} , (λ irred-e' → {!ih (i ∸ i') _ µ e' t₂ !})
    )
  MM-𝕍 k ih µ (fold v) (µα t)    j v∈V j≤k =
    fold v ∈𝕍 j ⟦ µα t ⟧          by
    fold v ∈𝕍 j ⟦ µα t ⟧          by {!!}

  -- R𝕍 k ih µ (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
  --                               (j≤k : j ≤ k) →
  --                               R𝕍 j (wk-ih j≤k ih) µ v t₁ →
  --                               R𝔼 j (wk-ih j≤k ih) µ (e ⋯ ⦅ v ⦆) t₂

  MM-𝔼 : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity-𝔼 k
  MM-𝔼 k ih µ e t j e∈k[t] j≤k =
    e ∈𝔼 j ⟦ t ⟧
      by fold-∈𝔼 (
    (∀ {i} {e'} → i < j → e ↪^[ i ] e' → Irred e' → R𝕍 (j ∸ i) (wk-ih (k∸j≤k j i) (λ j' j'<k → ∈𝕍𝔼 j')) µ e' t)
      by λ {i} {e'} i<j e↪[i]e' irred-e' →
    R𝕍 (j ∸ i) (wk-ih (k∸j≤k j i) (λ j' j'<k → ∈𝕍𝔼 j')) µ e' t
      by unfold-∈𝕍 (
    e' ∈𝕍 j ∸ i ⟦ t ⟧
      by
        let i<k = ≤-trans i<j j≤k in
        let R𝕍[k-i]e' = e∈k[t] {i} {e'} i<k e↪[i]e' irred-e' in
        -- let e'∈𝕍k∸i[t] = R𝕍[k-i]e' in
        -- let e'∈𝕍j∸i[t] = π₁ (ih (k ∸ i) {!!}) µ e' t (j ∸ i) {!!} {!!} in
        let e'∈𝕍j∸i[t] = π₁ (ih i i<k) µ e' t (j ∸ i) {!!} {!!} in
        {!fold-∈𝕍 R𝕍[k-i]e'!}
    )
    )

monotonicity : 
  ∀ k → Monotonicity k
monotonicity = <-rec _ MM

monotonicity-𝕍 : 
  ∀ k µ (v : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) j →
  v ∈𝕍 k ⟦ t ⟧ →
  j ≤ k →
  v ∈𝕍 j ⟦ t ⟧
monotonicity-𝕍 = {!!}

-- RecTy : Gas → Set
-- RecTy k = (µ : List Modeᵥ) (v : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) (j : ℕ) → v ∈𝕍 k ⟦ t ⟧ → j ≤ k → v ∈𝕍 j ⟦ t ⟧

-- MM : ∀ k → (∀ j → j < k → RecTy j) → RecTy k
-- -- MM : ∀ k → WfRec _<_ RecTy k → RecTy k
-- MM k ih µ (λx e)   (t₁ ⇒ t₂) j v∈V j≤k =
--   (λx e) ∈𝕍 j ⟦ t₁ ⇒ t₂ ⟧
--     by fold-∈𝕍 {e = λx e} {t = t₁ ⇒ t₂} (
--   (∀ {i v} → (i≤j : i ≤ j) → R𝕍 i (λ j j<k → ∈𝕍𝔼 j) µ v t₁ → R𝔼 i (λ j j<k → ∈𝕍𝔼 j) µ (e ⋯ ⦅ v ⦆) t₂)
--     -- by λ {i} {v} i≤j R𝕍-v → {!!}
--     by λ {i} {v} i≤j R𝕍-v {i'} {e'} i'<i → {!!} , (λ irred-e' → {!ih (i ∸ i') _ µ e' t₂ !})
--   )
-- MM k ih µ (fold v) (µα t)    j v∈V j≤k =
--   fold v ∈𝕍 j ⟦ µα t ⟧          by
--   fold v ∈𝕍 j ⟦ µα t ⟧          by {!!}

-- -- R𝕍 k ih µ (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
-- --                               (j≤k : j ≤ k) →
-- --                               R𝕍 j (wk-ih j≤k ih) µ v t₁ →
-- --                               R𝔼 j (wk-ih j≤k ih) µ (e ⋯ ⦅ v ⦆) t₂

-- monotonicity : 
--   ∀ k µ (v : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) j →
--   v ∈𝕍 k ⟦ t ⟧ →
--   j ≤ k →
--   v ∈𝕍 j ⟦ t ⟧
-- monotonicity = <-rec _ MM

-- Fundamental Property
⊢→⊧ :
  Γ ⊢ e ∶ t →
  Γ ⊧ e ∶ t
⊢→⊧ ⊢e = {!!}

-- ⊧→safe :
--   Γ ⊧ e ∶ t →
--   safe
-- ⊧→⊢ ⊧e = {!!}

-- -- mutual      
-- --   𝕍→Value : e ∈𝕍⟦ t ⟧ k → Value e
-- --   𝕍→Value = {!!}
