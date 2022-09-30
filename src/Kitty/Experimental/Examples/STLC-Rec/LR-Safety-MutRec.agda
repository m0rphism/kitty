module Kitty.Experimental.Examples.STLC-Rec.LR-Safety where

open import Kitty.Experimental.Examples.STLC-Rec.Definitions hiding (_,_)
open import Kitty.Experimental.Examples.STLC-Rec.SubjectReduction

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction using (<-rec; <-wellFounded)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-step)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax; ∃-syntax) renaming (proj₁ to π₁; proj₂ to π₂) 
open import Data.Unit.Polymorphic
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
RelTy = ∀ {µ} → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set


-- Field accessors for the R𝕍 and R𝔼 components of the induction hypothesis.
R𝕍< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → A)
R𝕍< ih j j<k = π₁ (ih j j<k)
R𝔼< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → B)
R𝔼< ih j j<k = π₂ (ih j j<k)

R𝕍 R𝔼 : ∀ (k : Gas) → WfRec _<_ (λ _ → RelTy × RelTy) k → RelTy
R𝕍 k ih _        (`[ p ] x) = ⊥
R𝕍 k ih (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
                              (j≤k : j ≤ k) →
                              R𝕍 j (wk-ih j≤k ih) v t₁ →
                              R𝔼 j (wk-ih j≤k ih) (e ⋯ ⦅ v ⦆) t₂
R𝕍 k ih _        (t₁ ⇒ t₂)  = ⊥
R𝕍 k ih _        𝟘          = ⊥
R𝕍 k ih (fold v) (µα t)     = ∀ {j} →
                              (j<k : j < k) →
                              R𝕍< ih j j<k v (t ⋯ ⦅ µα t ⦆)
R𝕍 k ih _        (µα t)     = ⊥
R𝔼 k ih e        t          = ∀ {j e'} →
                              (j<k : j < k) →
                              e ↪^[ j ] e' × (Irred e' → R𝕍 (k ∸ j) (wk-ih (k∸j≤k k j) ih) e' t)

R : ∀ (k : Gas) →
  WfRec _<_ (λ _ → RelTy × RelTy) k →
  RelTy × RelTy
R k ih = R𝕍 k ih , R𝔼 k ih

infix 3 _∈𝕍_⟦_⟧  _∈𝔼_⟦_⟧

_∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : ∀ {µ} → µ ⊢ 𝕖 → Gas → µ ∶⊢ 𝕖 → Set
v ∈𝕍 k ⟦ t ⟧ = π₁ (<-rec _ R k) v t
e ∈𝔼 k ⟦ t ⟧ = π₂ (<-rec _ R k) e t

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

infixr 0 _by_
_by_ : ∀ {ℓ} (A : Set ℓ) → A → A
A by a = a

monotonicity : 
  ∀ k µ (v : µ ⊢ 𝕖) (t : µ ⊢ 𝕥) j →
  v ∈𝕍 k ⟦ t ⟧ →
  j ≤ k →
  v ∈𝕍 j ⟦ t ⟧
monotonicity = <-rec _ λ where
  k ih µ (λx v)   (t₁ ⇒ t₂) j     v∈𝕍 j≤k → λ j₁≤j v₁∈𝕍⟦t₁⟧ j₂<j₁ → {!j≤sk!} , λ irred-e' → {!!}
  k ih µ (fold v) (µα t)    j     v∈𝕍 j≤k →
    fold v ∈𝕍 j ⟦ µα t ⟧          by λ {j = i} i<j →
      -- let x = v ∈𝕍 i ⟦ t ⋯ S.⦅ µα t ⦆ ⟧  by  ih j {!j≤k!} µ v (t ⋯ ⦅ µα t ⦆) i {!v∈𝕍 i!} {!i≤j!} in
      let i<k = i < k by ≤-trans i<j j≤k in
      let y = v∈𝕍 i<k in
      let x = v ∈𝕍 i ⟦ t ⋯ S.⦅ µα t ⦆ ⟧  by  ih i i<k µ v (t ⋯ ⦅ µα t ⦆) i {!v∈𝕍 i<k!} ≤-refl in
      {! v∈𝕍 i<k!}
-- monotonicity = <-rec _ λ where
--   -- {!ih _ j<k µ v (t ⋯ ⦅ µα t ⦆) _ ? ?!}
--   zero    ih µ (λx v)   (t₁ ⇒ t₂) .zero v∈𝕍 z≤n → λ { z≤n x () }
--   zero    ih µ (fold v) (µα t)    .zero v∈𝕍 z≤n → λ ()
--   (suc k) ih µ (λx v)   (t₁ ⇒ t₂) j     v∈𝕍 j≤sk → λ j₁≤j v₁∈𝕍⟦t₁⟧ j₂<j₁ → {!j≤sk!} , λ irred-e' → {!!}
--   (suc k) ih µ (fold v) (µα t)    j     v∈𝕍 j≤sk →
--     fold v ∈𝕍 j ⟦ µα t ⟧          by λ {j = i} i<j →
--       -- let x = v ∈𝕍 i ⟦ t ⋯ S.⦅ µα t ⦆ ⟧  by  ih j {!j≤sk!} µ v (t ⋯ ⦅ µα t ⦆) i {!v∈𝕍 i!} {!i≤j!} in
--       let x = v ∈𝕍 i ⟦ t ⋯ S.⦅ µα t ⦆ ⟧  by  ih j {!j≤sk!} µ v (t ⋯ ⦅ µα t ⦆) i {!v∈𝕍 i!} {!i≤j!} in
--       {! x!}
--   -- (suc k) ih µ (fold v) (µα t)    zero  v∈𝕍 j≤k →
--   --   fold v ∈𝕍 0 ⟦ µα t ⟧          by λ
--   --     {
--   --       {j = zero} i<j →
--   --         {!v ∈𝕍 0 ⟦ t ⋯ ⦅ µα t ⦆ ⟧    by ?!}
--   --     ; {j = suc i} i<j →
--   --         {!v ∈𝕍 suc i ⟦ t ⋯ ⦅ µα t ⦆ ⟧    by ?!}
--   --     }
--   -- -- (suc k) ih µ (fold v) (µα t)    zero  v∈𝕍 j≤k →
--   -- --   fold v ∈𝕍 0 ⟦ µα t ⟧          by λ { {j = i} i<j →
--   -- --       {!v ∈𝕍 i ⟦ t ⋯ ⦅ µα t ⦆ ⟧    by ?!}
--   -- --     }
--   -- (suc k) ih µ (fold v) (µα t)    (suc j) v∈𝕍 j≤k →
--   --   fold v ∈𝕍 suc j ⟦ µα t ⟧          by λ { {j = i} i<j →
--   --       {!v ∈𝕍 i ⟦ t ⋯ ⦅ µα t ⦆ ⟧    by ?!}
--   --     }
--   -- -- (suc k) ih µ (fold v) (µα t)    j     v∈𝕍 j≤k →
--   -- --   fold v ∈𝕍 j ⟦ µα t ⟧          by λ {j = i} i<j →
--   -- --       {!v ∈𝕍 i ⟦ t ⋯ ⦅ µα t ⦆ ⟧    by ?!}
--   -- -- k ih v t j v∈𝕍 j≤k → {!!}

-- R𝕍 k ih (fold v) (µα t)     = ∀ {j} →
--                               (j<k : j < k) →
--                               R𝕍< ih j j<k v (t ⋯ ⦅ µα t ⦆)

-- ih  : (y : ℕ) →
--       y < k →
--       {v = v₁ : µ ⊢ 𝕖} {t = t₁ : µ ⊢ 𝕥} {j = j₁ : ℕ} →
--       v₁ ∈𝕍 y ⟦ t₁ ⟧ → j₁ ≤ y → v₁ ∈𝕍 j₁ ⟦ t₁ ⟧

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
