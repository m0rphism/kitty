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
open import Function using (_$_)
open import Induction
open import Induction.WellFounded as WF using (WfRec)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_)

-- Lemmas ----------------------------------------------------------------------

infixr 0 _by_
_by_ : ∀ {ℓ} (A : Set ℓ) → A → A
A by a = a

wk-ih : ∀ {ℓ j k} {P : ℕ → Set ℓ} →
  j ≤ k →
  WfRec _<_ P k →  -- (∀ i → i < k → P i) →
  WfRec _<_ P j    -- (∀ i → i < j → P i)
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

-- Recursive Definitions -------------------------------------------------------

module Rec where

  -- Type of the `_∈𝕍_⟦_⟧` and `_∈𝔼_⟦_⟧` relations, but without the `Gas`-parameter.
  RelTy : Set₁
  RelTy = [] ⊢ 𝕖 → [] ∶⊢ 𝕖 → Set


  -- Field accessors for the R𝕍 and R𝔼 components of the induction hypothesis.
  R𝕍< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → A)
  R𝕍< ih j j<k = π₁ (ih j j<k)
  R𝔼< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → B)
  R𝔼< ih j j<k = π₂ (ih j j<k)

  R𝕍 R𝔼 : ∀ (k : Gas) → (∀ j → j < k → RelTy × RelTy) → RelTy
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
                              e ↪^[ j ] e' →
                              Irred e' →
                              R𝕍 (k ∸ j) (wk-ih (k∸j≤k k j) ih) e' t

  R : ∀ (k : Gas) →
    (∀ j → j < k → RelTy × RelTy) →
    RelTy × RelTy
  R k ih = R𝕍 k ih , R𝔼 k ih

  infix 3 _∈𝕍_⟦_⟧  _∈𝔼_⟦_⟧  _∈𝔾_⟦_⟧  _⊧_∶_

  ∈𝕍𝔼 : Gas → RelTy × RelTy
  ∈𝕍𝔼 = <-rec _ R

  _∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set
  v ∈𝕍 k ⟦ t ⟧ = π₁ (∈𝕍𝔼 k) v t
  e ∈𝔼 k ⟦ t ⟧ = π₂ (∈𝕍𝔼 k) e t

  data _∈𝔾_⟦_⟧ : ∀ {µ₁} → µ₁ →ₛ [] → Gas → Ctx µ₁ → Set where
    [] : idₛ ∈𝔾 k ⟦ ∅ ⟧
    _∷_ : {σ : µ₁ →ₛ []} {k : Gas} {Γ : Ctx µ₁} {v : [] ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} →
      v        ∈𝕍 k ⟦ t ⋯ σ  ⟧ →
      σ        ∈𝔾 k ⟦ Γ      ⟧ →
      (σ ,ₛ v) ∈𝔾 k ⟦ Γ ,, t ⟧

  _⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
  Γ ⊧ e ∶ t = ∀ {k σ} →
    σ       ∈𝔾 k ⟦ Γ ⟧ →
    (e ⋯ σ) ∈𝔼 k ⟦ t ⋯ σ ⟧

  module Unfold-𝕍-𝔼 where

    open import Induction.WellFounded using (module FixPoint)
    open import Data.Nat.Induction using (<-wellFounded; <-rec)

    open FixPoint-FunExt <-wellFounded (λ _ → RelTy × RelTy) R
      renaming (unfold-wfRec to unfold-∈𝕍𝔼'-≡) public

    unfold-∈𝕍𝔼-≡ : {k : Gas} → ∈𝕍𝔼 k ≡ R k (λ j j<k → ∈𝕍𝔼 j)
    unfold-∈𝕍𝔼-≡ = unfold-∈𝕍𝔼'-≡

    unfold-∈𝕍'-≡ : ∀ {k : Gas} → π₁ (∈𝕍𝔼 k) ≡ π₁ (R k (λ j j<k → ∈𝕍𝔼 j))
    unfold-∈𝕍'-≡ = cong π₁ unfold-∈𝕍𝔼-≡

    unfold-∈𝕍-≡ : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      (e ∈𝕍 k ⟦ t ⟧) ≡ R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t
    unfold-∈𝕍-≡ {k = k} rewrite unfold-∈𝕍'-≡ {k} = refl

    fold-∈𝕍 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t → (e ∈𝕍 k ⟦ t ⟧)
    fold-∈𝕍 p = subst (λ x → x) (sym unfold-∈𝕍-≡) p

    unfold-∈𝕍 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      (e ∈𝕍 k ⟦ t ⟧) → R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t
    unfold-∈𝕍 p = subst (λ x → x) unfold-∈𝕍-≡ p

    unfold-∈𝔼'-≡ : ∀ {k : Gas} → π₂ (∈𝕍𝔼 k) ≡ π₂ (R k (λ j j<k → ∈𝕍𝔼 j))
    unfold-∈𝔼'-≡ = cong π₂ unfold-∈𝕍𝔼-≡

    unfold-∈𝔼-≡ : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      (e ∈𝔼 k ⟦ t ⟧) ≡ R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t
    -- unfold-𝔼 {k = k} rewrite unfold-𝔼'-≡ {k} = {!refl!}
    unfold-∈𝔼-≡ {k = k} = {!!}

    fold-∈𝔼 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t → (e ∈𝔼 k ⟦ t ⟧)
    fold-∈𝔼 p = subst (λ x → x) (sym unfold-∈𝔼-≡) p

    unfold-∈𝔼 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
      (e ∈𝔼 k ⟦ t ⟧) → R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t
    unfold-∈𝔼 p = subst (λ x → x) unfold-∈𝔼-≡ p

  open Unfold-𝕍-𝔼 public

-- --------------------------------------------------------------------------------

-- module Ind where

--   infix 3 _∈𝕍_⟦_⟧  _∈𝔼_⟦_⟧  _∈𝔾_⟦_⟧  _⊧_∶_

--   open Rec using () renaming
--     ( _∈𝕍_⟦_⟧ to _∈𝕍_⟦_⟧ᵣ
--     ; _∈𝔼_⟦_⟧ to _∈𝔼_⟦_⟧ᵣ
--     ; _∈𝔾_⟦_⟧ to _∈𝔾_⟦_⟧ᵣ
--     ; _⊧_∶_ to _⊧ᵣ_∶_
--     )
--   mutual
--     data _∈𝕍_⟦_⟧ : ∀ {µ} → µ ⊢ 𝕖 → Gas → µ ∶⊢ 𝕖 → Set where
--       𝕍-⇒ : ∀ {k} →
--         (∀ {j v} → (j≤k : j ≤ k) →
--           v           ∈𝕍 j ⟦ t₁ ⟧ᵣ →
--           (e ⋯ ⦅ v ⦆) ∈𝔼 j ⟦ t₂ ⟧) →
--         (λx e) ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧
--       𝕍-µ : ∀ {k} →
--         (∀ {j} (j<k : j < k) →
--           v ∈𝕍 j ⟦ t ⋯ ⦅ µα t ⦆ ⟧) →
--         (fold v) ∈𝕍 k ⟦ µα t ⟧

--     data _∈𝔼_⟦_⟧ : ∀ {µ} → µ ⊢ 𝕖 → Gas → µ ∶⊢ 𝕖 → Set where
--       𝔼 : ∀ {k} →
--         (∀ {j e'} → (j<k : j < k) →
--           e ↪^[ j ] e' →
--           Irred e' →
--           e' ∈𝕍 (k ∸ j) ⟦ t ⟧) →
--         e ∈𝔼 k ⟦ t ⟧

--   data _∈𝔾_⟦_⟧ : ∀ {µ₁ µ₂} → µ₁ →ₛ µ₂ → Gas → Ctx µ₁ → Set where
--     [] : idₛ ∈𝔾 k ⟦ ∅ ⟧
--     _∷_ : {σ : µ₁ →ₛ µ₂} {k : Gas} {Γ : Ctx µ₁} {v : µ₂ ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} →
--       v        ∈𝕍 k ⟦ t ⋯ σ  ⟧ →
--       σ        ∈𝔾 k ⟦ Γ      ⟧ →
--       (σ ,ₛ v) ∈𝔾 k ⟦ Γ ,, t ⟧

--   _⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
--   Γ ⊧ e ∶ t = ∀ {k σ} →
--     σ       ∈𝔾 k ⟦ Γ ⟧ →
--     (e ⋯ σ) ∈𝔼 k ⟦ t ⟧

-- module Rec→Ind where
--   open Ind
--   open Rec using () renaming
--     ( _∈𝕍_⟦_⟧ to _∈𝕍_⟦_⟧ᵣ
--     ; _∈𝔼_⟦_⟧ to _∈𝔼_⟦_⟧ᵣ
--     ; _∈𝔾_⟦_⟧ to _∈𝔾_⟦_⟧ᵣ
--     ; _⊧_∶_ to _⊧ᵣ_∶_
--     )

--   𝕍ᵣ→𝕍ᵢ : e ∈𝕍 k ⟦ t ⟧ᵣ → e ∈𝕍 k ⟦ t ⟧
--   𝕍ᵣ→𝕍ᵢ {µ} {λx e}   {k} {t₁ ⇒ t₂} e∈𝕍 = {!𝕍-⇒ ?!}
--   𝕍ᵣ→𝕍ᵢ {µ} {fold e} {k} {µα t}    e∈𝕍 = {!!}


open Rec

--------------------------------------------------------------------------------

Monotonicity-𝕍 : Gas → Set
Monotonicity-𝕍 k = (v : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) (j : ℕ) → v ∈𝕍 k ⟦ t ⟧ → j < k → v ∈𝕍 j ⟦ t ⟧

Monotonicity-𝔼 : Gas → Set
Monotonicity-𝔼 k = (e : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) (j : ℕ) → e ∈𝔼 k ⟦ t ⟧ → j < k → e ∈𝔼 j ⟦ t ⟧

Monotonicity : Gas → Set
Monotonicity k = Monotonicity-𝕍 k × Monotonicity-𝔼 k

Monotonicity≤-𝕍 : Gas → Set
Monotonicity≤-𝕍 k = (v : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) (j : ℕ) → v ∈𝕍 k ⟦ t ⟧ → j ≤ k → v ∈𝕍 j ⟦ t ⟧

Monotonicity≤-𝔼 : Gas → Set
Monotonicity≤-𝔼 k = (e : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) (j : ℕ) → e ∈𝔼 k ⟦ t ⟧ → j ≤ k → e ∈𝔼 j ⟦ t ⟧

open import Data.Sum using (_⊎_; inj₁; inj₂)

≤→<∨≡ : ∀ {x y} → x ≤ y → x ≡ y ⊎ x < y
≤→<∨≡ {.zero} {zero} z≤n = inj₁ refl
≤→<∨≡ {.zero} {suc y} z≤n = inj₂ (s≤s z≤n)
≤→<∨≡ {suc x} {suc y} (s≤s x≤y) with ≤→<∨≡ x≤y
... | inj₁ x≡y = inj₁ (cong suc x≡y)
... | inj₂ x<y = inj₂ (s≤s x<y)

mono-<→≤' : (P : ℕ → Set ℓ) → (∀ k j → P k → j < k → P j) → (∀ k j → P k → j ≤ k → P j)
mono-<→≤' P mono-< k j Pk j≤k with ≤→<∨≡ j≤k
... | inj₁ j≡k = subst P (sym j≡k) Pk
... | inj₂ j<k = mono-< k j Pk j<k

mono-<→≤-𝕍 : ∀ {k} → Monotonicity-𝕍 k → Monotonicity≤-𝕍 k
mono-<→≤-𝕍 {k} mono-< e t j e∈𝕍k⟦t⟧ j≤k with ≤→<∨≡ j≤k
... | inj₁ refl = e∈𝕍k⟦t⟧
... | inj₂ j<k = mono-< e t j e∈𝕍k⟦t⟧ j<k

mono-<→≤-𝔼 : ∀ {k} → Monotonicity-𝔼 k → Monotonicity≤-𝔼 k
mono-<→≤-𝔼 {k} mono-< e t j e∈𝔼k⟦t⟧ j≤k with ≤→<∨≡ j≤k
... | inj₁ refl = e∈𝔼k⟦t⟧
... | inj₂ j<k = mono-< e t j e∈𝔼k⟦t⟧ j<k

<→≤ : ∀ {x y} → x < y → x ≤ y
<→≤ = {!!}

MM : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity k
MM k ih = MM-𝕍 k ih , MM-𝔼 k ih
  where

  MM-𝕍 : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity-𝕍 k
  MM-𝕍 k ih (λx e)   (t₁ ⇒ t₂) j λxe∈𝕍k[t₁⇒t₂] j<k =
    (λx e) ∈𝕍 j ⟦ t₁ ⇒ t₂ ⟧
      by fold-∈𝕍 {e = λx e} {t = t₁ ⇒ t₂} (
    (∀ {i v} → (i≤j : i ≤ j) → R𝕍 i (λ j j<k → ∈𝕍𝔼 j) v t₁ → R𝔼 i (λ j j<k → ∈𝕍𝔼 j) (e ⋯ ⦅ v ⦆) t₂)
      by λ {i} {v} i≤j R𝕍-v →
    R𝔼 i (λ j j<k → ∈𝕍𝔼 j) (e ⋯ ⦅ v ⦆) t₂
      -- by
      --   {! MM-𝕍 k ih!}
      --   {! (λxe∈𝕍k[t₁⇒t₂] {i} {!i<k!} (≤-trans i<j j≤k))!}
      by unfold-∈𝔼 (
    e ⋯ ⦅ v ⦆ ∈𝔼 i ⟦ t₂ ⟧
      by let R𝔼-j-e⋯v-t₂ = R𝔼 j (wk-ih (<→≤ j<k) (λ j j<k → ∈𝕍𝔼 j)) (e ⋯ ⦅ v ⦆) t₂ by {! λxe∈𝕍k[t₁⇒t₂] {j} (<→≤ j<k) ? !} in
         let R𝔼-j-e⋯v-t₂' = R𝔼 j (λ j j<k → ∈𝕍𝔼 j) (e ⋯ ⦅ v ⦆) t₂ by {! λxe∈𝕍k[t₁⇒t₂] {j} (<→≤ j<k) ? !} in
         let [e⋯v]∈𝔼j⟦t₂⟧ = e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ by fold-∈𝔼 {!λxe∈𝕍k[t₁⇒t₂] {j} {!j≤k!} ?!} in
         let [e⋯v]∈𝔼j⟦t₂⟧' = e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ by {!λxe∈𝕍k[t₁⇒t₂] {j} {!j≤k!} ?!} in
         -- let [e⋯v]∈𝔼j⟦t₂⟧ = e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ by {!!} in
         mono-<→≤-𝔼 (π₂ (ih j j<k)) (e ⋯ ⦅ v ⦆) t₂ i [e⋯v]∈𝔼j⟦t₂⟧ i≤j
         -- π₂ (ih j j<k) (e ⋯ ⦅ v ⦆) t₂ i (e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ by {!!}) {!i<j!}
      -- by {!MM-𝔼 k ih (e ⋯ ⦅ v ⦆) t₂ i!}
      -- by {!λxe∈𝕍k[t₁⇒t₂] {i} {!i<k!} ?!}
    )
      -- by λ {i} {v} i≤j R𝕍-v {i'} {e'} i'<i → {!!} , (λ irred-e' → {!ih (i ∸ i') _ e' t₂ !})
    )
  MM-𝕍 k ih (fold v) (µα t)    j v∈V j≤k =
    fold v ∈𝕍 j ⟦ µα t ⟧          by
    fold v ∈𝕍 j ⟦ µα t ⟧          by {!!}

  -- R𝕍 k ih (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
  --                               (j≤k : j ≤ k) →
  --                               R𝕍 j (wk-ih j≤k ih) v t₁ →
  --                               R𝔼 j (wk-ih j≤k ih) (e ⋯ ⦅ v ⦆) t₂

  MM-𝔼 : ∀ k → (∀ j → j < k → Monotonicity j) → Monotonicity-𝔼 k
  MM-𝔼 k ih e t j e∈k[t] j≤k =
    e ∈𝔼 j ⟦ t ⟧
      by fold-∈𝔼 (
    (∀ {i} {e'} → i < j → e ↪^[ i ] e' → Irred e' → R𝕍 (j ∸ i) (wk-ih (k∸j≤k j i) (λ j' j'<k → ∈𝕍𝔼 j')) e' t)
      by λ {i} {e'} i<j e↪[i]e' irred-e' →
    R𝕍 (j ∸ i) (wk-ih (k∸j≤k j i) (λ j' j'<k → ∈𝕍𝔼 j')) e' t
      by unfold-∈𝕍 (
    e' ∈𝕍 j ∸ i ⟦ t ⟧
      by
        let i<k = ≤-trans i<j {!j≤k!} in
        let R𝕍[k-i]e' = e∈k[t] {i} {e'} i<k e↪[i]e' irred-e' in
        -- let e'∈𝕍k∸i[t] = R𝕍[k-i]e' in
        -- let e'∈𝕍j∸i[t] = π₁ (ih (k ∸ i) {!!}) e' t (j ∸ i) {!!} {!!} in
        let e'∈𝕍j∸i[t] = π₁ (ih i i<k) e' t (j ∸ i) {!!} {!!} in
        {!fold-∈𝕍 R𝕍[k-i]e'!}
    )
    )

monotonicity : 
  ∀ k → Monotonicity k
monotonicity = <-rec _ MM

monotonicity-𝕍 : 
  ∀ k (v : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) j →
  v ∈𝕍 k ⟦ t ⟧ →
  j ≤ k →
  v ∈𝕍 j ⟦ t ⟧
-- monotonicity-𝕍 = {!!}
monotonicity-𝕍 k (λx e)   (t₁ ⇒ t₂) j λxe∈𝕍k⟦t₁⇒t₂⟧   j≤k {i} {v} i≤j v∈𝕍i⟦t₁⟧ {h} {e'} h<i e⋯v↪^[h]e' irred-e' =
  {!!}
  -- let i≤k = i ≤ k by {!!} in
  -- -- {!λxe∈𝕍k⟦t₁⇒t₂⟧ {i} i≤k {!v∈𝕍i⟦t₁⟧!} h<i e⋯v↪^[h]e' irred-e'!}
  -- R𝕍 (i ∸ h)
  --     (wk-ih (k∸j≤k i h)
  --      (wk-ih i≤j
  --       -- (WF.All.wfRecBuilder <-wellFounded (Level.suc Level.zero)
  --       --  (λ _ → RelTy × RelTy) (λ k₁ ih → R𝕍 k₁ ih , R𝔼 k₁ ih) j)
  --       (λ i _ → ∈𝕍𝔼 i)
  --       ))
  --     e' t₂
  -- by
  -- {!fold-∈𝔼 (λxe∈𝕍k⟦t₁⇒t₂⟧ {i} i≤k {!v∈𝕍i⟦t₁⟧!})!}
 
-- monotonicity-𝕍 k (λx e)   (t₁ ⇒ t₂) j λxe∈𝕍k⟦t₁⇒t₂⟧   j≤k {i} {v} i≤j v∈𝕍i⟦t₁⟧ =
--   -- (e ⋯ ⦅ v ⦆) ∈𝔼 i ⟦ t₂ ⟧
--   -- let e⋯v∈𝔼i⟦t₂⟧ = (e ⋯ ⦅ v ⦆) ∈𝔼 i ⟦ t₂ ⟧ by {!λxe∈𝕍k⟦t₁⇒t₂⟧ {i} {!i≤k!} {!v∈𝕍i⟦t₁⟧!}!} in
--   let e⋯v∈𝔼i⟦t₂⟧ = (e ⋯ ⦅ v ⦆) ∈𝔼 i ⟦ t₂ ⟧ by {!λxe∈𝕍k⟦t₁⇒t₂⟧ {i} {!i≤k!} {!v∈𝕍i⟦t₁⟧!}!} in
--   {!λxe∈𝕍k⟦t₁⇒t₂⟧ {i} {!i≤k!} {!v∈𝕍i⟦t₁⟧!}!}
monotonicity-𝕍 k (fold v) (µα t)    j foldv∈𝕍k⟦µαt⟧ j≤k = {!!}

-- RecTy : Gas → Set
-- RecTy k = (v : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) (j : ℕ) → v ∈𝕍 k ⟦ t ⟧ → j ≤ k → v ∈𝕍 j ⟦ t ⟧

-- MM : ∀ k → (∀ j → j < k → RecTy j) → RecTy k
-- -- MM : ∀ k → WfRec _<_ RecTy k → RecTy k
-- MM k ih (λx e)   (t₁ ⇒ t₂) j v∈V j≤k =
--   (λx e) ∈𝕍 j ⟦ t₁ ⇒ t₂ ⟧
--     by fold-∈𝕍 {e = λx e} {t = t₁ ⇒ t₂} (
--   (∀ {i v} → (i≤j : i ≤ j) → R𝕍 i (λ j j<k → ∈𝕍𝔼 j) v t₁ → R𝔼 i (λ j j<k → ∈𝕍𝔼 j) (e ⋯ ⦅ v ⦆) t₂)
--     -- by λ {i} {v} i≤j R𝕍-v → {!!}
--     by λ {i} {v} i≤j R𝕍-v {i'} {e'} i'<i → {!!} , (λ irred-e' → {!ih (i ∸ i') _ e' t₂ !})
--   )
-- MM k ih (fold v) (µα t)    j v∈V j≤k =
--   fold v ∈𝕍 j ⟦ µα t ⟧          by
--   fold v ∈𝕍 j ⟦ µα t ⟧          by {!!}

-- -- R𝕍 k ih (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
-- --                               (j≤k : j ≤ k) →
-- --                               R𝕍 j (wk-ih j≤k ih) v t₁ →
-- --                               R𝔼 j (wk-ih j≤k ih) (e ⋯ ⦅ v ⦆) t₂

-- monotonicity : 
--   ∀ k (v : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) j →
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
