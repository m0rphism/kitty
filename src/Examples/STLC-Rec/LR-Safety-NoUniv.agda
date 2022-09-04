module Examples.STLC-Rec.LR-Safety-NoUniv where

open import Examples.STLC-Rec.Definitions hiding (_,_)
open import Examples.STLC-Rec.SubjectReduction

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction using (<-rec; <-wellFounded)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-step; ∸-monoˡ-≤; <⇒≤; +-comm)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax; ∃-syntax) renaming (proj₁ to π₁; proj₂ to π₂) 
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic
open import Function using (_$_)
open import Induction
open import Induction.WellFounded as WF using (WfRec)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)

-- Lemmas ----------------------------------------------------------------------

infixr 0 _by_
_by_ : ∀ {ℓ} (A : Set ℓ) → A → A
A by a = a

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
  ↪-refl : e ↪^[ k ] e
  ↪-step : e₁ ↪ e₂ → e₂ ↪^[ k ] e₃ → e₁ ↪^[ suc k ] e₃

lift-↪^' : e₁ ↪^[ k ] e₂ → e₁ ↪^[ k + k' ] e₂
lift-↪^' ↪-refl = ↪-refl
lift-↪^' (↪-step e₁↪e₂ e₂↪^[k]e₃) = ↪-step e₁↪e₂ (lift-↪^' e₂↪^[k]e₃)

lift-↪^ : ∀ {k k'} → e₁ ↪^[ k ] e₂ → e₁ ↪^[ k' + k ] e₂
lift-↪^ {_} {e₁} {e₂} {k} {k'} p = subst (e₁ ↪^[_] e₂) (+-comm k k') (lift-↪^' p)

↪^-trans : e₁ ↪^[ k ] e₂ → e₂ ↪^[ k' ] e₃ → e₁ ↪^[ k + k' ] e₃
↪^-trans ↪-refl q = lift-↪^ q
↪^-trans (↪-step s p) q = ↪-step s (↪^-trans p q)

-- ↪^→↪* : e₁ ↪^[ k ] e₂ → e₁ ↪* e₂
-- ↪^→↪* p = ?

-- ↪*→↪^ : e₁ ↪* e₂ → ∃[ k ] (e₁ ↪^[ k ] e₂)
-- ↪*→↪^ p = {!!}

Red : µ ⊢ 𝕖 → Set
Red e = ∃[ e' ] (e ↪ e')

Irred : µ ⊢ 𝕖 → Set
Irred e = ¬ Red e

-- _∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set

-- -- (λx e) ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧ = ∀ {j v} →
-- --                               v           ∈𝕍 k ⟦ t₁ ⟧ →
-- --                               (e ⋯ ⦅ v ⦆) ∈𝔼 k ⟦ t₂ ⟧
-- -- _      ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧ = ⊥
-- -- fold v ∈𝕍 suc k ⟦ µα t    ⟧ = v ∈𝕍 k ⟦ t ⋯ ⦅ µα t ⦆ ⟧
-- -- fold v ∈𝕍 zero ⟦ µα t    ⟧ = ⊥
-- -- _      ∈𝕍 k ⟦ µα t    ⟧ = ⊥
-- -- _      ∈𝕍 k ⟦ 𝟘       ⟧ = ⊥

-- v ∈𝕍 k ⟦ t ⟧ with k
-- ... | zero = ⊥
-- ... | suc k with t | v
-- ...   | (t₁ ⇒ t₂) | (λx e)   = ∀ {v} → v ∈𝕍 suc k ⟦ t₁ ⟧ → (e ⋯ ⦅ v ⦆) ∈𝔼 suc k ⟦ t₂ ⟧
-- ...   | (t₁ ⇒ t₂) | _        = ⊥
-- ...   | (µα t)    | (fold v) = v ∈𝕍 k ⟦ t ⋯ ⦅ µα t ⦆ ⟧
-- ...   | (µα t)    | _        = ⊥ 
-- ...   | 𝟘         | _        = ⊥

-- e ∈𝔼 k ⟦ t ⟧ = ∀ {j e'} →
--   (j<k : j < k) →
--   e ↪^[ j ] e' →
--   Irred e' →
--   e' ∈𝕍 k ∸ j ⟦ t ⟧





-- _∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set

-- (λx e) ∈𝕍 k     ⟦ t₁ ⇒ t₂ ⟧ = ∀ {v} →
--                                   v           ∈𝕍 k ⟦ t₁ ⟧ →
--                                   (e ⋯ ⦅ v ⦆) ∈𝔼 k ⟦ t₂ ⟧
-- _      ∈𝕍 k     ⟦ t₁ ⇒ t₂ ⟧ = ⊥
-- fold v ∈𝕍 suc k ⟦ µα t    ⟧ = v ∈𝕍 k ⟦ t ⋯ ⦅ µα t ⦆ ⟧
-- fold v ∈𝕍 zero  ⟦ µα t    ⟧ = ⊥
-- _      ∈𝕍 k     ⟦ µα t    ⟧ = ⊥
-- _      ∈𝕍 k     ⟦ 𝟘       ⟧ = ⊥

-- e ∈𝔼 zero  ⟦ t ⟧ = ⊥
-- e ∈𝔼 suc k ⟦ t ⟧ = ∀ {e'} →
--   e ↪^[ k ] e' →
--   Irred e' →
--   e' ∈𝕍 k ⟦ t ⟧






_∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set

(λx e) ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧ = ∀ {j v} →
                              (j≤k : j ≤ k) →
                              v           ∈𝕍 j ⟦ t₁ ⟧ →
                              (e ⋯ ⦅ v ⦆) ∈𝔼 j ⟦ t₂ ⟧
_      ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧ = ⊥
fold v ∈𝕍 k ⟦ µα t    ⟧ = ∀ {j} →
                              (j<k : j < k) →
                              v ∈𝕍 j ⟦ t ⋯ ⦅ µα t ⦆ ⟧
_      ∈𝕍 k ⟦ µα t    ⟧ = ⊥
_      ∈𝕍 k ⟦ 𝟘       ⟧ = ⊥

e ∈𝔼 k ⟦ t ⟧ = ∀ {j e'} →
  (j<k : j < k) →
  e ↪^[ j ] e' →
  Irred e' →
  e' ∈𝕍 k ∸ j ⟦ t ⟧


-- -- Recursive Definitions -------------------------------------------------------

-- module Rec where

--   -- Type of the `_∈𝕍_⟦_⟧` and `_∈𝔼_⟦_⟧` relations, but without the `Gas`-parameter.
--   RelTy : Set₁
--   RelTy = [] ⊢ 𝕖 → [] ∶⊢ 𝕖 → Set


--   -- Field accessors for the R𝕍 and R𝔼 components of the induction hypothesis.
--   R𝕍< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → A)
--   R𝕍< ih j j<k = π₁ (ih j j<k)
--   R𝔼< : ∀ {k} → (∀ j → j < k → A × B) → (∀ j → j < k → B)
--   R𝔼< ih j j<k = π₂ (ih j j<k)

--   R𝕍 R𝔼 : ∀ (k : Gas) → (∀ j → j < k → RelTy × RelTy) → RelTy
--   R𝕍 k ih _        (`[ p ] x) = ⊥
--   R𝕍 k ih (λx e)   (t₁ ⇒ t₂)  = ∀ {j v} →
--                               (j≤k : j ≤ k) →
--                               R𝕍 j (wk-ih j≤k ih) v t₁ →
--                               R𝔼 j (wk-ih j≤k ih) (e ⋯ ⦅ v ⦆) t₂
--   R𝕍 k ih _        (t₁ ⇒ t₂)  = ⊥
--   R𝕍 k ih _        𝟘          = ⊥
--   R𝕍 k ih (fold v) (µα t)     = ∀ {j} →
--                               (j<k : j < k) →
--                               R𝕍< ih j j<k v (t ⋯ ⦅ µα t ⦆)
--   R𝕍 k ih _        (µα t)     = ⊥
--   R𝔼 k ih e        t          = ∀ {j e'} →
--                               (j<k : j < k) →
--                               e ↪^[ j ] e' →
--                               Irred e' →
--                               R𝕍 (k ∸ j) (wk-ih (k∸j≤k k j) ih) e' t

--   R : ∀ (k : Gas) →
--     (∀ j → j < k → RelTy × RelTy) →
--     RelTy × RelTy
--   R k ih = R𝕍 k ih , R𝔼 k ih

--   infix 3 _∈𝕍_⟦_⟧  _∈𝔼_⟦_⟧  _∈𝔾_⟦_⟧  _⊧_∶_

--   ∈𝕍𝔼 : Gas → RelTy × RelTy
--   ∈𝕍𝔼 = <-rec _ R

--   _∈𝕍_⟦_⟧ _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set
--   v ∈𝕍 k ⟦ t ⟧ = π₁ (∈𝕍𝔼 k) v t
--   e ∈𝔼 k ⟦ t ⟧ = π₂ (∈𝕍𝔼 k) e t

--   _∈𝔾_⟦_⟧ : ∀ {µ} → µ →ₛ [] → Gas → Ctx µ → Set
--   _∈𝔾_⟦_⟧ {µ = µ} σ k Γ = (x : µ ∋ 𝕖) → σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ σ ⟧ 

--   -- TODO: it's probably easier to transport the next two lemmas from
--   -- the inductive def or vice versa.

--   []𝔾 : idₛ ∈𝔾 k ⟦ ∅ ⟧
--   []𝔾 ()

--   _∷𝔾_ : {σ : µ₁ →ₛ []} {k : Gas} {Γ : Ctx µ₁} {v : [] ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} →
--     v        ∈𝕍 k ⟦ t ⋯ σ  ⟧ →
--     σ        ∈𝔾 k ⟦ Γ      ⟧ →
--     (σ ,ₛ v) ∈𝔾 k ⟦ Γ ,, t ⟧
--   _∷𝔾_ {µ₁} {σ} {k} {Γ} {v} {t} v∈𝕍 σ∈𝔾 (here refl) =
--       (σ ,ₛ v) 𝕖 (here refl) ∈𝕍 k ⟦ wk-telescope (Γ ,, t) (here refl) ⋯ (σ ,ₛ v) ⟧
--     by (
--       v ∈𝕍 k ⟦ t ⋯ wk ⋯ (σ ,ₛ v) ⟧
--     by subst (λ ■ → v ∈𝕍 k ⟦ ■ ⟧) (sym (wk-cancels-,ₛ t σ v)) (
--       v ∈𝕍 k ⟦ t ⋯ σ ⟧
--     by v∈𝕍))
--   _∷𝔾_ {µ₁} {σ} {k} {Γ} {v} {t} v∈𝕍 σ∈𝔾 (there x) =
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope (Γ ,, t) (there x) ⋯ (σ ,ₛ v) ⟧
--     by (
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ wk ⋯ (σ ,ₛ v) ⟧
--     by subst (λ ■ → σ 𝕖 x ∈𝕍 k ⟦ ■ ⟧) (sym (wk-cancels-,ₛ (wk-telescope Γ x) σ v)) (
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ σ ⟧
--     by σ∈𝔾 x))

--   _⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
--   Γ ⊧ e ∶ t = ∀ {k σ} →
--     σ       ∈𝔾 k ⟦ Γ ⟧ →
--     (e ⋯ σ) ∈𝔼 k ⟦ t ⋯ σ ⟧

--   module Unfold-𝕍-𝔼 where

--     open import Induction.WellFounded using (module FixPoint)
--     open import Data.Nat.Induction using (<-wellFounded; <-rec)

--     open FixPoint-FunExt <-wellFounded (λ _ → RelTy × RelTy) R
--       renaming (unfold-wfRec to unfold-∈𝕍𝔼'-≡) public

--     unfold-∈𝕍𝔼-≡ : {k : Gas} → ∈𝕍𝔼 k ≡ R k (λ j j<k → ∈𝕍𝔼 j)
--     unfold-∈𝕍𝔼-≡ = unfold-∈𝕍𝔼'-≡

--     unfold-∈𝕍'-≡ : ∀ {k : Gas} → π₁ (∈𝕍𝔼 k) ≡ π₁ (R k (λ j j<k → ∈𝕍𝔼 j))
--     unfold-∈𝕍'-≡ = cong π₁ unfold-∈𝕍𝔼-≡

--     unfold-∈𝕍-≡ : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       (e ∈𝕍 k ⟦ t ⟧) ≡ R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t
--     unfold-∈𝕍-≡ {k = k} rewrite unfold-∈𝕍'-≡ {k} = refl

--     fold-∈𝕍 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t → (e ∈𝕍 k ⟦ t ⟧)
--     fold-∈𝕍 p = subst (λ x → x) (sym unfold-∈𝕍-≡) p

--     unfold-∈𝕍 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       (e ∈𝕍 k ⟦ t ⟧) → R𝕍 k (λ j j<k → ∈𝕍𝔼 j) e t
--     unfold-∈𝕍 p = subst (λ x → x) unfold-∈𝕍-≡ p

--     unfold-∈𝔼'-≡ : ∀ {k : Gas} → π₂ (∈𝕍𝔼 k) ≡ π₂ (R k (λ j j<k → ∈𝕍𝔼 j))
--     unfold-∈𝔼'-≡ = cong π₂ unfold-∈𝕍𝔼-≡

--     unfold-∈𝔼-≡ : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       (e ∈𝔼 k ⟦ t ⟧) ≡ R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t
--     -- unfold-𝔼 {k = k} rewrite unfold-𝔼'-≡ {k} = {!refl!}
--     unfold-∈𝔼-≡ {k = k} = {!!}

--     fold-∈𝔼 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t → (e ∈𝔼 k ⟦ t ⟧)
--     fold-∈𝔼 p = subst (λ x → x) (sym unfold-∈𝔼-≡) p

--     unfold-∈𝔼 : ∀ {k : Gas} {e : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} →
--       (e ∈𝔼 k ⟦ t ⟧) → R𝔼 k (λ j j<k → ∈𝕍𝔼 j) e t
--     unfold-∈𝔼 p = subst (λ x → x) unfold-∈𝔼-≡ p

--   open Unfold-𝕍-𝔼 public

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
--     data _∈𝕍_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set where
--       𝕍-⇒ : ∀ {k} →
--         (∀ {j v} → (j≤k : j ≤ k) →
--           v           ∈𝕍 j ⟦ t₁ ⟧ᵣ →
--           (e ⋯ ⦅ v ⦆) ∈𝔼 j ⟦ t₂ ⟧) →
--         (λx e) ∈𝕍 k ⟦ t₁ ⇒ t₂ ⟧
--       𝕍-µ : ∀ {k} →
--         (∀ {j} (j<k : j < k) →
--           v ∈𝕍 j ⟦ t ⋯ ⦅ µα t ⦆ ⟧) →
--         (fold v) ∈𝕍 k ⟦ µα t ⟧

--     data _∈𝔼_⟦_⟧ : [] ⊢ 𝕖 → Gas → [] ∶⊢ 𝕖 → Set where
--       𝔼 : ∀ {k} →
--         (∀ {j e'} → (j<k : j < k) →
--           e ↪^[ j ] e' →
--           Irred e' →
--           e' ∈𝕍 (k ∸ j) ⟦ t ⟧) →
--         e ∈𝔼 k ⟦ t ⟧

--   unwrap-𝔼 : e ∈𝔼 k ⟦ t ⟧ → (∀ {j e'} → (j<k : j < k) →
--         e ↪^[ j ] e' →
--         Irred e' →
--         e' ∈𝕍 (k ∸ j) ⟦ t ⟧)
--   unwrap-𝔼 (𝔼 e) = e

--   _∈𝔾_⟦_⟧ : ∀ {µ} → µ →ₛ [] → Gas → Ctx µ → Set
--   _∈𝔾_⟦_⟧ {µ = µ} σ k Γ = (x : µ ∋ 𝕖) → σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ σ ⟧ 

--   []𝔾 : idₛ ∈𝔾 k ⟦ ∅ ⟧
--   []𝔾 ()

--   _∷𝔾_ : {σ : µ₁ →ₛ []} {k : Gas} {Γ : Ctx µ₁} {v : [] ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} →
--     v        ∈𝕍 k ⟦ t ⋯ σ  ⟧ →
--     σ        ∈𝔾 k ⟦ Γ      ⟧ →
--     (σ ,ₛ v) ∈𝔾 k ⟦ Γ ,, t ⟧
--   _∷𝔾_ {µ₁} {σ} {k} {Γ} {v} {t} v∈𝕍 σ∈𝔾 (here refl) =
--       (σ ,ₛ v) 𝕖 (here refl) ∈𝕍 k ⟦ wk-telescope (Γ ,, t) (here refl) ⋯ (σ ,ₛ v) ⟧
--     by (
--       v ∈𝕍 k ⟦ t ⋯ wk ⋯ (σ ,ₛ v) ⟧
--     by subst (λ ■ → v ∈𝕍 k ⟦ ■ ⟧) (sym (wk-cancels-,ₛ t σ v)) (
--       v ∈𝕍 k ⟦ t ⋯ σ ⟧
--     by v∈𝕍))
--   _∷𝔾_ {µ₁} {σ} {k} {Γ} {v} {t} v∈𝕍 σ∈𝔾 (there x) =
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope (Γ ,, t) (there x) ⋯ (σ ,ₛ v) ⟧
--     by (
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ wk ⋯ (σ ,ₛ v) ⟧
--     by subst (λ ■ → σ 𝕖 x ∈𝕍 k ⟦ ■ ⟧) (sym (wk-cancels-,ₛ (wk-telescope Γ x) σ v)) (
--       σ 𝕖 x ∈𝕍 k ⟦ wk-telescope Γ x ⋯ σ ⟧
--     by σ∈𝔾 x))

--   _⊧_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set
--   Γ ⊧ e ∶ t = ∀ {k σ} →
--     σ       ∈𝔾 k ⟦ Γ ⟧ →
--     (e ⋯ σ) ∈𝔼 k ⟦ t ⋯ σ ⟧


-- module Rec→Ind where
--   open Ind
--   open Rec using () renaming
--     ( _∈𝕍_⟦_⟧ to _∈𝕍_⟦_⟧ᵣ
--     ; _∈𝔼_⟦_⟧ to _∈𝔼_⟦_⟧ᵣ
--     ; _∈𝔾_⟦_⟧ to _∈𝔾_⟦_⟧ᵣ
--     ; _⊧_∶_ to _⊧ᵣ_∶_
--     ; []𝔾 to []𝔾ᵣ
--     ; _∷𝔾_ to _∷𝔾ᵣ_
--     )

--   RelTy : ℕ → Set _
--   RelTy k = (∀ {e t} → e ∈𝕍 k ⟦ t ⟧ᵣ → e ∈𝕍 k ⟦ t ⟧)
--           × (∀ {e t} → e ∈𝔼 k ⟦ t ⟧ᵣ → e ∈𝔼 k ⟦ t ⟧)

--   mutual
--     𝕍-R→I : ∀ k → (∀ j → j < k → RelTy j) → (∀ {e t} → e ∈𝕍 k ⟦ t ⟧ᵣ → e ∈𝕍 k ⟦ t ⟧)
--     𝕍-R→I k ih {λx e}   {t₁ ⇒ t₂} λxe∈𝕍 = 𝕍-⇒ λ {j} {v} j≤k v∈𝕍ᵣ → 𝔼-R→I j (wk-ih j≤k ih) (
--         e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ᵣ
--       by let λxe∈𝕍' = Rec.unfold-∈𝕍 {k = k} {e = λx e} {t = t₁ ⇒ t₂} λxe∈𝕍 in
--           Rec.fold-∈𝔼 (λxe∈𝕍' j≤k (Rec.unfold-∈𝕍 v∈𝕍ᵣ)))
--     𝕍-R→I k ih {fold e} {µα t}    fold-e∈𝕍 =
--       let fold-e∈𝕍' = Rec.unfold-∈𝕍 {k = k} {e = fold e} {t = µα t} fold-e∈𝕍 in
--       𝕍-µ λ {j} j<k → π₁ (ih j j<k) (fold-e∈𝕍' j<k)

--     𝔼-R→I : ∀ k → (∀ j → j < k → RelTy j) → (∀ {e t} → e ∈𝔼 k ⟦ t ⟧ᵣ → e ∈𝔼 k ⟦ t ⟧)
--     𝔼-R→I k ih {e} {t} e∈𝔼 = 𝔼 (λ {j} {e'} j<k e→e' irred-e' → 𝕍-R→I (k ∸ j) (wk-ih (k∸j≤k k j) ih)
--       (Rec.fold-∈𝕍 (Rec.unfold-∈𝔼 {k = k} {e = e} {t = t} e∈𝔼 j<k e→e' irred-e')))

--   R→I : ∀ k → RelTy k
--   R→I = <-rec _ λ k ih → 𝕍-R→I k ih , 𝔼-R→I k ih

--   RelTy' : ℕ → Set _
--   RelTy' k = (∀ {e t} → e ∈𝕍 k ⟦ t ⟧ → e ∈𝕍 k ⟦ t ⟧ᵣ)
--            × (∀ {e t} → e ∈𝔼 k ⟦ t ⟧ → e ∈𝔼 k ⟦ t ⟧ᵣ)

--   mutual
--     𝕍-I→R : ∀ k → (∀ j → j < k → RelTy' j) → (∀ {e t} → e ∈𝕍 k ⟦ t ⟧ → e ∈𝕍 k ⟦ t ⟧ᵣ)
--     𝕍-I→R = {!!}
--     -- 𝕍-I→R k ih {λx e}   {t₁ ⇒ t₂} λxe∈𝕍 = 𝕍-⇒ λ {j} {v} j≤k v∈𝕍ᵣ → 𝔼-I→R j (wk-ih j≤k ih) (
--     --     e ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⟧ᵣ
--     --   by let λxe∈𝕍' = Rec.unfold-∈𝕍 {k = k} {e = λx e} {t = t₁ ⇒ t₂} λxe∈𝕍 in
--     --       Rec.fold-∈𝔼 (λxe∈𝕍' j≤k (Rec.unfold-∈𝕍 v∈𝕍ᵣ)))
--     -- 𝕍-I→R k ih {fold e} {µα t}    fold-e∈𝕍 =
--     --   let fold-e∈𝕍' = Rec.unfold-∈𝕍 {k = k} {e = fold e} {t = µα t} fold-e∈𝕍 in
--     --   𝕍-µ λ {j} j<k → π₁ (ih j j<k) (fold-e∈𝕍' j<k)

--     𝔼-I→R : ∀ k → (∀ j → j < k → RelTy' j) → (∀ {e t} → e ∈𝔼 k ⟦ t ⟧ → e ∈𝔼 k ⟦ t ⟧ᵣ)
--     𝔼-I→R = {!!}
--     -- 𝔼-I→R k ih {e} {t} e∈𝔼 = 𝔼 (λ {j} {e'} j<k e→e' irred-e' → 𝕍-I→R (k ∸ j) (wk-ih (k∸j≤k k j) ih)
--     --   (Rec.fold-∈𝕍 (Rec.unfold-∈𝔼 {k = k} {e = e} {t = t} e∈𝔼 j<k e→e' irred-e')))

--   I→R : ∀ k → RelTy' k
--   I→R = <-rec _ λ k ih → 𝕍-I→R k ih , 𝔼-I→R k ih

--   𝕍ᵣ→𝕍ᵢ : e ∈𝕍 k ⟦ t ⟧ᵣ → e ∈𝕍 k ⟦ t ⟧
--   𝕍ᵣ→𝕍ᵢ {e} {k} {t} = π₁ (R→I k) {e} {t}

--   𝔼ᵣ→𝔼ᵢ : e ∈𝔼 k ⟦ t ⟧ᵣ → e ∈𝔼 k ⟦ t ⟧
--   𝔼ᵣ→𝔼ᵢ {e} {k} {t} = π₂ (R→I k) {e} {t}

--   𝕍ᵢ→𝕍ᵣ : e ∈𝕍 k ⟦ t ⟧ → e ∈𝕍 k ⟦ t ⟧ᵣ
--   𝕍ᵢ→𝕍ᵣ {e} {k} {t} = π₁ (I→R k) {e} {t}

--   𝔼ᵢ→𝔼ᵣ : e ∈𝔼 k ⟦ t ⟧ → e ∈𝔼 k ⟦ t ⟧ᵣ
--   𝔼ᵢ→𝔼ᵣ {e} {k} {t} = π₂ (I→R k) {e} {t}

--   𝔾ᵣ→𝔾ᵢ : ∀ {σ} → σ ∈𝔾 k ⟦ Γ ⟧ᵣ → σ ∈𝔾 k ⟦ Γ ⟧
--   𝔾ᵣ→𝔾ᵢ σ∈𝔾 x = 𝕍ᵣ→𝕍ᵢ (σ∈𝔾 x)

--   𝔾ᵢ→𝔾ᵣ : ∀ {σ} → σ ∈𝔾 k ⟦ Γ ⟧ → σ ∈𝔾 k ⟦ Γ ⟧ᵣ
--   𝔾ᵢ→𝔾ᵣ σ∈𝔾 x = 𝕍ᵢ→𝕍ᵣ (σ∈𝔾 x)

--   ⊧ᵣ→⊧ᵢ : Γ ⊧ᵣ e ∶ t → Γ ⊧ e ∶ t
--   ⊧ᵣ→⊧ᵢ ⊧e σ∈𝔾 = 𝔼ᵣ→𝔼ᵢ (⊧e (𝔾ᵢ→𝔾ᵣ σ∈𝔾))

--   ⊧ᵢ→⊧ᵣ : Γ ⊧ e ∶ t → Γ ⊧ᵣ e ∶ t
--   ⊧ᵢ→⊧ᵣ ⊧e σ∈𝔾 = 𝔼ᵢ→𝔼ᵣ (⊧e (𝔾ᵣ→𝔾ᵢ σ∈𝔾))


-- open Rec
-- open Ind using (𝕍-⇒; 𝕍-µ; 𝔼; unwrap-𝔼) renaming
--   ( _∈𝕍_⟦_⟧ to _∈𝕍_⟦_⟧ᵢ
--   ; _∈𝔼_⟦_⟧ to _∈𝔼_⟦_⟧ᵢ
--   ; _∈𝔾_⟦_⟧ to _∈𝔾_⟦_⟧ᵢ
--   ; _⊧_∶_ to _⊧ᵢ_∶_
--   ; []𝔾 to []𝔾ᵢ
--   ; _∷𝔾_ to _∷𝔾ᵢ_
--   )
-- open Rec→Ind

-- --------------------------------------------------------------------------------

-- monotonicity-𝕍ᵢ : 
--   ∀ {k} {v : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} {j} →
--   j ≤ k →
--   v ∈𝕍 k ⟦ t ⟧ᵢ →
--   v ∈𝕍 j ⟦ t ⟧ᵢ
-- monotonicity-𝕍ᵢ {k} {.(λx e)} {.(t₁ ⇒ t₂)} {j} j≤k (𝕍-⇒ {t₁ = t₁} {e = e} {t₂ = t₂} p) =
--   𝕍-⇒ λ {i} {v} i≤j v∈𝕍i →
--     let i≤k = i ≤ k by ≤-trans i≤j j≤k in
--     p i≤k v∈𝕍i
-- monotonicity-𝕍ᵢ {k} {.(fold v)} {.(µα t)}  {j} j≤k (𝕍-µ {v = v} {t = t} p) =
--   𝕍-µ λ {i} i<j →
--     let i<k = i < k by ≤-trans i<j j≤k in
--     p i<k

-- monotonicity-𝔼ᵢ : 
--   ∀ k (e : [] ⊢ 𝕖) (t : [] ⊢ 𝕥) j →
--   j ≤ k →
--   e ∈𝔼 k ⟦ t ⟧ᵢ →
--   e ∈𝔼 j ⟦ t ⟧ᵢ
-- monotonicity-𝔼ᵢ k e t j j≤k (𝔼 p) =
--   𝔼 λ {i} {e'} i<j e→[i]e' irred-e' →
--     let i<k = i < k by ≤-trans i<j j≤k in
--     let P = e' ∈𝕍 k ∸ i ⟦ t ⟧ᵢ by p i<k e→[i]e' irred-e' in
--     let j∸i≤k∸i = j ∸ i ≤ k ∸ i by ∸-monoˡ-≤ i j≤k in
--     monotonicity-𝕍ᵢ j∸i≤k∸i P

-- monotonicity-𝔾ᵢ : 
--   ∀ {k} {σ : µ →ₛ []} {Γ : Ctx µ} {j} →
--   j ≤ k →
--   σ ∈𝔾 k ⟦ Γ ⟧ᵢ →
--   σ ∈𝔾 j ⟦ Γ ⟧ᵢ
-- monotonicity-𝔾ᵢ j≤k σ∈𝔾 x = monotonicity-𝕍ᵢ j≤k (σ∈𝔾 x)

-- monotonicity-𝕍ᵣ : 
--   ∀ {k} {v : [] ⊢ 𝕖} {t : [] ⊢ 𝕥} {j} →
--   j ≤ k →
--   v ∈𝕍 k ⟦ t ⟧ →
--   v ∈𝕍 j ⟦ t ⟧
-- monotonicity-𝕍ᵣ j≤k v∈𝕍 = 𝕍ᵢ→𝕍ᵣ (monotonicity-𝕍ᵢ j≤k (𝕍ᵣ→𝕍ᵢ v∈𝕍))

-- -- Fundamental Property

-- inv-Irred-fold :
--   Irred (fold e) →
--   Irred e
-- inv-Irred-fold irred-fold-e (e' , e↪e') = irred-fold-e (fold e' , ξ-fold e↪e')

-- inv-↪^-fold :
--   fold e ↪^[ k ] e' →
--   Irred e' →
--   ∃[ e'' ] e ↪^[ k ] e'' × Irred e'' × e' ≡ fold e''
-- inv-↪^-fold ↪-refl irred-folde = _ , ↪-refl , inv-Irred-fold irred-folde , refl
-- inv-↪^-fold (↪-step (ξ-fold e↪e′) fold-e′↪^e″) irred-e″ with inv-↪^-fold fold-e′↪^e″ irred-e″
-- ... | e‴ , e′↪ʲe‴ , irred-e‴ , e′≡folde‴ = e‴ , ↪-step e↪e′ e′↪ʲe‴ , irred-e‴ , e′≡folde‴

-- -- Those lemmas are only problematic because of cbv:
-- -- `fold e` is a value if `e` is a value,
-- -- To prove that `e` is a value we require a recursive call with j < k,
-- -- hence we need `∀ k → e ∈𝕍 k ⟦ t ⟧ᵢ` as assumption...

-- -- 𝕍→Irred : e ∈𝕍 suc k ⟦ t ⟧ᵢ → Irred^ (suc k) e
-- -- 𝕍→Irred (𝕍-⇒ p) (e' , ↪-step () q)
-- -- 𝕍→Irred {k = .zero} (𝕍-µ {v = v} p) (.(fold _) , ↪-step (ξ-fold x) ↪-refl) = {!p (s≤s z≤n)!}
-- -- 𝕍→Irred {k = .(suc _)} (𝕍-µ {v = v} p) (e' , ↪-step (ξ-fold x) (↪-step x₁ q)) = {!!}

-- -- 𝕍→Irred : e ∈𝕍 k ⟦ t ⟧ᵢ → Irred^ (suc k) e
-- -- 𝕍→Irred (𝕍-⇒ p) (e' , ↪-step () q)
-- -- 𝕍→Irred {k = zero} (𝕍-µ {v = v} p) (.(fold _) , ↪-step (ξ-fold v→e'') ↪-refl) = {!!}
-- -- 𝕍→Irred {k = suc k} (𝕍-µ {v = v} p) (e' , ↪-step (ξ-fold v→e'') folde''→ᵏe') = {!!}
-- -- -- 𝕍→Irred (𝕍-µ {v = v} p) (e' , ↪-step (ξ-fold v→e'') folde''→ᵏe') = {!!}
-- -- -- 𝕍→Irred (𝕍-µ {v = v} p) (e' , ↪-step (ξ-fold v→e'') e₂→ᵏe') with inv-↪^-fold - = {!!}

-- -- 𝕍→Irred : e ∈𝕍 k ⟦ t ⟧ᵢ → Irred^ k e
-- -- 𝕍→Irred (𝕍-⇒ p) (.(λx _) , ↪-refl) = {!p z≤n!}
-- -- 𝕍→Irred (𝕍-µ {v = v} p) (e' , q) = {!!}

-- -- 𝕍→Irred (𝕍-µ {v = v} p) (.(fold _) , ξ-fold v→e') = 𝕍→Irred {!!} {!!}

-- -- 𝕍→Irred : e ∈𝕍 k ⟦ t ⟧ᵢ → Irred e
-- -- 𝕍→Irred (𝕍-⇒ p) (e' , ())
-- -- 𝕍→Irred (𝕍-µ {v = v} p) (.(fold _) , ξ-fold v→e') = 𝕍→Irred {!!} {!!}

-- -- 𝕍→Value : e ∈𝕍 k ⟦ t ⟧ᵢ → Value e
-- -- 𝕍→Value (𝕍-⇒ p) = λxe
-- -- 𝕍→Value (𝕍-µ p) = fold (𝕍→Value {!p!})

-- 𝕍→Value : (∀ k → e ∈𝕍 k ⟦ t ⟧) → Value e
-- 𝕍→Value {e = λx e}     {t = t₁ ⇒ t₂} f = λxe
-- 𝕍→Value {e = fold e}   {t = µα t}    f = fold (𝕍→Value {e = e} λ k →
--                                            let folde∈𝕍sk = Rec.unfold-∈𝕍 {k = suc k} {e = fold e} {t = µα t} (f (suc k)) in
--                                            folde∈𝕍sk (k < suc k by (≤-refl {suc k})))
-- 𝕍→Value {e = λx e}     {t = 𝟘}       f = ⊥-elim (f 0)
-- 𝕍→Value {e = λx e}     {t = µα t}    f = ⊥-elim (f 0)
-- 𝕍→Value {e = e₁ · e₂}  {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- 𝕍→Value {e = e₁ · e₂}  {t = 𝟘}       f = ⊥-elim (f 0)
-- 𝕍→Value {e = e₁ · e₂}  {t = µα t}    f = ⊥-elim (f 0)
-- 𝕍→Value {e = fold e}   {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- 𝕍→Value {e = fold e}   {t = 𝟘}       f = ⊥-elim (f 0)
-- 𝕍→Value {e = unfold e} {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- 𝕍→Value {e = unfold e} {t = 𝟘}       f = ⊥-elim (f 0)
-- 𝕍→Value {e = unfold e} {t = µα t}    f = ⊥-elim (f 0)

-- Value→Irred : Value e → Irred e
-- Value→Irred {µ} {.(λx e)} (λxe {e = e}) (e' , ())
-- Value→Irred {µ} {.(fold e)} (fold {e = e} val-e) (.(fold e') , ξ-fold {e' = e'} e↪e') = Value→Irred val-e (e' , e↪e')
-- Value→Irred {µ} {e} (neutral x) = {!irrelevant!}

-- -- Not sure if true in general! (requires ∀ k in assumption?)
-- 𝕍→𝔼 : e ∈𝕍 k ⟦ t ⟧ᵢ → e ∈𝔼 k ⟦ t ⟧ᵢ
-- 𝕍→𝔼 {.(λx _)}   {k} {.(t₁ ⇒ t₂)} (𝕍-⇒ {t₁ = t₁} {t₂ = t₂} p) =
--   𝔼 (λ {j} {e'} j<k λxe↪*e' irred-e' →
--     e' ∈𝕍 k ∸ j ⟦ t₁ ⇒ t₂ ⟧ᵢ
--   by {!contra λxe↪*e' irred-e'!})
-- 𝕍→𝔼 {.(fold v)} {k} {.(µα t)}  (𝕍-µ {v = v} {t = t} p) =
--     fold v ∈𝔼 k ⟦ µα t ⟧ᵢ
--   by 𝔼 λ where
--     {zero} {e'} j<k foldv↪*e' irred-e' →
--         e' ∈𝕍 k ∸ zero ⟦ µα t ⟧ᵢ
--       by {!p (k ∸ j)!} -- this works if we match on j! if j is zero, we're almost done by assumption!
--     {suc j} {e'} j<k foldv↪*e' irred-e' →
--         e' ∈𝕍 k ∸ suc j ⟦ µα t ⟧ᵢ
--       by let (e'' , v→ˢʲe'' , irred-e'' , e'≡folde'') = inv-↪^-fold foldv↪*e' irred-e' in
--          subst {!!} {!!} (
--         fold e'' ∈𝕍 k ∸ suc j ⟦ µα t ⟧ᵢ
--       by let pp = {!𝕍→𝔼 (p (k ∸ suc j < k by ?))!} in
--          {!unwrap-𝔼 pp!}
--          )


-- ⊢→⊧ᵢ :
--   Γ ⊢ e ∶ t →
--   Γ ⊧ᵢ e ∶ t

-- ⊢→⊧ᵢ {µ} {Γ} {.(` x)}      {t}        (τ-` {x = x} refl) =
--     Γ ⊧ᵢ ` x ∶ t
--   by λ {k} {σ} σ∈𝔾 →
--     σ 𝕖 x ∈𝔼 k ⟦ t ⋯ σ ⟧ᵢ
--   by 𝕍→𝔼 (σ∈𝔾 x)

-- ⊢→⊧ᵢ {µ} {Γ} {.(λx e)}     {.(t₁ ⇒ t₂)} (τ-λ {t₁ = t₁} {e = e} {t₂ = t₂} ⊢e) =
--     Γ ⊧ᵢ λx e ∶ t₁ ⇒ t₂
--   by λ {k} {σ} σ∈𝔾⟦Γ⟧ →
--     λx (e ⋯ σ ↑ₛ 𝕖) ∈𝔼 k ⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧ᵢ
--   by 𝕍→𝔼 (
--     λx (e ⋯ σ ↑ₛ 𝕖) ∈𝕍 k ⟦ (t₁ ⋯ σ) ⇒ (t₂ ⋯ σ) ⟧ᵢ
--   by 𝕍-⇒ λ {j} {v} j≤k v∈𝕍⟦t₁⋯σ⟧ →
--     e ⋯ σ ↑ₛ 𝕖 ⋯ ⦅ v ⦆ ∈𝔼 j ⟦ t₂ ⋯ σ ⟧ᵢ
--   by subst₂ (_∈𝔼 j ⟦_⟧ᵢ) (sym (⋯↑⋯⦅⦆-is-⋯,ₛ e v σ)) (wk-cancels-,ₛ t₂ σ v) (
--     (e ⋯ (σ ,ₛ v)) ∈𝔼 j ⟦ t₂ ⋯ wk ⋯ (σ ,ₛ v) ⟧ᵢ
--   by ⊢→⊧ᵢ ⊢e (
--     σ ,ₛ v ∈𝔾 j ⟦ Γ ,, t₁ ⟧ᵢ
--   by 𝕍ᵣ→𝕍ᵢ v∈𝕍⟦t₁⋯σ⟧ ∷𝔾ᵢ monotonicity-𝔾ᵢ j≤k σ∈𝔾⟦Γ⟧)))

-- ⊢→⊧ᵢ {µ} {Γ} {.(_ · _)}    {t}        (τ-· ⊢e₁ ⊢e₂) = {!!}

-- ⊢→⊧ᵢ {µ} {Γ} {.(fold e)}   {.(µα t)}  (τ-fold {e = e} {t = t} ⊢e) =
--     Γ ⊧ᵢ fold e ∶ µα t
--   by λ {k} {σ} σ∈𝔾 →
--     fold (e ⋯ σ) ∈𝔼 k ⟦ (µα t) ⋯ σ ⟧ᵢ
--   by 𝔼 λ {j} {e'} j<k [folde⋯σ]↪ʲ[e'] irred-e' →
--     e' ∈𝕍 k ∸ j ⟦ (µα t) ⋯ σ ⟧ᵢ
--   by let (e'' , e⋯σ↪e'' , irred-e'' , e'≡folde'') = inv-↪^-fold [folde⋯σ]↪ʲ[e'] irred-e' in -- TODO: if we would be able to match on the eq, stuff would be simpler...
--      let [e⋯σ]∈𝔼ᵏ = e ⋯ σ ∈𝔼 k ⟦ t ⋯ ⦅ µα t ⦆ ⋯ σ ⟧ᵢ by ⊢→⊧ᵢ ⊢e σ∈𝔾 in
--      let e''∈𝕍[k-j] = e'' ∈𝕍 k ∸ j ⟦ t ⋯ ⦅ µα t ⦆ ⋯ σ ⟧ᵢ by unwrap-𝔼 [e⋯σ]∈𝔼ᵏ j<k e⋯σ↪e'' irred-e'' in
--      subst (_∈𝕍 _ ⟦ _ ⟧ᵢ) (sym e'≡folde'') (
--     fold e'' ∈𝕍 k ∸ j ⟦ (µα t) ⋯ σ ⟧ᵢ
--   by 𝕍-µ λ {i} i<k∸j →
--     e'' ∈𝕍 i ⟦ t ⋯ σ ↑ 𝕥 ⋯ ⦅ (µα t) ⋯ σ ⦆ ⟧ᵢ
--   by monotonicity-𝕍ᵢ (i ≤ k ∸ j by <⇒≤ i<k∸j) (
--     e'' ∈𝕍 k ∸ j ⟦ t ⋯ σ ↑ 𝕥 ⋯ ⦅ (µα t) ⋯ σ ⦆ ⟧ᵢ
--   by subst (_ ∈𝕍 _ ⟦_⟧ᵢ) (dist-⦅⦆ₛ-⋯ₛ t (µα t) σ) (
--     e'' ∈𝕍 k ∸ j ⟦ t ⋯ ⦅ µα t ⦆ ⋯ σ ⟧ᵢ
--   by e''∈𝕍[k-j] )))

-- ⊢→⊧ᵢ {µ} {Γ} {.(unfold e)} {.(t ⋯ ⦅ µα t ⦆)} (τ-unfold {e = e} {t = t} ⊢e) =
--   {!!}
-- -- ⊢→⊧ᵢ {µ} {Γ} {.(unfold e)} {.(t ⋯ ⦅ µα t ⦆)} (τ-unfold {e = e} {t = t} ⊢e) =
-- --     Γ ⊧ᵢ unfold e ∶ t ⋯ ⦅ µα t ⦆
-- --   by λ {k} {σ} σ∈𝔾 →
-- --     unfold (e ⋯ σ) ∈𝔼 k ⟦ t ⋯ ⦅ µα t ⦆ ⋯ σ ⟧ᵢ
-- --   by 𝔼 λ {j} {e'} j<k [unfolde⋯σ]↪ʲ[e'] irred-e' →
-- --     e' ∈𝕍 k ∸ j ⟦ t ⋯ ⦅ µα t ⦆ ⋯ σ ⟧ᵢ
-- --   by let e⋯σ∈𝔼ᵏ = e ⋯ σ ∈𝔼 k ⟦ (µα t) ⋯ σ ⟧ᵢ by ⊢→⊧ᵢ ⊢e σ∈𝔾 in
-- --      -- requires inversion lemma
-- --      let e⋯σ→ʲe'' = (e ⋯ σ) ↪^[ j ] e'' by {!!} in
-- --      subst (e' ∈𝕍 k ∸ j ⟦_⟧ᵢ) (dist-⦅⦆ₛ-⋯ₛ {!t!} {!!} {!!}) (
-- --     e' ∈𝕍 k ∸ j ⟦ (µα t) ⋯ σ ⟧ᵢ
-- --   by unwrap-𝔼 e⋯σ∈𝔼ᵏ {j = j} j<k e⋯σ→ʲe' irred-e'
-- --      )

-- -- ⊢→⊧ᵢ (τ-` x)       = {!!}
-- -- ⊢→⊧ᵢ (τ-λ ⊢e)      = {!!}
-- -- ⊢→⊧ᵢ (τ-· ⊢e₁ ⊢e₂) = {!!}
-- -- ⊢→⊧ᵢ (τ-fold ⊢e)   =
-- --     Γ ⊧ᵢ fold e ∶
-- -- fold (e ⋯ σ) ∈𝔼 k ⟦ µα (t ⋯ σ S.↑ 𝕥) ⟧ᵢ
-- -- {!!}
-- -- ⊢→⊧ᵢ (τ-unfold ⊢e) = {!!}

-- ⊢→⊧ :
--   Γ ⊢ e ∶ t →
--   Γ ⊧ e ∶ t
-- ⊢→⊧ (τ-` x)       = {!!}
-- ⊢→⊧ (τ-λ ⊢e)      = {!!}
-- ⊢→⊧ (τ-· ⊢e₁ ⊢e₂) = {!!}
-- ⊢→⊧ (τ-fold ⊢e)   {k} σ∈𝔾 = {!!}
-- ⊢→⊧ (τ-unfold ⊢e) = {!!}




-- -- Safe : [] ⊢ 𝕖 → Set
-- -- Safe e = ∀ e' → e ↪* e' → Value e' ⊎ Red e'

-- -- Red? : ∀ (e : [] ⊢ 𝕖) → Dec (Red e)
-- -- Red? e = {!!}

-- -- -- TODO: use func rep for 𝔾 or remove.
-- -- idₛ∈𝔾⟦∅⟧ : idₛ ∈𝔾 k ⟦ ∅ ⟧
-- -- idₛ∈𝔾⟦∅⟧ = []

-- -- 𝕍ᵢ→Value : e ∈𝕍 k ⟦ t ⟧ᵢ → Value e
-- -- 𝕍ᵢ→Value (𝕍-⇒ x) = λxe
-- -- 𝕍ᵢ→Value {e = fold v} {k = k} {t = µα t} (𝕍-µ {v = v} foldv∈𝕍) =
-- --   let foldv∈𝕍ᵣ = v ∈𝕍 k ⟦ t ⋯ ⦅ µα t ⦆ ⟧  by {!Rec.unfold-∈𝕍 foldv∈𝕍!} in
-- --   let foldv∈𝕍ᵢ = v ∈𝕍 k ⟦ t ⋯ ⦅ µα t ⦆ ⟧ᵢ by 𝕍ᵣ→𝕍ᵢ foldv∈𝕍ᵣ in
-- --   {!!}
-- --   -- fold (𝕍ᵢ→Value (𝕍ᵣ→𝕍ᵢ foldv∈𝕍))
-- -- -- 𝕍ᵢ→Value {fold e} {k} {µα t}    fold-e∈𝕍⟦t⟧ = fold (𝕍→Value {!fold-e∈𝕍⟦t⟧ {!j<k!}!})

-- -- 𝕍ᵢ→Value' : (∀ k → e ∈𝕍 k ⟦ t ⟧ᵢ) → Value e
-- -- 𝕍ᵢ→Value' = {!!}
-- -- -- 𝕍ᵢ→Value' {e = λx e}     {t = t₁ ⇒ t₂} f = λxe
-- -- -- 𝕍ᵢ→Value' {e = fold e}   {t = µα t}    f = fold (𝕍ᵢ→Value' {e = e} λ k → {!let 𝕍-µ x = f (suc k) in ? !})
-- -- --                                             -- fold (𝕍ᵢ→Value' {e = e} λ k →
-- -- --                                             -- let folde∈𝕍sk = Rec.unfold-∈𝕍 {k = suc k} {e = fold e} {t = µα t} (f (suc k)) in
-- -- --                                             -- folde∈𝕍sk (k < suc k by (≤-refl {suc k})))
-- -- -- -- 𝕍ᵢ→Value' {e = λx e}     {t = 𝟘}       f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = λx e}     {t = µα t}    f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = e₁ · e₂}  {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = e₁ · e₂}  {t = 𝟘}       f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = e₁ · e₂}  {t = µα t}    f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = fold e}   {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = fold e}   {t = 𝟘}       f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = unfold e} {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = unfold e} {t = 𝟘}       f = ⊥-elim (f 0)
-- -- -- -- 𝕍ᵢ→Value' {e = unfold e} {t = µα t}    f = ⊥-elim (f 0)

-- -- 𝕍→Value' : (∀ k → e ∈𝕍 k ⟦ t ⟧) → Value e
-- -- 𝕍→Value' {e = λx e}     {t = t₁ ⇒ t₂} f = λxe
-- -- 𝕍→Value' {e = fold e}   {t = µα t}    f = fold (𝕍→Value' {e = e} λ k →
-- --                                             let folde∈𝕍sk = Rec.unfold-∈𝕍 {k = suc k} {e = fold e} {t = µα t} (f (suc k)) in
-- --                                             folde∈𝕍sk (k < suc k by (≤-refl {suc k})))
-- -- 𝕍→Value' {e = λx e}     {t = 𝟘}       f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = λx e}     {t = µα t}    f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = e₁ · e₂}  {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = e₁ · e₂}  {t = 𝟘}       f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = e₁ · e₂}  {t = µα t}    f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = fold e}   {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = fold e}   {t = 𝟘}       f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = unfold e} {t = t ⇒ t₁}  f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = unfold e} {t = 𝟘}       f = ⊥-elim (f 0)
-- -- 𝕍→Value' {e = unfold e} {t = µα t}    f = ⊥-elim (f 0)

-- -- 𝕍→Value : e ∈𝕍 k ⟦ t ⟧ → Value e
-- -- 𝕍→Value {λx e}   {k} {t₁ ⇒ t₂} λxe∈𝕍⟦t⟧    = λxe
-- -- 𝕍→Value {fold e} {k} {µα t}    fold-e∈𝕍⟦t⟧ = fold (𝕍→Value {!fold-e∈𝕍⟦t⟧ {!j<k!}!})

-- -- ⊧ᵢ→safe :
-- --   ∅ ⊧ᵢ e ∶ t →
-- --   Safe e
-- -- ⊧ᵢ→safe {e} {t} ⊧e e′ e↪*e′ with Red? e′
-- -- ... | yes red-e′                  = inj₂ red-e′
-- -- ... | no irred-e′ rewrite ⋯-idₛ e = inj₁
-- --   let (k , e↪*[k]e′) = ↪*→↪^ e↪*e′ in
-- --   let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e {k = k} [] in
-- --   let e∈𝔼⟦t⟧ = subst₂ (_∈𝔼 k ⟦_⟧ᵢ) (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
-- --   𝕍→Value' {!!}
-- --   -- (𝕍→Value' (λ k →
-- --   --   let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e {k = suc k} [] in
-- --   --   let e∈𝔼⟦t⟧ = subst₂ (_∈𝔼 suc k ⟦_⟧ᵢ) (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
-- --   --   let e′∈𝕍⟦t⟧ = unwrap-𝔼 e∈𝔼⟦t⟧ (k < suc k by {!!}) {!e↪*[k]e′!} irred-e′ in
-- --   --   {!e′∈𝕍⟦t⟧!}))
-- --   -- (𝕍→Value' (λ k →
-- --   --   let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e {k = suc k} [] in
-- --   --   let e∈𝔼⟦t⟧ = subst₂ (_∈𝔼 suc k ⟦_⟧ᵢ) (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
-- --   --   let e′∈𝕍⟦t⟧ = unwrap-𝔼 e∈𝔼⟦t⟧ (k < suc k by {!!}) {!e↪*[k]e′!} irred-e′ in
-- --   --   {!e′∈𝕍⟦t⟧!}))

-- -- ⊧→safe :
-- --   ∅ ⊧ e ∶ t →
-- --   Safe e
-- -- ⊧→safe {e} {t} ⊧e e′ e↪*e′ with Red? e′
-- -- ... | yes red-e′                  = inj₂ red-e′
-- -- ... | no irred-e′ rewrite ⋯-idₛ e = inj₁
-- --   let (k , e↪*[k]e′) = ↪*→↪^ e↪*e′ in
-- --   let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e {k = k} idₛ∈𝔾⟦∅⟧ in
-- --   let e∈𝔼⟦t⟧ = subst₂ (_∈𝔼 k ⟦_⟧) (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
-- --   let e′∈𝕍⟦t⟧ = e∈𝔼⟦t⟧ {!impossible!} e↪*[k]e′ irred-e′ in
-- --   𝕍→Value' (λ k →
-- --     let e⋯id∈𝔼⟦t⋯id⟧ = ⊧e {k = k} idₛ∈𝔾⟦∅⟧ in
-- --     let e∈𝔼⟦t⟧ = subst₂ (_∈𝔼 k ⟦_⟧) (⋯-idₛ e) (⋯-idₛ t) e⋯id∈𝔼⟦t⋯id⟧ in
-- --     let e′∈𝕍⟦t⟧ = e∈𝔼⟦t⟧ {!impossible!} e↪*[k]e′ irred-e′ in
-- --     {!e′∈𝕍⟦t⟧!})
-- --   -- let e′∈𝕍⟦t⟧ = e∈𝔼⟦t⟧ e↪*e′ irred-e′ in
-- --   -- 𝕍→Value e′∈𝕍⟦t⟧


