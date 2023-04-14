module Kitty.Util.SubstSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)
open import Level renaming (suc to lsuc; zero to 0ℓ) using (Level; _⊔_; Setω; Lift; lift; lower)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Relation.Nullary using (Dec; yes; no; _because_)
open import Data.Empty using (⊥; ⊥-elim)

variable ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ : Level

data _≡?_ {ℓ} {A : Set ℓ} (a₁ a₂ : A) : Set ℓ where
  tt : a₁ ≡? a₂

mutual
  data Type ℓ : Set (lsuc ℓ) where
    `_ : (A : Set ℓ) → Type ℓ
    `∀ : (A : Type ℓ) → (⟦ A ⟧ → Type ℓ) → Type ℓ
    -- `≡ : (A : Type ℓ) → (a₁ a₂ : ⟦ A ⟧) → Type ℓ

  ⟦_⟧ : Type ℓ → Set ℓ
  ⟦ ` A   ⟧      = A
  ⟦ `∀ A B ⟧     = ∀ (a : ⟦ A ⟧) → ⟦ B a ⟧
  -- ⟦ `≡ A a₁ a₂ ⟧ = a₁ ≡ a₂

data Term ℓ : Set (lsuc ℓ) where
  `_∋_#_ : ∀ (A : Type ℓ) → (a : ⟦ A ⟧) → (i : ℕ) → Term ℓ
  _·_ : (t₁ t₂ : Term ℓ) → Term ℓ
  `subst : (t₁ t₂ t≡ t : Term ℓ) → Term ℓ
  -- `eq : Term ℓ → Term ℓ → Term ℓ

-- Subterm Relation
-- TODO: Derive for Kitty Terms!
data _≤ₜ_ {ℓ} (t' : Term ℓ) : (t : Term ℓ) → Set ℓ where
  ≤-refl :
    t' ≤ₜ t'
  ≤-·₁ : ∀ {t₁ t₂ : Term ℓ} →
    t' ≤ₜ t₁ →
    t' ≤ₜ (t₁ · t₂)
  ≤-·₂ : ∀ {t₁ t₂ : Term ℓ} →
    t' ≤ₜ t₂ →
    t' ≤ₜ (t₁ · t₂)
  ≤-subst₁ : ∀ {t₁ t₂ t≡ t : Term ℓ} →
    t' ≤ₜ t₁ →
    t' ≤ₜ (`subst t₁ t₂ t≡ t)
  ≤-subst₂ : ∀ {t₁ t₂ t≡ t : Term ℓ} →
    t' ≤ₜ t₂ →
    t' ≤ₜ (`subst t₁ t₂ t≡ t)
  ≤-subst₃ : ∀ {t₁ t₂ t≡ t : Term ℓ} →
    t' ≤ₜ t≡ →
    t' ≤ₜ (`subst t₁ t₂ t≡ t)
  ≤-subst₄ : ∀ {t₁ t₂ t≡ t : Term ℓ} →
    t' ≤ₜ t →
    t' ≤ₜ (`subst t₁ t₂ t≡ t)
  -- ≤-eq₁ : ∀ {t₁ t₂ : Term ℓ} →
  --   t' ≤ₜ t₁ →
  --   t' ≤ₜ (`eq t₁ t₂)
  -- ≤-eq₂ : ∀ {t₁ t₂ : Term ℓ} →
  --   t' ≤ₜ t₂ →
  --   t' ≤ₜ (`eq t₁ t₂)

RespId : Term ℓ → Set _
RespId {ℓ} t = ∀ {A : Type ℓ} {a₁ a₂ : ⟦ A ⟧} {i₁ i₂ : ℕ} →
  (` A ∋ a₁ # i₁) ≤ₜ t →
  (` A ∋ a₂ # i₂) ≤ₜ t →
  i₁ ≡ i₂ →
  a₁ ≡ a₂

data _≤ₜ[_,_] {ℓ} (t' t₁ t₂ : Term ℓ) : Set ℓ where
  left  : t' ≤ₜ t₁ → t' ≤ₜ[ t₁ , t₂ ]
  right : t' ≤ₜ t₂ → t' ≤ₜ[ t₁ , t₂ ]

RespId' : Term ℓ → Term ℓ → Set _
RespId' {ℓ} t₁ t₂ = ∀ {A : Type ℓ} {a₁ a₂ : ⟦ A ⟧} {i₁ i₂ : ℕ} →
  (` A ∋ a₁ # i₁) ≤ₜ[ t₁ , t₂ ] →
  (` A ∋ a₂ # i₂) ≤ₜ[ t₁ , t₂ ] →
  i₁ ≡ i₂ →
  a₁ ≡ a₂

lookup : ∀ {ℓ} (i : ℕ) (t : Term ℓ) →
  Maybe (Σ[ A ∈ Type ℓ ] Σ[ a ∈ ⟦ A ⟧ ] (` A ∋ a # i) ≤ₜ t)
lookup i (` A ∋ a # j) with i ≟ j
...                         | yes refl = some (A , a , ≤-refl)
...                         | no neq = none
lookup i (t₁ · t₂)          with lookup i t₁   | lookup i t₂
...                         | some (A , a , ≤) | _                = some (A , a , ≤-·₁ ≤)
...                         | _                | some (A , a , ≤) = some (A , a , ≤-·₂ ≤)
...                         | _                | _                = none
lookup i (`subst t₁ t₂ t₃ t₄)
 with lookup i t₁
... | some (A , a , ≤) = some (A , a , ≤-subst₁ ≤)
... | none
 with lookup i t₂
... | some (A , a , ≤) = some (A , a , ≤-subst₂ ≤)
... | none
 with lookup i t₃
... | some (A , a , ≤) = some (A , a , ≤-subst₃ ≤)
... | none
 with lookup i t₄
... | some (A , a , ≤) = some (A , a , ≤-subst₄ ≤)
... | none             = none

lookup₂ : ∀ {ℓ} (i : ℕ) (t₁ t₂ : Term ℓ) →
  Maybe (Σ[ A ∈ Type ℓ ] Σ[ a ∈ ⟦ A ⟧ ] (` A ∋ a # i) ≤ₜ[ t₁ , t₂ ])
lookup₂ i t₁ t₂ with lookup i t₁      | lookup i t₂
...                | some (A , a , ≤) | _                = some (A , a , left ≤)
...                | _                | some (A , a , ≤) = some (A , a , right ≤)
...                | _                | _                = none

lookup₂' : ∀ {ℓ} (i : ℕ) (t₁ t₂ : Term ℓ) →
  Maybe (Σ[ A ∈ Type ℓ ] ⟦ A ⟧)
lookup₂' i t₁ t₂ with lookup₂ i t₁ t₂
... | some (A , a , _) = some (A , a)
... | none             = none

RespId'' : Term ℓ → Term ℓ → Set _
RespId'' {ℓ} t₁ t₂ = ∀ {A : Type ℓ} {a₁ a₂ : ⟦ A ⟧} {i₁ i₂ : ℕ} →
  lookup₂' i₁ t₁ t₂ ≡ some (A , a₁) →
  lookup₂' i₂ t₁ t₂ ≡ some (A , a₂) →
  i₁ ≡ i₂ →
  a₁ ≡ a₂

≤→lookup : ∀ {t : Term ℓ} {A : Type ℓ} {a : ⟦ A ⟧} {i : ℕ} →
  (` A ∋ a # i) ≤ₜ t →
  Σ[ ≤ ∈ (` A ∋ a # i) ≤ₜ t ] lookup i t ≡ some (A , a , ≤)
  
≤→lookup {i = i} ≤-refl with i ≟ i
...                        | yes refl = ≤-refl , refl
...                        | no ¬refl = ⊥-elim (¬refl refl)
≤→lookup (≤-·₁ ≤) with ≤→lookup ≤
... | ≤' , eq rewrite eq = ≤-·₁ ≤' , refl
≤→lookup {i = i} (≤-·₂ {t₁ = t₁} ≤) with lookup i t₁ | ≤→lookup ≤
... | none              | ≤'  , eq rewrite eq = ≤-·₂ ≤' , refl
... | some (A , a , ≤') | ≤'' , eq rewrite eq = {!≤-·₁ ≤'!} , {!refl!}
≤→lookup (≤-subst₁ ≤) = {!!}
≤→lookup (≤-subst₂ ≤) = {!!}
≤→lookup (≤-subst₃ ≤) = {!!}
≤→lookup (≤-subst₄ ≤) = {!!}

RespId''→' : {t₁ t₂ : Term ℓ} → RespId'' t₁ t₂ → RespId' t₁ t₂ 
RespId''→' R {i₁ = i₁} {i₂} le1 le2 i₁≡i₂ = {!!}

≤ₜ-trans : ∀ {ℓ} {t₁ t₂ t₃ : Term ℓ} →
  t₁ ≤ₜ t₂ →
  t₂ ≤ₜ t₃ →
  t₁ ≤ₜ t₃
≤ₜ-trans le1 ≤-refl         = le1
≤ₜ-trans le1 (≤-·₁ le2)     = ≤-·₁ (≤ₜ-trans le1 le2)
≤ₜ-trans le1 (≤-·₂ le2)     = ≤-·₂ (≤ₜ-trans le1 le2)
≤ₜ-trans le1 (≤-subst₁ le2) = ≤-subst₁ (≤ₜ-trans le1 le2)
≤ₜ-trans le1 (≤-subst₂ le2) = ≤-subst₂ (≤ₜ-trans le1 le2)
≤ₜ-trans le1 (≤-subst₃ le2) = ≤-subst₃ (≤ₜ-trans le1 le2)
≤ₜ-trans le1 (≤-subst₄ le2) = ≤-subst₄ (≤ₜ-trans le1 le2)

≤ₜ-trans' : ∀ {ℓ} {t₁ t₂₁ t₂₂ t₃₁ t₃₂ : Term ℓ} →
  t₁ ≤ₜ[ t₂₁ , t₂₂ ] →
  t₂₁ ≤ₜ[ t₃₁ , t₃₂ ] →
  t₂₂ ≤ₜ[ t₃₁ , t₃₂ ] →
  t₁ ≤ₜ[ t₃₁ , t₃₂ ]
≤ₜ-trans' (left le1) (left le2) le3 = left (≤ₜ-trans le1 le2)
≤ₜ-trans' (left le1) (right le2) le3 = right (≤ₜ-trans le1 le2)
≤ₜ-trans' (right le1) le2 (left le3) = left (≤ₜ-trans le1 le3)
≤ₜ-trans' (right le1) le2 (right le3) = right (≤ₜ-trans le1 le3)

dec-eq : ∀ {ℓ} {t t₁ t₂ : Term ℓ} →
  RespId t →
  t₁ ≤ₜ t →
  t₂ ≤ₜ t →
  Dec (t₁ ≡ t₂)
dec-eq R t₁< t₂< = {!t₁<!}

dec-eq' : ∀ {ℓ} {t₁' t₂' t₁ t₂ : Term ℓ} →
  RespId' t₁' t₂' →
  t₁ ≤ₜ[ t₁' , t₂' ] →
  t₂ ≤ₜ[ t₁' , t₂' ] →
  Dec (t₁ ≡ t₂)
dec-eq' R t₁< t₂< = {!t₁<!}

≤ₜ-pres-RespId : ∀ {t₁ t₂ : Term ℓ} →
  t₁ ≤ₜ t₂ →
  RespId t₂ →
  RespId t₁
≤ₜ-pres-RespId le R le₁ le₂ ieq = R (≤ₜ-trans le₁ le) (≤ₜ-trans le₂ le) ieq

≤ₜ-pres-RespId' : ∀ {t₁' t₂' t₁ t₂ : Term ℓ} →
  t₁  ≤ₜ[ t₂ , t₂' ] →
  t₁' ≤ₜ[ t₂ , t₂' ] →
  RespId' t₂ t₂' →
  RespId' t₁ t₁'
≤ₜ-pres-RespId' le1 le1' R le2 le2' i₁≡i₂ = R (≤ₜ-trans' le2 le1 le1') (≤ₜ-trans' le2' le1 le1') i₁≡i₂

data _⊢_∋_ {ℓ} : Term ℓ → (A : Type ℓ) → ⟦ A ⟧ → Set (lsuc ℓ) where
  ⊢` : ∀ {i} (A : Type ℓ) (a : ⟦ A ⟧) → (` A ∋ a # i) ⊢ A ∋ a
  ⊢· : ∀ {A : Type ℓ} {B : ⟦ A ⟧ → Type ℓ} {tf f ta a} {Ba fa} →
    tf ⊢ `∀ A B ∋ f →
    ta ⊢ A ∋ a →
    (Ba-eq : Ba ≡ B a) →
    fa ≡ f a →
    (tf · ta) ⊢ Ba ∋ subst id (sym (cong ⟦_⟧ Ba-eq)) fa
  ⊢subst : ∀ {A : Type ℓ} {R : ⟦ A ⟧ → Type ℓ} {a b ta tb tra ra teq eq} →
    ta  ⊢ A ∋ a →
    tb  ⊢ A ∋ b →
    teq ⊢ (` (a ≡ b)) ∋ eq →
    tra ⊢ (R a) ∋ ra →
    `subst ta tb teq tra ⊢ (R b) ∋ (subst (λ a → ⟦ R a ⟧) eq ra)

open import Data.List
open import Data.List.Relation.Unary.All as All

infixr 5 _++A_
_++A_ : ∀ {A : Set ℓ₁} {P : A → Set ℓ₂} {xs ys} (pxs : All P xs) (pys : All P ys) → All P (xs ++ ys)
[]         ++A pys = pys
(px ∷ pxs) ++A pys = px ∷ (pxs ++A pys)

-- open import Data.List.Membership.Propositional
-- Eqs : ∀ ℓ → Set (lsuc ℓ)
-- Eqs ℓ = List (Term ℓ × Term ℓ × Term ℓ)


record Eq ℓ : Set (lsuc ℓ) where 
  constructor eq'
  field
    lhs rhs lhs≡rhs : Term ℓ

open Eq

record Eq≤ {ℓ} (t₁ t₂ : Term ℓ) (eq : Eq ℓ) : Set (lsuc ℓ) where 
  constructor eq≤
  field
    lhs≤     : lhs eq ≤ₜ[ t₁ , t₂ ]
    rhs≤     : rhs eq ≤ₜ[ t₁ , t₂ ]
    lhs≡rhs≤ : lhs≡rhs eq ≤ₜ[ t₁ , t₂ ]
  open Eq eq public renaming (lhs to ≤-lhs; rhs to ≤-rhs; lhs≡rhs to ≤-lhs≡rhs)

open Eq≤

Eqs : ∀ ℓ → Set (lsuc ℓ)
Eqs ℓ = List (Eq ℓ) 

Eqs≤ : ∀ {ℓ} → List (Eq ℓ) → (t₁ t₂ : Term ℓ) → Set (lsuc ℓ)
Eqs≤ eqs t₁ t₂ = All (Eq≤ t₁ t₂) eqs

lookup-eqs : ∀ {t₁ t₂ : Term ℓ} {eqs : Eqs ℓ} →
  (t : Term ℓ) →
  t ≤ₜ[ t₁ , t₂ ] →
  RespId' t₁ t₂ →
  Eqs≤ eqs t₁ t₂ →
  Maybe (Term ℓ)
lookup-eqs t le R [] = none
lookup-eqs t le R (eq ∷ eqs)
 with dec-eq' R (rhs≤ eq) le
... | no ¬p = lookup-eqs t le R eqs
... | yes p = some (≤-lhs eq)

-- lift-Eq' : ∀ {ℓ} {t₁ t₂ t₁' t₂' : Term ℓ} →
--   t₁ ≤ₜ[ t₁' , t₂' ] →
--   t₂ ≤ₜ[ t₁' , t₂' ] →
--   Eq' t₁ t₂ →
--   Eq' t₁' t₂'
-- lift-Eq' le1 le2 (eq' t₁' t₂' eq t₁'≤ t₂'≤ eq≤) =
--   eq' t₁' t₂' eq (≤ₜ-trans' t₁'≤ le1 le2) (≤ₜ-trans' t₂'≤ le1 le2) (≤ₜ-trans' eq≤ le1 le2)

-- ≤ₜ'-flip : ∀ {t t₁ t₂ : Term ℓ} → t ≤ₜ[ t₁ , t₂ ] → t ≤ₜ[ t₂ , t₁ ]
-- ≤ₜ'-flip (left x) = right x
-- ≤ₜ'-flip (right x) = left x

-- RespId'-flip : ∀ {t₁ t₂ : Term ℓ} → RespId' t₁ t₂ → RespId' t₂ t₁ 
-- RespId'-flip R ≤₁ ≤₂ i₁≡i₂ = R (≤ₜ'-flip ≤₁) (≤ₜ'-flip ≤₂) i₁≡i₂

pullout : ∀ {t₁} {t₂} {A : Type ℓ} {a : ⟦ A ⟧} {eqs : Eqs ℓ} →
  (t : Term ℓ) →
  t ⊢ A ∋ a →
  t ≤ₜ[ t₁ , t₂ ] →
  Eqs≤ eqs t₁ t₂ →
  RespId' t₁ t₂ →
  ∃[ eqs ] Eqs≤ eqs t₁ t₂ × Term ℓ
pullout t@(` A ∋ a # i) ⊢t le eqs R with lookup-eqs t le R eqs
... | some t₂ = _ , [] , t₂
... | none    = _ , [] , t
  -- TODO: we probably need to apply all matching eqs, since we're pulling out multiple subs
pullout (t₁ · t₂) (⊢· ⊢t₁ ⊢t₂ eq₁ eq₂) le eqs R
 with pullout t₂ ⊢t₂ (≤ₜ-trans' (left (≤-·₂ ≤-refl)) le le) eqs R
... | _ , eqs' , t₂'
 with pullout t₁ ⊢t₁ (≤ₜ-trans' (left (≤-·₁ ≤-refl)) le le) (eqs' ++A eqs) R
... | _ , eqs'' , t₁'
 = _ , eqs' ++A eqs'' , (t₁' · t₂')
pullout (`subst ta tb t₁ t₂) (⊢subst ⊢ta ⊢tb ⊢t₁ ⊢t₂) le eqs R
 with pullout t₂ ⊢t₂ (≤ₜ-trans' (left (≤-subst₄ ≤-refl)) le le) eqs R
... | _ , eqs' , t₂'
 = _ , eq≤
     (≤ₜ-trans' (left (≤-subst₁ ≤-refl)) le le)
     (≤ₜ-trans' (left (≤-subst₂ ≤-refl)) le le)
     (≤ₜ-trans' (left (≤-subst₃ ≤-refl)) le le)
   ∷ eqs' , t₂'

lookup-irrelevant : ∀ {t₁ t₂ t₁' t₂'} (A : Type ℓ) (a : ⟦ A ⟧) i →
  (≤₁ : (` A ∋ a # i) ≤ₜ[ t₁ , t₂ ]) →
  (≤₂ : (` A ∋ a # i) ≤ₜ[ t₁' , t₂' ]) →
  (eqs : Eqs ℓ) →
  (eqs≤₁ : Eqs≤ eqs t₁ t₂) →
  (eqs≤₂ : Eqs≤ eqs t₁' t₂') →
  (R₁ : RespId' t₁ t₂) →
  (R₂ : RespId' t₁' t₂') →
  lookup-eqs (` A ∋ a # i) ≤₁ R₁ eqs≤₁ ≡ lookup-eqs (` A ∋ a # i) ≤₂ R₂ eqs≤₂
lookup-irrelevant = {!!}

pullout-irrelevant : ∀ {t₁ t₂ t₁' t₂'} {A : Type ℓ} {a : ⟦ A ⟧} →
  (t : Term ℓ) →
  (⊢t : t ⊢ A ∋ a) →
  (≤₁ : t ≤ₜ[ t₁ , t₂ ]) →
  (≤₂ : t ≤ₜ[ t₁' , t₂' ]) →
  (eqs : Eqs ℓ) →
  (eqs≤₁ : Eqs≤ eqs t₁ t₂) →
  (eqs≤₂ : Eqs≤ eqs t₁' t₂') →
  (R₁ : RespId' t₁ t₂) →
  (R₂ : RespId' t₁' t₂') →
  proj₂ (proj₂ (pullout t ⊢t ≤₁ eqs≤₁ R₁)) ≡ proj₂ (proj₂ (pullout t ⊢t ≤₂ eqs≤₂ R₂)) ×
  proj₁ (pullout t ⊢t ≤₁ eqs≤₁ R₁) ≡ proj₁ (pullout t ⊢t ≤₂ eqs≤₂ R₂)
pullout-irrelevant (` A ∋ a # i) (⊢` _ _) ≤₁ ≤₂ eqs eqs≤₁ eqs≤₂ R₁ R₂
 with lookup-eqs (` A ∋ a # i) ≤₁ R₁ eqs≤₁
        | lookup-eqs (` A ∋ a # i) ≤₂ R₂ eqs≤₂
        | lookup-irrelevant A a i ≤₁ ≤₂ eqs eqs≤₁ eqs≤₂ R₁ R₂ 
... | some x | some y | refl = refl , refl
... | none   | none   | refl = refl , refl
pullout-irrelevant .(_ · _) (⊢· ⊢t₁ ⊢t₂ Ba-eq fa-eq) ≤₁ ≤₂ eqs eqs≤₁ eqs≤₂ R₁ R₂
 with pullout-irrelevant _ ⊢t₂
       (≤ₜ-trans' (left (≤-·₂ ≤-refl)) ≤₁ ≤₁)
       (≤ₜ-trans' (left (≤-·₂ ≤-refl)) ≤₂ ≤₂)
       _
       eqs≤₁
       eqs≤₂
       R₁
       R₂
... | eqq₁ , eqq₂
 with pullout _ ⊢t₂ (≤ₜ-trans' (left (≤-·₂ ≤-refl)) ≤₁ ≤₁) eqs≤₁ R₁ in P₁₂
... | eqs₂' , eqs≤₂' , t₂'
 with pullout _ ⊢t₂ (≤ₜ-trans' (left (≤-·₂ ≤-refl)) ≤₂ ≤₂) eqs≤₂ R₂ in P₂₂
... | eqs₂'' , eqs≤₂'' , t₂''
 with eqq₁ | eqq₂
... | refl | refl
 with pullout-irrelevant _ ⊢t₁
       (≤ₜ-trans' (left (≤-·₁ ≤-refl)) ≤₁ ≤₁)
       (≤ₜ-trans' (left (≤-·₁ ≤-refl)) ≤₂ ≤₂)
       _
       (eqs≤₂' ++A eqs≤₁)
       (eqs≤₂'' ++A eqs≤₂)
       R₁
       R₂
... | eqq₁ , eqq₂
 with pullout _ ⊢t₁ (≤ₜ-trans' (left (≤-·₁ ≤-refl)) ≤₁ ≤₁) (eqs≤₂' ++A eqs≤₁) R₁ in P₁₁
... | eqs₁' , eqs≤₁' , t₁'
 with pullout _ ⊢t₁ (≤ₜ-trans' (left (≤-·₁ ≤-refl)) ≤₂ ≤₂) (eqs≤₂'' ++A eqs≤₂) R₂ in P₂₁
... | eqs₁'' , eqs≤₁'' , t₁''
 with eqq₁ | eqq₂
... | refl | refl
 = refl , refl
pullout-irrelevant .(`subst _ _ _ _) (⊢subst ⊢ta ⊢tb ⊢t≡ ⊢t) ≤₁ ≤₂ eqs eqs≤₁ eqs≤₂ R₁ R₂
 with pullout-irrelevant _ ⊢t
       (≤ₜ-trans' (left (≤-subst₄ ≤-refl)) ≤₁ ≤₁)
       (≤ₜ-trans' (left (≤-subst₄ ≤-refl)) ≤₂ ≤₂)
       _
       eqs≤₁
       eqs≤₂
       R₁
       R₂
... | eqq₁ , eqq₂
 with pullout _ ⊢t (≤ₜ-trans' (left (≤-subst₄ ≤-refl)) ≤₁ ≤₁) eqs≤₁ R₁ in P₁
... | eqs₁' , eqs≤₁' , t₁'
 with pullout _ ⊢t (≤ₜ-trans' (left (≤-subst₄ ≤-refl)) ≤₂ ≤₂) eqs≤₂ R₂ in P₂
... | eqs₁' , eqs≤₁' , t₁'
 with eqq₁ | eqq₂
... | refl | refl
 = refl , refl

normalize' : ∀ {t} {t₁} {t₂} {A : Type ℓ} {a : ⟦ A ⟧} →
  t ⊢ A ∋ a →
  t ≤ₜ[ t₁ , t₂ ] →
  RespId' t₁ t₂ →
  Term ℓ
normalize' {t = t} ⊢t le R = proj₂ (proj₂ (pullout t ⊢t le [] R))

-- normalize'-R₂ : ∀ {t} {t₁} {t₂} {t₂'} {A : Type ℓ} {a : ⟦ A ⟧} →
--   (⊢t : t ⊢ A ∋ a) →
--   (≤ : t ≤ₜ t₁) →
--   (R : RespId' t₁ t₂) →
--   (R' : RespId' t₁ t₂') →
--   normalize' ⊢t (left ≤) R ≡ normalize' ⊢t (left ≤) R'
-- normalize'-R₂ = {!!}

normalize : Term ℓ → Term ℓ
normalize (` A ∋ a # i)        = ` A ∋ a # i
normalize (t₁ · t₂)            = (normalize t₁) · (normalize t₂)
normalize (`subst ta tb teq t) = normalize t

·-injective : ∀ {tf₁ ta₁ tf₂ ta₂ : Term ℓ} →
  (tf₁ · ta₁) ≡ (tf₂ · ta₂) →
  (tf₁ ≡ tf₂) × (ta₁ ≡ ta₂)
·-injective refl = refl , refl

≡-irrelevant : ∀ {ℓ} {A : Set ℓ} {a b : A} (p q : a ≡ b) → p ≡ q
≡-irrelevant refl refl = refl

solve : ∀ {A₁ A₂ : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧} →
  (R : RespId' t₁ t₂) →
  (⊢t₁ : t₁ ⊢ A₁ ∋ a₁) →
  (⊢t₂ : t₂ ⊢ A₂ ∋ a₂) →
  normalize' ⊢t₁ (left ≤-refl) R ≡ normalize' ⊢t₂ (right ≤-refl) R →
  Σ[ eq ∈ (A₁ ≡ A₂) ] subst id (cong ⟦_⟧ eq) a₁ ≡ a₂
solve R (⊢` A₁ a₁) (⊢` A₂ a₂) refl = refl , refl
solve R (⊢· ⊢tf₁ ⊢ta₁ refl refl) (⊢· ⊢tf₂ ⊢ta₂ refl refl) norm-eq
 with solve (≤ₜ-pres-RespId' (left (≤-·₂ ≤-refl)) (right (≤-·₂ ≤-refl)) R) ⊢ta₁ ⊢ta₂ {!normalize' ⊢ta₁ (left ≤-refl)
      (≤ₜ-pres-RespId' (left (≤-·₂ ≤-refl)) (right (≤-·₂ ≤-refl)) R)!}
... | refl , refl
 with solve (≤ₜ-pres-RespId' (left (≤-·₁ ≤-refl)) (right (≤-·₁ ≤-refl)) R) ⊢tf₁ ⊢tf₂ {!normalize' (⊢· ⊢tf₁ ⊢ta₁ refl refl) (left ≤-refl) R!}
... | refl , refl
 = refl , refl
solve R ⊢t₁ (⊢subst {R = R''} {eq = refl} ⊢ta ⊢tb ⊢t≡ ⊢t₂) norm-eq =
  solve
    (≤ₜ-pres-RespId' (left ≤-refl) (right (≤-subst₄ ≤-refl)) R)
    ⊢t₁ ⊢t₂
    (let R' = (≤ₜ-pres-RespId' (left ≤-refl) (right (≤-subst₄ ≤-refl)) R) in
     begin
      normalize' ⊢t₁ (left ≤-refl) R'
     ≡⟨ proj₁  (pullout-irrelevant _ ⊢t₁ (left ≤-refl) (left ≤-refl) _ [] [] R' R) ⟩
      normalize' ⊢t₁ (left ≤-refl) R
    ≡⟨ norm-eq ⟩
      normalize' (⊢subst {R = R''} ⊢ta ⊢tb ⊢t≡ ⊢t₂) (right ≤-refl) R
    ≡⟨⟩
      proj₂ (proj₂ (pullout _ (⊢subst {R = R''} ⊢ta ⊢tb ⊢t≡ ⊢t₂) (right ≤-refl) [] R))
    ≡⟨⟩
      proj₂ (proj₂ (pullout _ ⊢t₂ (right (≤-subst₄ ≤-refl)) [] R))
    ≡⟨ proj₁ (pullout-irrelevant _ ⊢t₂ (right (≤-subst₄ ≤-refl)) (right ≤-refl) _ [] [] R R') ⟩
      proj₂ (proj₂ (pullout _ ⊢t₂ (right ≤-refl) [] R'))
    ≡⟨⟩
     normalize' ⊢t₂ (right ≤-refl) R'
    ∎)
solve R (⊢subst {R = R''} {eq = refl} ⊢ta ⊢tb ⊢t≡ ⊢t₁) ⊢t₂ norm-eq =
  solve
    (≤ₜ-pres-RespId' (left (≤-subst₄ ≤-refl)) (right ≤-refl) R)
    ⊢t₁ ⊢t₂
    (let R' = (≤ₜ-pres-RespId' (left (≤-subst₄ ≤-refl)) (right ≤-refl) R) in
     begin
       normalize' ⊢t₁ (left ≤-refl) R'
     ≡⟨ proj₁ (pullout-irrelevant _ ⊢t₁ (left ≤-refl) (left (≤-subst₄ ≤-refl)) _ [] [] R' R) ⟩
       normalize' (⊢subst {R = R''} ⊢ta ⊢tb ⊢t≡ ⊢t₁) (left ≤-refl) R
     ≡⟨ norm-eq ⟩
       normalize' ⊢t₂ (right ≤-refl) R
     ≡⟨ proj₁  (pullout-irrelevant _ ⊢t₂ (right ≤-refl) (right ≤-refl) _ [] [] R R') ⟩
       normalize' ⊢t₂ (right ≤-refl) R'
     ∎)

solve' : ∀ {A : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ a₂ : ⟦ A ⟧} →
  (R : RespId' t₁ t₂) →
  (⊢t₁ : t₁ ⊢ A ∋ a₁) →
  (⊢t₂ : t₂ ⊢ A ∋ a₂) →
  normalize' ⊢t₁ (left ≤-refl) R ≡ normalize' ⊢t₂ (right ≤-refl) R →
  a₁ ≡ a₂
solve' R ⊢t₁ ⊢t₂ norm-eq with solve R ⊢t₁ ⊢t₂ norm-eq
... | refl , eqa = eqa

-- solve : ∀ {A₁ A₂ : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧} →
--   RespId' t₁ t₂ →
--   t₁ ⊢ A₁ ∋ a₁ →
--   t₂ ⊢ A₂ ∋ a₂ →
--   normalize t₁ ≡ normalize t₂ →
--   Σ[ eq ∈ (A₁ ≡ A₂) ] subst id (cong ⟦_⟧ eq) a₁ ≡ a₂
-- solve R (⊢` A₁ a₁) (⊢` A₂ a₂) refl = refl , refl
-- solve R (⊢subst {eq = refl} ⊢ta ⊢tb ⊢teq ⊢tra) ⊢t₂ norm-eq
--  = solve (≤ₜ-pres-RespId' (left (≤-subst₄ ≤-refl)) (right ≤-refl) R) ⊢tra ⊢t₂ norm-eq
-- solve R ⊢t₁ (⊢subst {eq = refl} ⊢ta ⊢tb ⊢teq ⊢tra) norm-eq
--  = solve (≤ₜ-pres-RespId' (left ≤-refl) (right (≤-subst₄ ≤-refl)) R) ⊢t₁ ⊢tra norm-eq
-- solve R (⊢· ⊢tf₁ ⊢ta₁ refl refl) (⊢· ⊢tf₂ ⊢ta₂ refl refl) norm-eq
--  with ·-injective norm-eq                   
-- ... | norm-eq-tf , norm-eq-ta
--  with solve (≤ₜ-pres-RespId' (left (≤-·₁ ≤-refl)) (right (≤-·₁ ≤-refl)) R) ⊢tf₁ ⊢tf₂ norm-eq-tf
-- ... | refl , refl
--  with solve (≤ₜ-pres-RespId' (left (≤-·₂ ≤-refl)) (right (≤-·₂ ≤-refl)) R) ⊢ta₁ ⊢ta₂ norm-eq-ta
-- ... | refl , refl
--  = refl , refl

-- solve' : ∀ {A : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ a₂ : ⟦ A ⟧} →
--   RespId' t₁ t₂ →
--   t₁ ⊢ A ∋ a₁ →
--   t₂ ⊢ A ∋ a₂ →
--   normalize t₁ ≡ normalize t₂ →
--   a₁ ≡ a₂
-- solve' R ⊢t₁ ⊢t₂ norm-eq with solve R ⊢t₁ ⊢t₂ norm-eq
-- ... | refl , eqa = eqa

data ITerm {ℓ} : ∀ (A : Type ℓ) → (a : ⟦ A ⟧) → Set (lsuc ℓ) where
  `_∋_#_ : ∀ (A : Type ℓ) → (a : ⟦ A ⟧) → ℕ → ITerm A a
  _·_ : ∀ {A : Type ℓ} {B : ⟦ A ⟧ → Type ℓ} {f a} →
    ITerm (`∀ A B) f →
    ITerm A a →
    ITerm (B a) (f a)
  `subst : ∀ {A : Type ℓ} (R : ⟦ A ⟧ → Type ℓ) {a b ra} {a≡b : a ≡ b} →
    ITerm A a →
    ITerm A b →
    ITerm (` (a ≡ b)) a≡b →
    ITerm (R a) ra →
    ITerm (R b) (subst (λ a → ⟦ R a ⟧) a≡b ra)

pattern `_#_ a i = ` _ ∋ a # i

split : ∀ {ℓ} {A : Type ℓ} {a : ⟦ A ⟧} →
  ITerm A a →
  Σ[ t ∈ Term ℓ ]
    t ⊢ A ∋ a
split (` A ∋ a # i)                     = (` A ∋ a # i) , (⊢` A a)
split (t₁ · t₂) with split t₁ | split t₂
...                | tf , ⊢tf | ta , ⊢ta = (tf · ta) , (⊢· ⊢tf ⊢ta refl refl)
split (`subst {A = A} R a b a≡b t) with split a | split b | split a≡b | split t
...                                   | a' , ⊢a' | b' , ⊢b' | a≡b' , ⊢a≡b' | t' , ⊢t'
                                      = (`subst a' b' a≡b' t') , (⊢subst {A = A} {R = R} ⊢a' ⊢b' ⊢a≡b' ⊢t')

split₁ : ∀ {ℓ} {A : Type ℓ} {a : ⟦ A ⟧} →
  ITerm A a →
  Term ℓ
split₁ t = proj₁ (split t)

-- normalize' : ∀ {t} {t₁} {t₂} {A : Type ℓ} {a : ⟦ A ⟧} →
--   t ⊢ A ∋ a →
--   t ≤ₜ[ t₁ , t₂ ] →
--   RespId' t₁ t₂ →
--   Term ℓ

isolve' : ∀ {A : Type ℓ} {a₁ a₂ : ⟦ A ⟧} →
  (t₁ : ITerm A a₁) →
  (t₂ : ITerm A a₂) →
  (R : RespId' (split₁ t₁) (split₁ t₂)) →
  normalize' (proj₂ (split t₁)) (left ≤-refl) R ≡ normalize' (proj₂ (split t₂)) (right ≤-refl) R →
  a₁ ≡ a₂
isolve' t₁ t₂ R norm-eq with split t₁   | split t₂
...                        | t₁' , ⊢t₁' | t₂' , ⊢t₂'
                           = solve' R ⊢t₁' ⊢t₂' norm-eq

module Example where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Vec
  open import Data.Vec.Properties

  data Index : ℕ → Set where
    index : ∀ n → Index n 

  test₁ : ∀ m n (i : Index (m + n)) →
    subst Index (+-comm n m) (subst Index (+-comm m n) i) ≡ i
  test₁ m n i = solve'
    {t₁ = `subst (` (` ℕ) ∋ (n + m) # 3) (` (` ℕ) ∋ (m + n) # 4)
            (` (+-comm n m) # 0)
            (`subst (` (` ℕ) ∋ (m + n) # 4) (` (` ℕ) ∋ (n + m) # 3)
              (` (+-comm m n) # 1)
              (` i # 2))}
    {t₂ = ` i # 2}
    (λ where
      x y → {!x y!}
      -- (left (≤-subst₁ ≤-refl)) (left (≤-subst₁ ≤-refl)) refl                       → refl
      -- (left (≤-subst₁ ≤-refl)) (left (≤-subst₂ (≤-subst₁ ()))) refl
      -- (left (≤-subst₁ ≤-refl)) (left (≤-subst₂ (≤-subst₂ ()))) refl
      -- (left (≤-subst₂ (≤-subst₁ ≤-refl))) (left (≤-subst₂ (≤-subst₁ ≤-refl))) refl → refl
      -- (left (≤-subst₂ (≤-subst₂ ≤-refl))) (left (≤-subst₂ (≤-subst₂ ≤-refl))) refl → refl
      -- (left (≤-subst₂ (≤-subst₂ ≤-refl))) (right ≤-refl) refl                      → refl
      -- (right ≤-refl) (left (≤-subst₂ (≤-subst₂ ≤-refl))) refl                      → refl
      -- (right ≤-refl) (right ≤-refl) refl                                           → refl
    )
    (⊢subst {A = ` ℕ} {R = λ n → ` Index n}
      (⊢` _ (n + m)) (⊢` _ (m + n))
      (⊢` _ (+-comm n m))
      (⊢subst {A = ` ℕ} {R = λ n → ` Index n}
        (⊢` _ (m + n)) (⊢` _ (n + m))
        (⊢` _ (+-comm m n))
        (⊢` (` Index (m + n)) i)))
    (⊢` (` Index (m + n)) i)
    refl

  test₁' : ∀ m n (i : Index (m + n)) →
    subst Index (+-comm n m) (subst Index (+-comm m n) i) ≡ i
  test₁' m n i = isolve'
    (`subst {A = ` ℕ} (λ n → ` Index n) (` (n + m) # 0) (` (m + n) # 1) (` +-comm n m # 2)
      (`subst {A = ` ℕ} (λ n → ` Index n) (` (m + n) # 1) (` (n + m) # 0) (` +-comm m n # 3)
        (` i # 4)))
    (` i # 4)
    {!!}
    refl

  g : ∀ m → Index m → Index m
  g m (index _) = index _

  test₂' : ∀ m (i : Index (m + 0)) →
    g m (subst Index (+-identityʳ m) i) ≡ subst Index (+-identityʳ m) (g (m + 0) i)
  test₂' m i = isolve'
    (_·_ {A = ` Index m} {B = λ _ → ` Index m}
      ((_·_ {A = ` ℕ} {B = λ n → `∀ (` Index n) (λ _ → ` Index n)} (` g # 0) (` m # 1)))
      (`subst {A = ` ℕ} (λ n → ` Index n) (` (m + 0) # 2) (` m # 1) (` +-identityʳ m # 3) (` i # 4)))
    (`subst {A = ` ℕ} (λ n → ` Index n) (` (m + 0) # 2) (` m # 1) (` +-identityʳ m # 3)
      (_·_ {A = ` Index (m + 0)} {B = λ _ → ` Index (m + 0)}
        ((_·_ {A = ` ℕ} {B = λ n → `∀ (` Index n) (λ _ → ` Index n)} (` g # 0) (` (m + 0) # 2)))
        (` i # 4)))
    (λ where
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ ()))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) refl → refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₂ _≤ₜ_.≤-refl)) refl → refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) refl → refl
        (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ ()))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (right (≤-subst₁ _≤ₜ_.≤-refl)) refl → refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (right (≤-subst₂ _≤ₜ_.≤-refl)) refl → refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (right (≤-subst₃ _≤ₜ_.≤-refl)) refl → refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) refl → refl
        (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ ()))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (left (≤-·₁ (≤-·₁ ()))) refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (left (≤-·₁ (≤-·₂ ()))) refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (left (≤-·₂ (≤-subst₂ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (left (≤-·₁ (≤-·₁ ()))) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (left (≤-·₁ (≤-·₂ ()))) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (left (≤-·₂ (≤-subst₃ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (left (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) (left (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₁ ()))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₁ (≤-·₂ ()))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) (left (≤-·₂ (≤-subst₁ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (left (≤-·₂ (≤-subst₄ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (right (≤-subst₁ _≤ₜ_.≤-refl)) refl → refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (right (≤-subst₂ ())) refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (right (≤-subst₃ ())) refl
        (right (≤-subst₁ _≤ₜ_.≤-refl)) (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) refl → refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (right (≤-subst₁ ())) refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (right (≤-subst₂ _≤ₜ_.≤-refl)) refl → refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (right (≤-subst₃ ())) refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (right (≤-subst₂ _≤ₜ_.≤-refl)) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (right (≤-subst₁ ())) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (right (≤-subst₂ ())) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (right (≤-subst₃ _≤ₜ_.≤-refl)) refl → refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (right (≤-subst₃ _≤ₜ_.≤-refl)) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) (right (≤-subst₁ _≤ₜ_.≤-refl)) refl → refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) refl → refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) refl → refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₁ ())))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₁ (≤-·₂ ())))) refl
        (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) (right (≤-subst₄ (≤-·₂ _≤ₜ_.≤-refl))) refl → refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (left (≤-·₂ (≤-subst₁ ()))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (left (≤-·₂ (≤-subst₂ ()))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₁ _≤ₜ_.≤-refl)))) (left (≤-·₂ (≤-subst₃ ()))) refl
        (right (≤-subst₄ (≤-·₁ (≤-·₂ _≤ₜ_.≤-refl)))) (left (≤-·₁ (≤-·₁ ()))) refl
    )
    refl
    -- refl

  -- before removing substs, we need to pull them to the outside.
  -- this function returns a list of all substs and the term without substs.
  -- in the _·_ case the substs from call on t₂ are given to the call on t₁.
  -- if an argument matches the input subst rhs it is replaced by the lhs.
  -- do we need the subst's R to be more precise where to apply the eq?

--   f : ∀ m n → Index (m + n) → Index (n + m)
--   f m n (index _) = index _

--   test₃' : ∀ m n (i : Index (m + n)) →
--     f n m (subst Index (+-comm m n) i) ≡ subst Index (+-comm n m) (f m n i)
--   test₃' m n i = isolve'
--     (_·_ {A = ` Index (n + m)} {B = λ i → ` Index (m + n)}
--       (` (f n m))
--       (`subst {A = ` ℕ} (λ n → ` Index n) (+-comm m n) (` i)))
--     (`subst {A = ` ℕ} (λ n → ` Index n) (+-comm n m)
--       (_·_ {A = ` Index (m + n)} {B = λ i → ` Index (n + m)}
--         (` (f m n)) (` i)))
--     {!!}

--   -- test₂ : ∀ m n p (u : Vec ℕ m) (v : Vec ℕ n) (w : Vec ℕ p) →
--   --   (u ++ (v ++ w)) ≡ subst (Vec ℕ) (+-assoc m n p) ((u ++ v) ++ w)
--   -- test₂ m n p u v w = solve' {t₁ = (` _++_ {0ℓ} {ℕ} {m} {n}) · {!(` u)!}} (⊢· {!!} {!!} refl refl) {!!} {!!}
