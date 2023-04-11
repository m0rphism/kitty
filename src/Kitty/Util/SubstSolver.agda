module Kitty.Util.SubstSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)
open import Level renaming (suc to lsuc; zero to 0ℓ) using (Level; _⊔_; Setω; Lift; lift; lower)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)

variable ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ : Level

data Term ℓ : Set (lsuc ℓ) where
  `_ : ∀ {A : Set ℓ} → (a : A) → Term ℓ
  _·_ : Term ℓ → Term ℓ → Term ℓ
  `subst : Term ℓ → Term ℓ → Term ℓ

mutual
  data Type ℓ : Set (lsuc ℓ) where
    `_ : (A : Set ℓ) → Type ℓ
    `∀ : (A : Type ℓ) → (⟦ A ⟧ → Type ℓ) → Type ℓ

  ⟦_⟧ : Type ℓ → Set ℓ
  ⟦ ` A   ⟧ = A
  ⟦ `∀ A B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B a ⟧

data _⊢_∋_ {ℓ} : Term ℓ → (A : Type ℓ) → ⟦ A ⟧ → Set (lsuc ℓ) where
  ⊢` : ∀ (A : Set ℓ) (a : A) → (` a) ⊢ ` A ∋ a
  ⊢· : ∀ {A : Type ℓ} {B : ⟦ A ⟧ → Type ℓ} {tf f ta a} {Ba fa} →
    tf ⊢ `∀ A B ∋ f →
    ta ⊢ A ∋ a →
    (Ba-eq : Ba ≡ B a) →
    fa ≡ f a →
    (tf · ta) ⊢ Ba ∋ subst id (sym (cong ⟦_⟧ Ba-eq)) fa
  ⊢subst : ∀ {A : Type ℓ} {R : ⟦ A ⟧ → Type ℓ} {a b tra ra teq eq} →
    teq ⊢ ` (a ≡ b) ∋ eq →
    tra ⊢ (R a) ∋ ra →
    `subst teq tra ⊢ (R b) ∋ (subst (λ a → ⟦ R a ⟧) eq ra)

normalize : Term ℓ → Term ℓ
normalize (` a)          = ` a
normalize (t₁ · t₂)      = (normalize t₁) · (normalize t₂)
normalize (`subst teq t) = normalize t

·-injective : ∀ {tf₁ ta₁ tf₂ ta₂ : Term ℓ} →
  (tf₁ · ta₁) ≡ (tf₂ · ta₂) →
  (tf₁ ≡ tf₂) × (ta₁ ≡ ta₂)
·-injective refl = refl , refl

solve : ∀ {A₁ A₂ : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧} →
  t₁ ⊢ A₁ ∋ a₁ →
  t₂ ⊢ A₂ ∋ a₂ →
  normalize t₁ ≡ normalize t₂ →
  Σ[ eq ∈ (A₁ ≡ A₂) ] subst id (cong ⟦_⟧ eq) a₁ ≡ a₂
solve {ℓ} {A₁} {A₂} {.(` a₁)} {.(` a₂)} {.a₁} {.a₂} (⊢` _ a₁) (⊢` _ a₂) refl = refl , refl
solve {ℓ} {_} {A₂} {_} {t₂} {_} {a₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
solve {ℓ} {_} {A₂} {_} {t₂} {_} {a₂} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
solve {ℓ} {A₁} {A₂}
      {.(_ · _)} {.(_ · _)}
      {.(subst id (sym (cong ⟦_⟧ Ba-eq₁)) _)}
      {.(subst id (sym (cong ⟦_⟧ Ba-eq₂)) _)}
      (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁)
      (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
      norm-eq
  with ·-injective norm-eq                   
... | norm-eq-tf , norm-eq-ta
  with solve ⊢ta₁ ⊢ta₂ norm-eq-ta
... | refl , refl
  with solve ⊢tf₁ ⊢tf₂ norm-eq-tf
... | refl , refl
  with Ba-eq₂ | fa-eq₂
... | refl | refl
  with Ba-eq₁ | fa-eq₁
... | refl | refl
  =  refl , refl

solve' : ∀ {A : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ a₂ : ⟦ A ⟧} →
  t₁ ⊢ A ∋ a₁ →
  t₂ ⊢ A ∋ a₂ →
  normalize t₁ ≡ normalize t₂ →
  a₁ ≡ a₂
solve' ⊢t₁ ⊢t₂ norm-eq with solve ⊢t₁ ⊢t₂ norm-eq
... | refl , eqa = eqa

data ITerm {ℓ} : ∀ (A : Type ℓ) → (a : ⟦ A ⟧) → Set (lsuc ℓ) where
  `_ : ∀ {A : Set ℓ} → (a : A) → ITerm (` A) a
  _·_ : ∀ {A : Type ℓ} {B : ⟦ A ⟧ → Type ℓ} {f a} →
    ITerm (`∀ A B) f →
    ITerm A a →
    ITerm (B a) (f a)
  `subst : ∀ {A : Type ℓ} (R : ⟦ A ⟧ → Type ℓ) {a b ra} →
    (a≡b : a ≡ b) →
    ITerm (R a) ra →
    ITerm (R b) (subst (λ a → ⟦ R a ⟧) a≡b ra)

split : ∀ {ℓ} {A : Type ℓ} {a : ⟦ A ⟧} →
  ITerm A a →
  Σ[ t ∈ Term ℓ ]
    t ⊢ A ∋ a
split (`_ {A = A} a)                     = (` a) , (⊢` A a)
split (t₁ · t₂) with split t₁ | split t₂
...                | tf , ⊢tf | ta , ⊢ta = (tf · ta) , (⊢· ⊢tf ⊢ta refl refl)
split (`subst {A = A} R a≡b t) with split t
...                | t' , ⊢t' = (`subst (` a≡b) t') , (⊢subst {A = A} {R = R} (⊢` _ a≡b) ⊢t')

inormalize : ∀ {ℓ} {A : Type ℓ} {a} → ITerm A a → Term ℓ
inormalize t with split t
... | t' , ⊢t' = normalize t'

isolve' : ∀ {A : Type ℓ} {a₁ a₂ : ⟦ A ⟧} →
  (t₁ : ITerm A a₁) →
  (t₂ : ITerm A a₂) →
  inormalize t₁ ≡ inormalize t₂ →
  a₁ ≡ a₂
isolve' t₁ t₂ norm-eq with split t₁   | split t₂
...                      | t₁' , ⊢t₁' | t₂' , ⊢t₂'
                         = solve' ⊢t₁' ⊢t₂' norm-eq

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
    {t₁ = `subst (` (+-comm n m)) (`subst (` (+-comm m n)) (` i))}
    {t₂ = ` i}
    (⊢subst {A = ` ℕ} {R = λ n → ` Index n}
      (⊢` _ (+-comm n m))
      (⊢subst {A = ` ℕ} {R = λ n → ` Index n}
        (⊢` _ (+-comm m n))
        (⊢` (Index (m + n)) i)))
    (⊢` (Index (m + n)) i)
    refl

  test₁' : ∀ m n (i : Index (m + n)) →
    subst Index (+-comm n m) (subst Index (+-comm m n) i) ≡ i
  test₁' m n i = isolve'
    (`subst {A = ` ℕ} (λ n → ` Index n) (+-comm n m)
      (`subst {A = ` ℕ} (λ n → ` Index n) (+-comm m n)
        (` i)))
    (` i)
    refl

  -- test₂ : ∀ m n p (u : Vec ℕ m) (v : Vec ℕ n) (w : Vec ℕ p) →
  --   (u ++ (v ++ w)) ≡ subst (Vec ℕ) (+-assoc m n p) ((u ++ v) ++ w)
  -- test₂ m n p u v w = solve' {t₁ = (` _++_ {0ℓ} {ℕ} {m} {n}) · {!(` u)!}} (⊢· {!!} {!!} refl refl) {!!} {!!}


