module Kitty.Examples.LambdaPiRec-Derive.Definitions where

open import Data.List.Relation.Unary.Any using (here; there) public
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; _⊔_; suc; zero)
open import Data.Bool renaming (Bool to 𝔹) using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (Terms; SortTy; Var; NoVar)
open import Kitty.Util.Closures

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _≣_  _⊢_∶_
infixr  5  λx_  Π[x∶_]_  Σ[x∶_]_  µx_
infixl  4  _,_
infixl  8  _·_
infix   9  `_

-- Sorts -----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖 : Sort Var

variable
  m n o                     : ℕ
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' S'' : List (Sort Var)
  x y z                     : S ∋ s

-- Syntax ----------------------------------------------------------------------

data Label : Set where
  #1 #2 : Label

select : ∀ {ℓ} {A : Label → Set ℓ} (l : Label) → A #1 → A #2 → A l
select #1 a₁ a₂ = a₁
select #2 a₁ a₂ = a₂

J' : ∀ {A : Set} {C : (x y : A) → (x ≡ y) → Set} →
     (c : ∀ x → C x x refl) →
     (x y : A) → (p : x ≡ y) → C x y p
J' c x .x refl = c x

-- Expressions, Types, and Kinds
data _⊢_ : List (Sort Var) → Sort st → Set where
  `_         : S ∋ s  →  S ⊢ s

  Π[x∶_]_    : S ⊢ 𝕖  →  S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  λx_        : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  _·_        : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖

  λ[f]x_     : S ▷ 𝕖 ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  RecArg     : S ⊢ 𝕖  →  𝔹  →  S ⊢ 𝕖  →  S ⊢ 𝕖 
  RecFun     : S ⊢ 𝕖  →  S ⊢ 𝕖 
  RecSet     : ℕ → S ⊢ 𝕖
  ⌞_⌟        : S ⊢ 𝕖  →  S ⊢ 𝕖 

  Σ[x∶_]_    : S ⊢ 𝕖  →  S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  _,_        : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖 
  π          : Label  →  S ⊢ 𝕖  →  S ⊢ 𝕖

  _+_        : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖 
  ι          : Label  →  S ⊢ 𝕖  →  S ⊢ 𝕖 
  case_[_;_] : S ⊢ 𝕖 → S ▷ 𝕖 ⊢ 𝕖 → S ▷ 𝕖 ⊢ 𝕖 → S ⊢ 𝕖

  µx_        : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  fold       : S ⊢ 𝕖  →  S ⊢ 𝕖
  unfold     : S ⊢ 𝕖  →  S ⊢ 𝕖

  `⊤         : S ⊢ 𝕖
  tt         : S ⊢ 𝕖

  `⊥         : S ⊢ 𝕖
  absurd     : S ⊢ 𝕖  →  S ⊢ 𝕖

  _`≡_∶_     : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  refl       : S ⊢ 𝕖  →  S ⊢ 𝕖
  J          : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖

  `Set       : ℕ → S ⊢ 𝕖

variable
  l l₁ l₂ l'                : Label
  e e₁ e₂ e₃ e' e₁' e₂' e₃' ex ey : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : S ⊢ s
  E E₁ E₂ E₃ E' E₁' E₂' E₃' : S ⊢ s

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)

unquoteDecl D = derive Sort _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeSorts terms

-- Each variable sort corresponds to a term sort that represents its type.
type-sorts : TypeSorts
type-sorts = record { ↑ᵗ = λ { m → _ , m } }

open TypeSorts type-sorts public

open import Kitty.Typing.CtxRepr type-sorts

ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : S ⊢ s → Set where
    `_     : ∀ (x : S ∋ s) → Neutral (` x)
    _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    π      : (l : Label) → Neutral e → Neutral (π l e)
    case_[_;_] : Neutral e → Value e₁ → Value e₂ → Neutral (case e [ e₁ ; e₂ ])
    unfold : Neutral e → Neutral (unfold e)
    absurd : Neutral e → Neutral (absurd e)
    J      : Value e₁ → Neutral e₂ → Neutral (J e₁ e₂)

  data Value : S ⊢ s → Set where
    Π[x∶_]_ : Value t₁ → Value t₂ → Value (Π[x∶ t₁ ] t₂)
    λx_     : Value e → Value (λx e)
    Σ[x∶_]_ : Value t₁ → Value t₂ → Value (Σ[x∶ t₁ ] t₂)
    _,_     : Value e₁ → Value e₂ → Value (e₁ , e₂)
    _+_     : Value t₁ → Value t₂ → Value (t₁ + t₂)
    ι       : (l : Label) → Value e → Value (ι l e)
    `⊤      : Value {S} `⊤
    tt      : Value {S} tt
    `⊥      : Value {S} `⊥
    _`≡_    : Value e₁ → Value e₂ → Value t → Value (e₁ `≡ e₂ ∶ t)
    refl    : Value e → Value (refl e)
    µx_     : Value t → Value (µx t)
    fold    : Value e → Value (fold e)
    `Set    : (n : ℕ) → Value {S} (`Set n)
    neutral : Neutral e → Value e

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-Π : ∀ {e₂ : S ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆'ₛ
  β-Σ : ∀ {e₁ e₂ : S ⊢ 𝕖} →
    π l (e₁ , e₂) ↪ select l e₁ e₂
  β-+ : ∀ {e : S ⊢ 𝕖} →
    case (ι l e) [ e₁ ; e₂ ] ↪ select l e₁ e₂ ⋯ ⦅ e ⦆'ₛ
  β-≡ : {e : S ⊢ 𝕖} →
    J e₁ (refl e) ↪ e₁ ⋯ ⦅ e ⦆'ₛ
  β-µ :
    unfold (fold e) ↪ e

  ξ-Π₁ :
    t₁ ↪ t₁' →
    Π[x∶ t₁ ] t₂ ↪ Π[x∶ t₁' ] t₂
  ξ-Π₂ :
    t₂ ↪ t₂' →
    Π[x∶ t₁ ] t₂ ↪ Π[x∶ t₁ ] t₂'
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

  ξ-Σ₁ :
    t₁ ↪ t₁' →
    Σ[x∶ t₁ ] t₂ ↪ Σ[x∶ t₁' ] t₂
  ξ-Σ₂ :
    t₂ ↪ t₂' →
    Σ[x∶ t₁ ] t₂ ↪ Σ[x∶ t₁ ] t₂'
  ξ-π :
    e ↪ e' →
    π l e ↪ π l e'
  ξ-,₁ :
    e₁ ↪ e₁' →
    e₁ , e₂ ↪ e₁' , e₂
  ξ-,₂ :
    e₂ ↪ e₂' →
    e₁ , e₂ ↪ e₁ , e₂'

  ξ-+₁ :
    t₁ ↪ t₁' →
    t₁ + t₂ ↪ t₁' + t₂
  ξ-+₂ :
    t₂ ↪ t₂' →
    t₁ + t₂ ↪ t₁ + t₂'
  ξ-ι :
    e ↪ e' →
    ι l e ↪ ι l e'
  ξ-case₁ :
    e ↪ e' →
    case e [ e₁ ; e₂ ] ↪ case e' [ e₁ ; e₂ ]
  ξ-case₂ :
    e₁ ↪ e₁' →
    case e [ e₁ ; e₂ ] ↪ case e [ e₁' ; e₂ ]
  ξ-case₃ :
    e₂ ↪ e₂' →
    case e [ e₁ ; e₂ ] ↪ case e [ e₁ ; e₂' ]

  ξ-≡₁ :
    e₁ ↪ e₁' →
    (e₁ `≡ e₂ ∶ t) ↪ (e₁' `≡ e₂ ∶ t)
  ξ-≡₂ :
    e₂ ↪ e₂' →
    (e₁ `≡ e₂ ∶ t) ↪ (e₁ `≡ e₂' ∶ t)
  ξ-≡₃ :
    t ↪ t' →
    (e₁ `≡ e₂ ∶ t) ↪ (e₁ `≡ e₂ ∶ t')
  ξ-refl :
    e ↪ e' →
    refl e ↪ refl e'
  ξ-J₁ :
    e₁ ↪ e₁' →
    J e₁ e₂ ↪ J e₁' e₂
  ξ-J₂ :
    e₂ ↪ e₂' →
    J e₁ e₂ ↪ J e₁ e₂'

  ξ-µ :
    t ↪ t' →
    µx t ↪ µx t'
  ξ-fold :
    t ↪ t' →
    fold t ↪ fold t'
  ξ-unfold :
    t ↪ t' →
    unfold t ↪ unfold t'

open ReflexiveTransitiveClosure₃ (λ st S s → _⊢_ {st} S s) _↪_ renaming
  ( ReflTrans to _↪*_
  ; map-ReflTrans to map-↪*
  ; _⟨_⟩_ to _↪⟨_⟩_
  ; _*⟨_⟩_ to _↪*⟨_⟩_
  ; _∎ to _↪∎
  ; trans to ↪*-trans
  ) public

data _≣_ (t₁ t₂ : S ⊢ s) : Set where
  mk-≣ : ∀ t → (t₁↪*t : t₁ ↪* t) → (t₂↪*t : t₂ ↪* t) → t₁ ≣ t₂

data _⇓_ (e₁ e₂ : S ⊢ s) : Set where
  ⇓[_,_] :
      e₁ ↪* e₂  
    → Value e₂
    → e₁ ⇓ e₂

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {x : S ∋ s} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T

  ⊢Π :
    Γ ⊢ t₁ ∶ `Set m →
    Γ ▶ t₁ ⊢ t₂ ∶ `Set n →
    Γ ⊢ Π[x∶ t₁ ] t₂ ∶ `Set (m ⊔ n)
  ⊢λ :
    Γ ⊢ t₁ ∶ `Set m →
    Γ ▶ t₁ ⊢ e ∶ t₂ →
    Γ ⊢ λx e ∶ Π[x∶ t₁ ] t₂
  ⊢· :
    Γ ⊢ e₁ ∶ Π[x∶ t₁ ] t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆'ₛ

  ⊢λ[f] : {Γ : Ctx S} →
    Γ ⊢ t₁ ∶ `Set m →
    Γ ▶ RecFun (Π[x∶ t₁ ] (t₂ ⋯ ⦅ ⌞ # 0 ⌟ ⦆))
      ▶ (RecArg (# 0) false (t₁ ⋯ wknᵣ)) ⊢ e
      ∶ t₂ ⋯ ⦅ ⌞ # 0 ⌟ ⦆ ⋯ (wknᵣ ↑ 𝕖) →
    Γ ⊢ λ[f]x e ∶ Π[x∶ t₁ ] t₂
  ⊢RecArg : ∀ {b} →
    Γ ⊢ t₁ ∶ `Set n →
    Γ ⊢ e ∶ RecFun (Π[x∶ t₁ ] t₂) →
    Γ ⊢ RecArg e b t₁ ∶ RecSet n
  ⊢RecFun :
    Γ ⊢ t ∶ `Set n →
    Γ ⊢ RecFun t ∶ RecSet n
  ⊢RecSet :
    Γ ⊢ RecSet n ∶ RecSet (suc n)
  ⊢⌞⌟ : ∀ {b} →
    Γ ⊢ e ∶ RecArg e' b t →
    Γ ⊢ ⌞ e ⌟ ∶ t
  ⊢f· :
    Γ ⊢ e₁ ∶ RecFun (Π[x∶ t₁ ] t₂) →
    Γ ⊢ e₂ ∶ RecArg e₁ true t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆'ₛ

  ⊢Σ :
    Γ ⊢ t₁ ∶ `Set m →
    Γ ▶ t₁ ⊢ t₂ ∶ `Set n →
    Γ ⊢ Σ[x∶ t₁ ] t₂ ∶ `Set (m ⊔ n)
  ⊢, : {t₂ : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ e₂ ∶ t₂ ⋯ ⦅ e₁ ⦆'ₛ →
    Γ ⊢ e₁ , e₂ ∶ Σ[x∶ t₁ ] t₂
  ⊢π₁ : {t₂ : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ Σ[x∶ t₁ ] t₂ →
    Γ ⊢ π #1 e ∶ t₁
  ⊢π₂ : {t₂ : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ Σ[x∶ t₁ ] t₂ →
    Γ ⊢ π #2 e ∶ t₂ ⋯ ⦅ π #1 e ⦆'ₛ
  ⊢rec-π₁ : ∀ {b} {t₂ : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ RecArg e' b (Σ[x∶ t₁ ] t₂) →
    Γ ⊢ π #1 e ∶ RecArg e' true t₁
  ⊢rec-π₂ : ∀ {b} {t₂ : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ RecArg e' b (Σ[x∶ t₁ ] t₂) →
    Γ ⊢ π #2 e ∶ RecArg e' true (t₂ ⋯ ⦅ π #1 e ⦆'ₛ)

  ⊢+ :
    Γ ⊢ t₁ ∶ `Set m →
    Γ ⊢ t₂ ∶ `Set n →
    Γ ⊢ t₁ + t₂ ∶ `Set (m ⊔ n)
  ⊢ι : ∀ l →
    Γ ⊢ e ∶ select l t₁ t₂ →
    Γ ⊢ ι l e ∶ t₁ + t₂
  ⊢case : {t : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ t₁ + t₂ →
    Γ ▶ t₁ ⊢ e₁ ∶ t ⋯ ⦅ ι #1 (` here {xs = S} refl) ⦆ₛ →
    Γ ▶ t₂ ⊢ e₂ ∶ t ⋯ ⦅ ι #2 (` here {xs = S} refl) ⦆ₛ →
    Γ ⊢ case e [ e₁ ; e₂ ] ∶ t ⋯ ⦅ e ⦆'ₛ
  ⊢rec-case : ∀ {b} {t : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ⊢ e ∶ RecArg e' b (t₁ + t₂) →
    Γ ▶ RecArg e' true t₁ ⊢ e₁ ∶ t ⋯ ⦅ ι #1 (⌞ ` here {xs = S} refl ⌟) ⦆ₛ →
    Γ ▶ RecArg e' true t₂ ⊢ e₂ ∶ t ⋯ ⦅ ι #2 (⌞ ` here {xs = S} refl ⌟) ⦆ₛ →
    Γ ⊢ case e [ e₁ ; e₂ ] ∶ t ⋯ ⦅ e ⦆'ₛ
  -- ⊢case-non-dep : {t : S ⊢ 𝕖} →
  --   Γ ⊢ e ∶ t₁ + t₂ →
  --   Γ ▶ t₁ ⊢ e₁ ∶ t ⋯ wknᵣ →
  --   Γ ▶ t₂ ⊢ e₂ ∶ t ⋯ wknᵣ →
  --   Γ ⊢ case e [ e₁ ; e₂ ] ∶ t
  -- -- should be implementable via ⊢case with t = (e. case e [ t ; t ])
  -- ⊢case-alt : {t : S ▷ 𝕖 ⊢ 𝕖} →
  --   Γ ⊢ e ∶ t₁ + t₂ →
  --   Γ ▶ t₁ ⊢ e₁ ∶ t →
  --   Γ ▶ t₂ ⊢ e₂ ∶ t →
  --   Γ ⊢ case e [ e₁ ; e₂ ] ∶ case e [ t ; t ]

  ⊢µ :
    Γ ▶ `Set m ⊢ t ∶ `Set m →
    Γ ⊢ µx t ∶ `Set m
  ⊢fold : {Γ : Ctx S} →
    Γ ⊢ e ∶ t ⋯ ⦅ µx t ⦆'ₛ →
    Γ ⊢ fold e ∶ µx t
  ⊢unfold : {Γ : Ctx S} →
    Γ ⊢ e ∶ µx t →
    Γ ⊢ unfold e ∶ t ⋯ ⦅ µx t ⦆'ₛ
  ⊢rec-unfold : ∀ {b} {Γ : Ctx S} →
    Γ ⊢ e ∶ RecArg e' b (µx t) →
    Γ ⊢ unfold e ∶ RecArg e' true (t ⋯ ⦅ µx t ⦆'ₛ)

  ⊢⊤ :
    Γ ⊢ `⊤ ∶ `Set 0
  ⊢tt :
    Γ ⊢ tt ∶ `⊤

  ⊢⊥ :
    Γ ⊢ `⊥ ∶ `Set 0
  ⊢absurd :
    Γ ⊢ e ∶ `⊥ →
    Γ ⊢ absurd e ∶ t

  ⊢≡ :
    Γ ⊢ e₁ ∶ t →
    Γ ⊢ e₂ ∶ t →
    Γ ⊢ t ∶ `Set m →
    Γ ⊢ (e₁ `≡ e₂ ∶ t) ∶ `Set m
  ⊢refl :
    Γ ⊢ e ∶ t →
    Γ ⊢ refl e ∶ (e `≡ e ∶ t)
  ⊢J : {Γ : Ctx S} {t : S ▷ 𝕖 ▷ 𝕖 ▷ 𝕖 ⊢ 𝕖} {ex ey t' : S ⊢ 𝕖}  →
    Γ ▶ t' ⊢ e₁ ∶ t ⋯ₛ wkₖ 𝕖 (idₛ {S = S}) ,ₖ (` here refl) ,ₖ (` here refl) ,ₖ refl (` here refl) →
    Γ ⊢ e₂ ∶ (ex `≡ ey ∶ t') →
    Γ ⊢ J e₁ e₂ ∶ t ⋯ id ,ₖ ex ,ₖ ey ,ₖ e₂

  ⊢Set :
    Γ ⊢ `Set n ∶ `Set (suc n)

  ⊢≣ :
    t ≣ t' →
    Γ ⊢ e ∶ t →
    Γ ⊢ e ∶ t'

pattern ι₁ e = ι #1 e
pattern ι₂ e = ι #2 e
pattern π₁ e = π #1 e
pattern π₂ e = π #2 e
pattern _`×_ e₁ e₂ = Σ[x∶ e₁ ] e₂


module Examples where
  `ℕ `𝔹 : S ⊢ 𝕖
  `𝔹 = `⊤ + `⊤
  `ℕ = µx `⊤ + # 0

  -- `ℕ-List : S ⊢ 𝕖
  -- `ℕ-List = µx (`⊤ + (`ℕ            `× # 0))
  -- `ℕ-List = µx (`⊤ + ((µx `⊤ + # 0 + # 1) `× # 0))

  `0 : S ⊢ 𝕖
  `0 = fold (ι₁ tt)

  `suc : S ⊢ 𝕖 → S ⊢ 𝕖
  `suc e = fold (ι₂ e)

  `+ : S ⊢ 𝕖 
  `+ = λ[f]x (λx case (unfold (# 1))
    [ `0
    ; `suc (# 3 · # 0 · # 1 )
    ])

  `ℕ∶★ : Γ ⊢ `ℕ ∶ `Set 0
  `ℕ∶★ = ⊢µ (⊢+ ⊢⊤ (⊢` {!here refl!}))

  postulate
    ⊢`+ : Γ ⊢ `+ ∶ Π[x∶ `ℕ ] Π[x∶ `ℕ ] `ℕ

  ⊢`+' : ∅ ⊢ `+ ∶ Π[x∶ `ℕ ] Π[x∶ `ℕ ] `ℕ
  ⊢`+' = ⊢λ[f] `ℕ∶★ (⊢λ `ℕ∶★ (⊢rec-case
    {t = `ℕ}
    (⊢rec-unfold (⊢` refl))
    (⊢fold (⊢ι #1 ⊢tt))
    (⊢fold (⊢ι #2 (⊢·
      (⊢f· {t₁ = `ℕ} {t₂ = Π[x∶ `ℕ ] `ℕ} (⊢` refl) (⊢` refl))
      (⊢` refl))))))

  `1 : S ⊢ 𝕖
  `1 = `suc `0

  0∶ℕ : Γ ⊢ `0 ∶ `ℕ
  0∶ℕ = ⊢fold (⊢ι #1 ⊢tt)

  1∶ℕ : Γ ⊢ `1 ∶ `ℕ
  1∶ℕ = ⊢fold (⊢ι #2 0∶ℕ)

  ⊢suc : Γ ⊢ e ∶ `ℕ → Γ ⊢ `suc e ∶ `ℕ
  ⊢suc ⊢e = ⊢fold (⊢ι #2 ⊢e)

  `cong-suc : S ⊢ 𝕖
  `cong-suc = λx λx λx (J (refl (`suc (# 0))) (# 0))

  ⊢cong-suc : Γ ⊢ `cong-suc
    ∶ Π[x∶ `ℕ ] Π[x∶ `ℕ ] Π[x∶ (# 1) `≡ (# 0) ∶ `ℕ ] (`suc (# 2) `≡ `suc (# 1) ∶ `ℕ) 
  ⊢cong-suc = ⊢λ `ℕ∶★ (⊢λ `ℕ∶★ (⊢λ (⊢≡ (⊢` {!!}) {!!} {!!})
    (⊢J {t = `suc (# 2) `≡ `suc (# 1) ∶ `ℕ}
        (⊢refl (⊢suc (⊢` {!!})))
        (⊢` {!!}))))

  `n+0≡n : S ⊢ 𝕖
  `n+0≡n = λ[f]x case (unfold (# 0))
    [ refl `0
    ; `cong-suc · (`+ · ⌞ (# 0) ⌟ · `0) · ⌞ # 0 ⌟ · (# 2 · # 0)
    ]

  ⊢n+0≡n : ∅ ⊢ `n+0≡n ∶ Π[x∶ `ℕ ] (`+ · # 0 · `0) `≡ (# 0) ∶ `ℕ
  ⊢n+0≡n =
    ⊢λ[f] `ℕ∶★
      (⊢≣ {!!} 
        (⊢rec-case
          {t = (`+ · fold (# 0) · `0) `≡ fold (# 0) ∶ `ℕ}
          (⊢rec-unfold (⊢` refl))
          (⊢≣ {!!} (⊢refl 0∶ℕ))
          (⊢≣ {!!} (⊢·
            (⊢·
              (⊢·
                ⊢cong-suc
                (⊢·
                  (⊢· ⊢`+ (⊢⌞⌟ (⊢` refl)))
                  0∶ℕ))
              (⊢⌞⌟ (⊢` refl)))
            (⊢f·
              (⊢` refl)
              (⊢` refl))))))

  -- `0≡0 : [] ⊢ 𝕖
  -- `0≡0 = `0 `≡ `0 ∶ `ℕ

  `0≡0 : ∅ ⊢ refl `0 ∶ (`0 `≡ `0 ∶ `ℕ)
  `0≡0 = ⊢refl 0∶ℕ

  -- `0≢1 : ∅ ⊢ λx (J (case (unfold (# 0)) [ tt ; tt ]) (# 0)) ∶ (Π[x∶ (`0 `≡ `1 ∶ `ℕ) ] `⊥)
  -- `0≢1 = ⊢λ (⊢≡ 0∶ℕ 1∶ℕ `ℕ∶★)
  --           (⊢≣ {!!}
  --             (⊢J {t = case (unfold (# 2)) [ case (unfold (# 2)) [ `⊤ ; `⊥ ] ; `⊤ ] }
  --                 (⊢case (⊢unfold (⊢` refl))
  --                        (⊢≣ {!!} ⊢tt)
  --                        (⊢≣ {!!} ⊢tt))
  --                 (⊢` refl)))

  open import Data.Nat
  open import Data.Empty
  open import Data.Unit

  J'' : ∀ {A : Set} {C : (x y : A) → (x ≡ y) → Set} →
      (c : ∀ z → C z z refl) →
      (x y : A) → (p : x ≡ y) → C x y p
  J'' c x .x refl = c x

  foo : 0 ≡ 1 → ⊥
  foo p = J'' {C = λ where
                       zero    (suc y) p → ⊥
                       _       _       p → ⊤}
              (λ { zero → tt ; (suc x) → tt }) 0 1 p

  boo : ∀ x y → x ≡ y → suc x ≡ suc y
  boo x y p = J'' {C = λ x y p → suc x ≡ suc y} (λ z → refl) x y p




-- Values : Ctx S → Set
-- Values {S} Γ = ∀ {m} (x : S ∋ m) → Value (Γ x) 

-- Values-ext : ∀ {Γ : Ctx S} → Values Γ → Value t → Values (Γ ▶ t)
-- Values-ext {S} VΓ Vt (here refl) = Vt
-- Values-ext {S} VΓ Vt (there x) = VΓ x

-- -- postulate
-- --   Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- -- Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- -- Value-wk-telescope {x = here refl} VΓx = {!VΓx!}
-- -- -- Value-wk-telescope {x = there x} VΓx = {!!}

-- -- ⊢-Value :
-- --   ∀ {S} {Γ : Ctx S} {M} {e : S ⊢ M} {t : S ⊢ M}
-- --   → Values Γ
-- --   → Γ ⊢ e ∶ t
-- --   → Value t
-- -- ⊢-Value {Γ = Γ} VΓ (⊢` {x = x} refl) = Value-wk-telescope {Γ = Γ} (VΓ x)
-- -- ⊢-Value VΓ (⊢λ Vt₁ ⊢e₁ ⊢e₂)          = ∀[x∶ Vt₁ ] ⊢-Value (Values-ext VΓ Vt₁) ⊢e₂
-- -- ⊢-Value VΓ (⊢∀ t₁⇓t₁' ⊢t₁ ⊢t₂)       = ★
-- -- ⊢-Value VΓ (⊢· ⊢e₁ ⊢e₂ ⇓[ _ , Vt ])  = Vt
-- -- ⊢-Value VΓ ⊢★                        = ★
