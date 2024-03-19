module Kitty.Examples.LambdaPi.Definitions where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (SortTy; Var; NoVar)
open import Kitty.Util.Closures
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _↪*_  _≈_  _⊢_∶_
infixr  5  λx_  ∀[x∶_]_  ∃[x∶_]_
infix   6  _`≡_
infixr  7  _`,_
infixl  8  _·_
infix   9  `_

-- Syntax ----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖 : Sort Var

variable
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : List (Sort Var)
  x y z                     : S ∋ s

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List (Sort Var) → Sort st → Set where
  -- Variables
  `_        : S ∋ s  →  S ⊢ s

  -- Pi Types
  ∀[x∶_]_   : S ⊢ 𝕖  →  S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  λx_       : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  _·_       : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖

  -- Sigma Types
  ∃[x∶_]_   : S ⊢ 𝕖  →  S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  _`,_      : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  `proj₁    : S ⊢ 𝕖  →  S ⊢ 𝕖
  `proj₂    : S ⊢ 𝕖  →  S ⊢ 𝕖

  -- Equality Types
  _`≡_      : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  `refl     : S ⊢ 𝕖
  `J        : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖

  -- Universe
  `Set      : S ⊢ 𝕖

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : S ⊢ s
  u u₁ u₂ u₃ u' u₁' u₂' u₃' : S ⊢ s

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Term.Reflection using (derive; module Derived)

unquoteDecl D = derive Sort _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeSorts terms

-- Each variable mode corresponds to a term mode that represents its type.
type-sorts : TypeSorts
type-sorts = record { ↑ᵗ = λ { 𝕖 → _ , 𝕖 } }

open TypeSorts type-sorts public

open import Kitty.Typing.CtxRepr type-sorts

ctx-repr : CtxRepr
ctx-repr = List-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  t t₁ t₂ t' t₁' t₂' : S ∶⊢ 𝕖
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

-- Semantics -------------------------------------------------------------------

mutual
  data Value : S ⊢ s → Set where
    val-λ    : Value e → Value (λx e)
    val-∀    : Value e₁ → Value e₂ → Value (∀[x∶ e₁ ] e₂)
    val-Set  : Value {S = S} `Set
    val-neu  : Neutral e → Value e
    val-∃    : Value e₁ → Value e₂ → Value (∃[x∶ e₁ ] e₂)
    val-,    : Value e₁ → Value e₂ → Value (e₁ `, e₂)
    val-≡    : Value e₁ → Value e₂ → Value (e₁ `≡ e₂)
    val-refl : Value {S = S} `refl

  data Neutral : S ⊢ s → Set where
    neu-`     : Neutral (` x)
    neu-·     : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    neu-proj₁ : Neutral e → Neutral (`proj₁ e)
    neu-proj₂ : Neutral e → Neutral (`proj₂ e)
    neu-J     : Value e → Neutral e₁ → Value e₂ → Neutral (`J e e₁ e₂)

-- Reduction

data _↪_ : S ⊢ s → S ⊢ s → Set where

  -- Pi Types

  β-λ : ∀ {e₁ : (𝕖 ∷ S) ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆

  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'

  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂ 

  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

  ξ-∀₁ :
    t₁ ↪ t₁' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂

  ξ-∀₂ :
    t₂ ↪ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁ ] t₂'

  -- Sigma Types

  β-proj₁ :
    `proj₁ (e₁ `, e₂) ↪ e₁

  β-proj₂ :
    `proj₂ (e₁ `, e₂) ↪ e₂

  ξ-∃₁ :
    t₁ ↪ t₁' →
    ∃[x∶ t₁ ] t₂ ↪ ∃[x∶ t₁' ] t₂

  ξ-∃₂ :
    t₂ ↪ t₂' →
    ∃[x∶ t₁ ] t₂ ↪ ∃[x∶ t₁ ] t₂'

  ξ-proj₁ :
    e ↪ e' →
    `proj₁ e ↪ `proj₁ e'

  ξ-proj₂ :
    e ↪ e' →
    `proj₂ e ↪ `proj₂ e'

  ξ-,₁ :
    e₁ ↪ e₁' →
    (e₁ `, e₂) ↪ (e₁' `, e₂)

  ξ-,₂ :
    e₂ ↪ e₂' →
    (e₁ `, e₂) ↪ (e₁ `, e₂')

  -- Equality Types

  β-J :
    `J t `refl e ↪ e

  ξ-≡₁ :
    t₁ ↪ t₁' →
    (t₁ `≡ t₂) ↪ (t₁' `≡ t₂)

  ξ-≡₂ :
    t₂ ↪ t₂' →
    (t₁ `≡ t₂) ↪ (t₁ `≡ t₂')

  ξ-J₁ :
    t ↪ t' →
    `J t e₁ e₂ ↪ `J t' e₁ e₂

  ξ-J₂ :
    e₁ ↪ e₁' →
    `J t e₁ e₂ ↪ `J t e₁' e₂

  ξ-J₃ :
    e₂ ↪ e₂' →
    `J t e₁ e₂ ↪ `J t e₁ e₂'

data _↪*_ : S ⊢ s → S ⊢ s → Set where
  ↪*-refl : e ↪* e
  ↪*-step : e₁ ↪ e₂ → e₂ ↪* e₃ → e₁ ↪* e₃

record _≈_ (e₁ e₂ : S ⊢ s) : Set where
  constructor mk-≈
  field
    ≈-e     : S ⊢ s
    ≈-e₁↪*e : e₁ ↪* ≈-e
    ≈-e₂↪*e : e₂ ↪* ≈-e

open _≈_ public

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where

  -- Variables

  ⊢` : ∀ {x : S ∋ s} {T : S ∶⊢ s} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T

  -- Pi Types

  ⊢∀ :
    Γ ⊢ t₁ ∶ `Set →
    Γ ▶ t₁ ⊢ t₂ ∶ `Set →
    Γ ⊢ ∀[x∶ t₁ ] t₂ ∶ `Set

  ⊢λ :
    Γ ⊢ t₁ ∶ `Set →
    Γ ▶ t₁ ⊢ e ∶ t₂ →
    Γ ⊢ λx e ∶ ∀[x∶ t₁ ] t₂

  ⊢· : ∀ {Γ : Ctx S} →
    Γ ⊢ e₁ ∶ ∀[x∶ t₁ ] t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ

  -- Sigma Types

  ⊢∃ :
    Γ ⊢ t₁ ∶ `Set →
    Γ ▶ t₁ ⊢ t₂ ∶ `Set →
    Γ ⊢ ∃[x∶ t₁ ] t₂ ∶ `Set

  ⊢, : ∀ {Γ : Ctx S} →
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ e₂ ∶ t₂ ⋯ₛ ⦅ e₁ ⦆ₛ →
    Γ ⊢ e₁ `, e₂ ∶ ∃[x∶ t₁ ] t₂

  ⊢proj₁ : ∀ {Γ : Ctx S} →
    Γ ⊢ e ∶ ∃[x∶ t₁ ] t₂ →
    Γ ⊢ `proj₁ e ∶ t₁ 

  ⊢proj₂ : ∀ {Γ : Ctx S} →
    Γ ⊢ e ∶ ∃[x∶ t₁ ] t₂ →
    Γ ⊢ `proj₂ e ∶ t₂ ⋯ₛ ⦅ `proj₁ e ⦆ₛ 

  -- Equality Types

  ⊢≡ :
    Γ ⊢ e₁ ∶ t →
    Γ ⊢ e₂ ∶ t →
    Γ ⊢ e₁ `≡ e₂ ∶ `Set

  ⊢refl :
    Γ ⊢ e ∶ t →
    Γ ⊢ `refl ∶ e `≡ e

  ⊢J : ∀ {Γ : Ctx S} {t : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ▶ t' ⊢ t ∶ `Set →
    Γ ⊢ u₁ ∶ t' →
    Γ ⊢ u₂ ∶ t' →
    Γ ⊢ e₁ ∶ u₁ `≡ u₂ →
    Γ ⊢ e₂ ∶ t ⋯ₛ ⦅ u₁ ⦆ₛ →
    Γ ⊢ `J t e₁ e₂ ∶ t ⋯ₛ ⦅ u₂ ⦆ₛ

  -- Universe Type

  ⊢Set :
    Γ ⊢ `Set ∶ `Set

  -- Conversion

  ⊢≈ :
    t ≈ t' →
    Γ ⊢ e ∶ t →
    Γ ⊢ e ∶ t'

open import Kitty.Typing.Typing compose-traversal ctx-repr
typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }

variable
  _∋/⊢_ : List (Sort Var) → Sort Var → Set
