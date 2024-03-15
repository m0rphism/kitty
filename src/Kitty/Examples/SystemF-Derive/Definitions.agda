module Kitty.Examples.SystemF-Derive.Definitions where

open import Data.Product using (_,_)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (Terms; SortTy; Var; NoVar)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Modes -----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖 : Sort Var    -- Expressions
  𝕥 : Sort Var    -- Types
  𝕜 : Sort NoVar  -- Kinds

variable
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : List (Sort Var)
  x y z                     : S ∋ s

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : ∀ {st} → List (Sort Var) → Sort st → Set where
  `_        : ∀ {s}  →  S ∋ s  →  S ⊢ s
  λx_       : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  Λα_       : S ▷ 𝕥 ⊢ 𝕖  →  S ⊢ 𝕖
  ∀[α∶_]_   : S ⊢ 𝕜  →  S ▷ 𝕥 ⊢ 𝕥  →  S ⊢ 𝕥
  _·_       : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  _∙_       : S ⊢ 𝕖  →  S ⊢ 𝕥  →  S ⊢ 𝕖
  _⇒_       : S ⊢ 𝕥  →  S ⊢ 𝕥  →  S ⊢ 𝕥
  ★         : S ⊢ 𝕜

variable
  e e₁ e₂ e₃ e' e₁' e₂' : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : S ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂' : S ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂' : S ⊢ s

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)

unquoteDecl D = derive Sort _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeSorts terms

-- Each variable sort corresponds to a term sort that represents its type.
type-sorts : TypeSorts
type-sorts = record { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 } }

open TypeSorts type-sorts public

open import Kitty.Typing.CtxRepr type-sorts

ctx-repr : CtxRepr
ctx-repr = List-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {x : S ∋ s} {T : S ∶⊢ s} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ : ∀ {e : S ▷ 𝕖 ⊢ 𝕖} →
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkₖ _ id →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ :
    Γ ▶ k ⊢ e ∶ t₂ →
    Γ ⊢ Λα e ∶ ∀[α∶ k ] t₂
  ⊢· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙ : {Γ : Ctx S} →
    Γ ▶ k₂ ⊢ t₁ ∶ k₁ →
    Γ ⊢ t₂ ∶ k₂ →
    Γ ⊢ e₁ ∶ ∀[α∶ k₂ ] t₁ →
    Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆ₛ
  ⊢τ :
    Γ ⊢ t ∶ ★

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : S ⊢ s → Set where
    `_  : ∀ (x : S ∋ s) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙t : Neutral e₁ → Neutral (e₁ ∙ t₂)

  data Value : S ⊢ s → Set where
    λx_     : ∀ (e : (S ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    Λα_     : ∀ (e : (S ▷ 𝕥) ⊢ 𝕖) → Value (Λα e)
    neutral : Neutral e → Value e

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ : ∀ {e₂ : S ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  β-Λ : ∀ {t₂ : S ⊢ 𝕥} →
    (Λα e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆ₛ
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-Λ :
    e ↪ e' →
    Λα e ↪ Λα e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙₁ :
    e₁ ↪ e₁' →
    e₁ ∙ t₂ ↪ e₁' ∙ t₂
