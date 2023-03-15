module Kitty.Examples.SystemF-Derive.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Modes using (Modes)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables
  𝕥 : Modeᵥ  -- Type-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖
m→M 𝕥 = 𝕥

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `[_]_     : ∀ {m M}  →  m→M m ≡ M  →  µ ∋ m  →  µ ⊢ M
  λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  Λα_       : µ ▷ 𝕥 ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀[α∶_]_   : µ ⊢ 𝕜  →  µ ▷ 𝕥 ⊢ 𝕥  →  µ ⊢ 𝕥
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _∙_       : µ ⊢ 𝕖  →  µ ⊢ 𝕥  →  µ ⊢ 𝕖
  _⇒_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  ★         : µ ⊢ 𝕜

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂' : µ ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive.Traversal using (derive-traversal; module Derived)
unquoteDecl traversal = derive-traversal 𝕄 _⊢_ traversal
open Derived traversal public
open Sub-Functional public

pattern `_ x = `[ refl ] x  

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.Types terms

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

open import Kitty.Typing.OPE compose-traversal kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  ⊢` : ∀ {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ :
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkₖ _ id →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ :
    Γ ▶ k ⊢ e ∶ t₂ →
    Γ ⊢ Λα e ∶ ∀[α∶ k ] t₂
  ⊢· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙ : {Γ : Ctx µ} →
    Γ ▶ k₂ ⊢ t₁ ∶ k₁ →
    Γ ⊢ t₂ ∶ k₂ →
    Γ ⊢ e₁ ∶ ∀[α∶ k₂ ] t₁ →
    Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆ₛ
  ⊢τ :
    Γ ⊢ t ∶ ★

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `[_]_  : ∀ (eq : m→M m ≡ M) (x : µ ∋ m) → Neutral (`[ eq ] x)
    _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙_    : Neutral e₁ → Value t₂ → Neutral (e₁ ∙ t₂)

  data Value : µ ⊢ M → Set where
    λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    Λα_     : ∀ (e : (µ ▷ 𝕥) ⊢ 𝕖) → Value (Λα e)
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  β-Λ : ∀ {t₂ : µ ⊢ 𝕥} →
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
