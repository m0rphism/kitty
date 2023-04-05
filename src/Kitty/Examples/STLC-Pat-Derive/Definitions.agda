module Kitty.Examples.STLC-Pat-Derive.Definitions where

open import Kitty.Term.Prelude using (_∋_; _▷_; _▷▷_; List; []) public
open import Kitty.Term.Modes using (Modes; Terms)
open import Kitty.Util.List

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_
infixr  6  _⇒_
infixl  6  _·_
infix   7  `_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕡 : Modeₜ  -- Patterns
  ℙ : Modeₜ  -- Pattern Types
  𝕔𝕤 : Modeₜ  -- Clauses
  ℂ𝕊 : Modeₜ  -- Clause Types

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

↑ₜ : Modeₜ → Modeₜ
↑ₜ = λ { 𝕖 → 𝕥 ; 𝕡 → ℙ ; 𝕥 → 𝕥 ; ℙ → ℙ ;  𝕔𝕤 → ℂ𝕊 ; ℂ𝕊 → ℂ𝕊 }

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

mutual

  -- Expressions and Types
  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
    λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    _`→_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥

    𝟘 𝟙       : µ ⊢ 𝕥
    _`×_ _`⊎_ : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
    tt        : µ ⊢ 𝕖
    _,_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    inj₁ inj₂ : µ ⊢ 𝕖  →  µ ⊢ 𝕖

    match     : µ ⊢ 𝕖  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕖
    []        : µ ⊢ 𝕔𝕤
    _⇒_;_     : µ ⊢ 𝕡  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕔𝕤
    `ᵖ        : µ ⊢ 𝕡
    _,ᵖ_      : µ ⊢ 𝕡  →  µ ⊢ 𝕡  →  µ ⊢ 𝕡
    inj₁ᵖ inj₂ᵖ : µ ⊢ 𝕡  →  µ ⊢ 𝕡
    ttᵖ       : µ ⊢ 𝕡

    Pat       : ∀ {µ'}  →  µ ⊢ 𝕥  →  CtxP' µ µ'  →  µ ⊢ ℙ
    Clause    : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ ℂ𝕊

  CtxP' : List Modeᵥ → List Modeᵥ → Set
  CtxP' µ µ' = ∀ {m} → (x : µ' ∋ m) → drop-∈ x (µ ▷▷ µ') ⊢ ↑ₜ (m→M m)


variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  p p₁ p₂ p₃ p' p₁' p₂' : µ ⊢ 𝕡
  cs cs'                : µ ⊢ 𝕔𝕤
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)
unquoteDecl D = derive 𝕄 _⊢_ D
open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.Types terms

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = ↑ₜ }

open KitType kit-type public hiding (↑ₜ)

open import Kitty.Typing.OPE compose-traversal kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  τ-` : ∀ {µ} {m} {Γ : Ctx µ} {T : µ ∶⊢ m→M m} {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  τ-λ : {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wknᵣ →
    Γ ⊢ λx e ∶ t₁ `→ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ `→ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-tt :
    Γ ⊢ tt ∶ 𝟙
  τ-, :
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ e₂ ∶ t₂ →
    Γ ⊢ e₁ , e₂ ∶ t₁ `× t₂
  τ-inj₁ :
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ inj₁ e₁ ∶ t₁ `⊎ t₂
  τ-inj₂ :
    Γ ⊢ e₂ ∶ t₂ →
    Γ ⊢ inj₂ e₂ ∶ t₁ `⊎ t₂
  τ-match :
    Γ ⊢ e ∶ t →
    Γ ⊢ cs ∶ Clause t t' →
    Γ ⊢ match e cs ∶ t'
  τ-clause-[] :
    Γ ⊢ [] ∶ Clause t t'
  τ-clause-∷ :
    Γ ⊢ p ∶ Pat t Γ' →
    (Γ ▶▶ Γ') ⊢ e ∶ t' →
    Γ ⊢ cs ∶ Clause t t' →
    Γ ⊢ (p ⇒ e ; cs) ∶ Clause t t'


-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ M → Set where
--     `_  : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

--   data Value : µ ⊢ M → Set where
--     λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
--     neutral : Neutral e → Value e

-- data _↪_ : µ ⊢ M → µ ⊢ M → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
--   ξ-λ :
--     e ↪ e' →
--     λx e ↪ λx e'
--   ξ-·₁ :
--     e₁ ↪ e₁' →
--     e₁ · e₂ ↪ e₁' · e₂
--   ξ-·₂ :
--     e₂ ↪ e₂' →
--     e₁ · e₂ ↪ e₁ · e₂'
