module Kitty.Examples.LambdaPi-Derive-Sem.Definitions where

open import Data.List.Relation.Unary.Any using (here; there) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Modes using (Modes)
open import Kitty.Util.Closures

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  ∀[x∶_]_
-- infixr  6  _⇒_
infixl  6  _·_
infix   7  `_

-- Modes -----------------------------------------------------------------------

-- Variable and Term Modes
data Mode : Set where
  𝕖 : Mode  -- Expression-level variables

-- Mapping variable modes to the term modes they represent.
m→M : Mode → Mode
m→M m = m

𝕄 : Modes
𝕄 = record { VarMode = Mode ; TermMode = Mode ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Mode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Mode
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Mode → Mode → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
  λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀[x∶_]_   : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  ★         : µ ⊢ 𝕖

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : µ ⊢ M
  E E₁ E₂ E₃ E' E₁' E₂' E₃' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)

unquoteDecl D = derive 𝕄 _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.Types terms

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { m → m } }

open KitType kit-type public

open import Kitty.Typing.CtxRepr kit-type

ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal kit-type ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `_     : ∀ (x : µ ∋ m) → Neutral (` x)
    _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

  data Value : µ ⊢ M → Set where
    λx_     : ∀ {e : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value e
              → Value (λx e)
    ∀[x∶_]_ : ∀ {t₁ : µ ⊢ 𝕖} {t₂ : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value t₁
              → Value t₂
              → Value (∀[x∶ t₁ ] t₂)
    ★       : Value {µ} ★
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-∀₁ :
    t₁ ↪ t₁' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂
  ξ-∀₂ :
    t₂ ↪ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁ ] t₂'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

open import Kitty.Semantics.ISemantics compose-traversal kit-type ctx-repr

semantics : Semantics
semantics = record { _↪_ = _↪_ }

open Semantics semantics public hiding (_↪_) renaming (module WithConfluence to ↪-WithConfluence)

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  ⊢` : ∀ {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ :
    Γ ⊢ t₁ ∶ ★ →
    Γ ▶ t₁ ⊢ e ∶ t₂ →
    Γ ⊢ λx e ∶ ∀[x∶ t₁ ] t₂
  ⊢∀ :
    Γ ⊢ t₁ ∶ ★ →
    Γ ▶ t₁ ⊢ t₂ ∶ ★ →
    Γ ⊢ ∀[x∶ t₁ ] t₂ ∶ ★
  ⊢· :
    Γ ⊢ e₁ ∶ ∀[x∶ t₁ ] t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ
  ⊢★ :
    Γ ⊢ ★ ∶ ★
  ⊢≣ :
    t ≣ t' →
    Γ ⊢ e ∶ t →
    Γ ⊢ e ∶ t'

-- Values : Ctx µ → Set
-- Values {µ} Γ = ∀ {m} (x : µ ∋ m) → Value (Γ x) 

-- Values-ext : ∀ {Γ : Ctx µ} → Values Γ → Value t → Values (Γ ▶ t)
-- Values-ext {µ} VΓ Vt (here refl) = Vt
-- Values-ext {µ} VΓ Vt (there x) = VΓ x

-- postulate
--   Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- Value-wk-telescope {x = here refl} VΓx = {!VΓx!}
-- -- Value-wk-telescope {x = there x} VΓx = {!!}

-- ⊢-Value :
--   ∀ {µ} {Γ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M}
--   → Values Γ
--   → Γ ⊢ e ∶ t
--   → Value t
-- ⊢-Value {Γ = Γ} VΓ (⊢` {x = x} refl) = Value-wk-telescope {Γ = Γ} (VΓ x)
-- ⊢-Value VΓ (⊢λ Vt₁ ⊢e₁ ⊢e₂)          = ∀[x∶ Vt₁ ] ⊢-Value (Values-ext VΓ Vt₁) ⊢e₂
-- ⊢-Value VΓ (⊢∀ t₁⇓t₁' ⊢t₁ ⊢t₂)       = ★
-- ⊢-Value VΓ (⊢· ⊢e₁ ⊢e₂ ⇓[ _ , Vt ])  = Vt
-- ⊢-Value VΓ ⊢★                        = ★
