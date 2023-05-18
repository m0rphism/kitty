module Kitty.Examples.LambdaPiSigma-Derive-Sem.Definitions where

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

open Modes 𝕄 using (Scoped) public

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Mode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Mode
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Mode → Mode → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m

  ∀[x∶_]_   : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  Σ[x∶_]_   : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _,_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  `proj₁    : µ ⊢ 𝕖  →  µ ⊢ 𝕖
  `proj₂    : µ ⊢ 𝕖  →  µ ⊢ 𝕖

  `⊤        : µ ⊢ 𝕖
  `tt       : µ ⊢ 𝕖

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

open import Kitty.Typing.TypeModes terms

-- Each variable mode corresponds to a term mode that represents its type.
type-modes : TypeModes
type-modes = record { ↑ₜ = λ { m → m } }

open TypeModes type-modes public

open import Kitty.Typing.CtxRepr type-modes

ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `_     : ∀ (x : µ ∋ m) → Neutral (` x)
    _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    `proj₁ : Neutral e → Neutral (`proj₁ e)
    `proj₂ : Neutral e → Neutral (`proj₂ e)

  data Value : µ ⊢ M → Set where
    ∀[x∶_]_ : ∀ {t₁ : µ ⊢ 𝕖} {t₂ : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value t₁
              → Value t₂
              → Value (∀[x∶ t₁ ] t₂)
    λx_     : ∀ {e : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value e
              → Value (λx e)

    Σ[x∶_]_ : ∀ {t₁ : µ ⊢ 𝕖} {t₂ : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value t₁
              → Value t₂
              → Value (Σ[x∶ t₁ ] t₂)
    _,_     : Value e₁ → Value e₂ → Value (e₁ , e₂)

    `⊤      : Value {µ} `⊤
    `tt     : Value {µ} `tt

    ★       : Value {µ} ★

    neutral : Neutral e → Value e

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  β-proj₁ :
    `proj₁ (e₁ , e₂) ↪ e₁
  β-proj₂ : ∀ {e₁ : µ ⊢ 𝕖} →
    `proj₂ (e₁ , e₂) ↪ e₂
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-∀₁ :
    t₁ ↪ t₁' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂
  ξ-∀₂ :
    t₂ ↪ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁ ] t₂'
  ξ-Σ₁ :
    t₁ ↪ t₁' →
    Σ[x∶ t₁ ] t₂ ↪ Σ[x∶ t₁' ] t₂
  ξ-Σ₂ :
    t₂ ↪ t₂' →
    Σ[x∶ t₁ ] t₂ ↪ Σ[x∶ t₁ ] t₂'
  ξ-,₁ :
    t₁ ↪ t₁' →
    t₁ , t₂ ↪ t₁' , t₂
  ξ-,₂ :
    t₂ ↪ t₂' →
    t₁ , t₂ ↪ t₁ , t₂'
  ξ-proj₁ :
    e ↪ e' →
    `proj₁ e ↪ `proj₁ e'
  ξ-proj₂ :
    e ↪ e' →
    `proj₂ e ↪ `proj₂ e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

open import Kitty.Semantics.ISemantics compose-traversal ctx-repr

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
  ⊢Σ :
    Γ ⊢ t₁ ∶ ★ →
    Γ ▶ t₁ ⊢ t₂ ∶ ★ →
    Γ ⊢ Σ[x∶ t₁ ] t₂ ∶ ★
  ⊢, : ∀ {e₂ : µ ⊢ 𝕖} →
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ e₂ ∶ t₂ ⋯ₛ ⦅ e₁ ⦆ₛ →
    Γ ⊢ e₁ , e₂ ∶ Σ[x∶ t₁ ] t₂
  ⊢proj₁ :
    Γ ⊢ e ∶ Σ[x∶ t₁ ] t₂ →
    Γ ⊢ `proj₁ e ∶ t₁
  ⊢proj₂ :
    Γ ⊢ e ∶ Σ[x∶ t₁ ] t₂ →
    Γ ⊢ `proj₂ e ∶ t₂ ⋯ₛ ⦅ `proj₁ e ⦆ₛ
  ⊢tt :
    Γ ⊢ `tt ∶ `⊤
  ⊢⊤ :
    Γ ⊢ `⊤ ∶ ★
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
