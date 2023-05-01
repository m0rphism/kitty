module Kitty.Examples.LambdaPiPat-Derive-Sem.Definitions where

open import Data.List.Relation.Unary.Any using (here; there) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.List.Properties using (++-assoc)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_; _▷▷_) public
open import Kitty.Term.Modes using (Modes)
open import Kitty.Util.Closures
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _∈cs_
infixr  6  _⇒_
infixr  5  λx_  ∀[x∶_]_ Σ[x∶_]_ _∷_
infixl  6  _·_
infix   7  `_

-- Modes -----------------------------------------------------------------------

data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables

data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕡 : List Modeᵥ → Modeₜ  -- Patterns
  ℙ : List Modeᵥ → Modeₜ  -- Pattern Types
  𝕔 : Modeₜ  -- Clause
  𝕔𝕤 : Modeₜ  -- Clauses
  ℂ : Modeₜ  -- Clause Type

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

↑ₜ : Modeₜ → Modeₜ
↑ₜ = λ { 𝕖 → 𝕖 ; (𝕡 µ) → ℙ µ ; (ℙ µ) → ℙ µ ; 𝕔 → ℂ ; 𝕔𝕤 → ℂ ; ℂ → ℂ }

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
  `[_]_     : ∀ {m M}  →  M ≡ m→M m  →  µ ∋ m  →  µ ⊢ M

  ∀[x∶_]_ : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  λx_     : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_     : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  Σ[x∶_]_ : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _,_     : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  `⊤      : µ ⊢ 𝕖
  tt      : µ ⊢ 𝕖

  ★       : µ ⊢ 𝕖

  match   : µ ⊢ 𝕖  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕖
  _⇒_     : µ ⊢ 𝕡 µ'  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕔
  []      : µ ⊢ 𝕔𝕤
  _∷_     : µ ⊢ 𝕔  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕔𝕤
  `ᵖ      : µ ⊢ 𝕡 ([] ▷ 𝕖)
  _,ᵖ_    : µ ⊢ 𝕡 µ₁  →  (µ ▷▷ µ₁) ⊢ 𝕡 µ₂  →  µ ⊢ 𝕡 (µ₁ ▷▷ µ₂)
  ttᵖ     : µ ⊢ 𝕡 []
  -- dotᵖ    : µ ⊢ 𝕖 → µ ⊢ 𝕡 []

  []ᵖ     : µ ⊢ ℙ []
  _▶ᵖ_    : µ ⊢ ℙ µ₁  →  (µ ▷▷ µ₁) ⊢ 𝕖  →  µ ⊢ ℙ (µ₁ ▷ 𝕖)
  Clause  : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ ℂ

pattern `_ x = `[ refl ] x

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : µ ⊢ 𝕖
  p p₁ p₂ p₃ p' p₁' p₂' p₃' : µ ⊢ 𝕡 µ'
  P P₁ P₂ P₃ P' P₁' P₂' P₃' : µ ⊢ ℙ µ'
  c c₁ c₂ c₃ c' c₁' c₂' c₃' : µ ⊢ 𝕔
  cs cs₁ cs₂ cs₃ cs' cs₁' cs₂' cs₃' : µ ⊢ 𝕔𝕤
  C C₁ C₂ C₃ C' C₁' C₂' C₃' : µ ⊢ ℂ
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
kit-type = record { ↑ₜ = ↑ₜ }

open KitType kit-type public hiding (↑ₜ)

open import Kitty.Typing.CtxRepr kit-type

ctx-repr : CtxRepr
ctx-repr = List-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal kit-type ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `ⁿ_  : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
    _·_   : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    match : Neutral e → Neutral (match e cs)

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
    tt      : Value {µ} tt

    ★       : Value {µ} ★

    neutral : Neutral e → Value e

data Matches : µ₁ ⊢ 𝕖 → µ₂ ⊢ 𝕡 µ' → Set where
  M-` :
    Matches {µ₂ = µ₂} e `ᵖ
  M-tt :
    Matches {µ₂ = µ₂} (tt {µ = µ}) ttᵖ
  M-, :
    Matches e₁ p₁ →
    Matches e₂ p₂ →
    Matches (e₁ , e₂) (p₁ ,ᵖ p₂)

matching-sub : ∀ {µ µ' µ''} {e : µ ⊢ 𝕖} {p : µ' ⊢ 𝕡 µ''} → Matches e p → µ'' →ₛ µ
matching-sub {e = e} M-` = ⦅ e ⦆ₛ₀
matching-sub M-tt        = []*
matching-sub (M-, m₁ m₂) = matching-sub m₁ ∥ₛ matching-sub m₂

data _∈cs_ (c : µ ⊢ 𝕔) : µ ⊢ 𝕔𝕤 → Set where
  here : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ≡ c' → c ∈cs (c' ∷ cs)
  there : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ∈cs cs → c ∈cs (c' ∷ cs)

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  β-match : ∀ {µ µ'} {e : µ ⊢ 𝕖} {cs : µ ⊢ 𝕔𝕤} {p : µ ⊢ 𝕡 µ'} {e' : µ ▷▷ µ' ⊢ 𝕖} {σ : µ' →ₛ µ} →
    (p ⇒ e') ∈cs cs →
    (m : Matches e p) →
    matching-sub m ≡ σ →
    match e cs ↪ e' ⋯ₛ (idₛ ∥ₛ σ)
  -- TODO: ξ-match ...
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

data Canonical : µ₁ ⊢ 𝕖 → µ₂ ⊢ 𝕖 → Set where
  C-λ :
    Canonical (λx e) (∀[x∶ t₁ ] t₂)
  C-tt :
    Canonical (tt {µ = µ₁}) (`⊤ {µ = µ₂})
  C-, :
    Canonical e₁ t₁ →
    Canonical e₂ t₂ →
    Canonical (e₁ , e₂) (Σ[x∶ t₁ ] t₂)

Exhaustive : µ ⊢ 𝕔𝕤 → µ ⊢ 𝕖 → Set
Exhaustive {µ} cs t =
  ∀ {µ'} {e : µ' ⊢ 𝕖} →
  Canonical e t →
  ∃[ µ' ] Σ[ p ∈ µ ⊢ 𝕡 µ' ] ∃[ e' ]
    (p ⇒ e') ∈cs cs × Matches e p

PatTy→Ctx' : µ ⊢ ℙ µ' → Ctx' µ µ' 
PatTy→Ctx' (`[_]_ {m = 𝕖} () _)
PatTy→Ctx' []ᵖ      = ∅'
PatTy→Ctx' (P ▶ᵖ t) = PatTy→Ctx' P ▶' t

_▶▶ᵖ_ : µ ⊢ ℙ µ₁ → (µ ▷▷ µ₁) ⊢ ℙ µ₂ → µ ⊢ ℙ (µ₁ ▷▷ µ₂)
P₁ ▶▶ᵖ `[_]_ {m = 𝕖} () _
P₁ ▶▶ᵖ []ᵖ       = P₁
_▶▶ᵖ_ {µ} {µ₁} {µ₂ = µ₂ ▷ _} P₁ (P₂ ▶ᵖ t) =
  let sub = subst (_⊢ 𝕖) (sym (++-assoc µ₂ µ₁ µ)) in
  (P₁ ▶▶ᵖ P₂) ▶ᵖ sub t

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
  ⊢tt :
    Γ ⊢ tt ∶ `⊤
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
  ⊢-match :
    Γ ⊢ e ∶ t →
    Γ ⊢ cs ∶ Clause t t' →
    Exhaustive cs t →
    Γ ⊢ match e cs ∶ t'
  ⊢-clause : ∀ {Γ : Ctx µ} {p : µ ⊢ 𝕡 µ'} {t' : µ ⊢ 𝕖} →
    Γ ⊢ p ∶ P →
    (Γ ▶▶ PatTy→Ctx' P) ⊢ e ∶ wk* µ' t' →
    Γ ⊢ (p ⇒ e) ∶ Clause t t'
  ⊢-clause-[] :
    Γ ⊢ [] ∶ Clause t t'
  ⊢-clause-∷ : ∀ {Γ : Ctx µ} →
    Γ ⊢ c  ∶ Clause t t' →
    Γ ⊢ cs ∶ Clause t t' →
    Γ ⊢ (c ∷ cs) ∶ Clause t t'
  ⊢-ttᵖ :
    Γ ⊢ ttᵖ ∶ []ᵖ
  ⊢-`ᵖ :
    Γ ⊢ `ᵖ ∶ []ᵖ ▶ᵖ t
  ⊢-,ᵖ :
    ∀ {µ µ₁ µ₂} {Γ : Ctx µ} {p₁ : µ ⊢ 𝕡 µ₁} {P₁ : µ ⊢ ℙ µ₁} {p₂ : µ ▷▷ µ₁ ⊢ 𝕡 µ₂} {P₂ : µ ▷▷ µ₁ ⊢ ℙ µ₂} →
    Γ ⊢ p₁ ∶ P₁ →
    (Γ ▶▶ PatTy→Ctx' P₁) ⊢ p₂ ∶ P₂ →
    Γ ⊢ p₁ ,ᵖ p₂ ∶ (P₁ ▶▶ᵖ P₂)

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
