module Kitty.Examples.STLC-Pat-Derive.Definitions where

open import Kitty.Term.Prelude using (_∋_; _▷_; _▷▷_; List; []) public
open import Kitty.Term.Modes using (Modes; Terms)
open import Kitty.Util.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _∈cs_
infixr  5  λx_ _∷_
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
  𝕡 : List Modeᵥ → Modeₜ  -- Patterns
  ℙ : List Modeᵥ → Modeₜ  -- Pattern Types
  𝕔 : Modeₜ  -- Clause
  𝕔𝕤 : Modeₜ  -- Clauses
  ℂ : Modeₜ  -- Clause Type

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

↑ₜ : Modeₜ → Modeₜ
↑ₜ = λ { 𝕖 → 𝕥 ; (𝕡 µ) → ℙ µ ; 𝕥 → 𝕥 ; (ℙ µ) → ℙ µ ; 𝕔 → ℂ ; 𝕔𝕤 → ℂ ; ℂ → ℂ }

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
    `[_]_     : ∀ {m M}  →  M ≡ m→M m  →  µ ∋ m  →  µ ⊢ M
    λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    _`→_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥

    𝟘 𝟙       : µ ⊢ 𝕥
    _`×_ _`⊎_ : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
    tt        : µ ⊢ 𝕖
    _,_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    inj₁ inj₂ : µ ⊢ 𝕖  →  µ ⊢ 𝕖

    match     : µ ⊢ 𝕖  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕖
    _⇒_       : µ ⊢ 𝕡 µ'  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕔
    []        : µ ⊢ 𝕔𝕤
    _∷_       : µ ⊢ 𝕔  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕔𝕤
    `ᵖ        : µ ⊢ 𝕡 ([] ▷ 𝕖)
    _,ᵖ_      : µ ⊢ 𝕡 µ₁  →  (µ ▷▷ µ₁) ⊢ 𝕡 µ₂  →  µ ⊢ 𝕡 (µ₁ ▷▷ µ₂)
    inj₁ᵖ inj₂ᵖ : µ ⊢ 𝕡 µ'  →  µ ⊢ 𝕡 µ'
    ttᵖ       : µ ⊢ 𝕡 []

    []ᵖ       : µ ⊢ ℙ []
    _▶ᵖ_      : µ ⊢ ℙ µ₁ → (µ ▷▷ µ₁) ⊢ 𝕥 → µ ⊢ ℙ (µ₁ ▷ 𝕖)
    Clause    : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ ℂ

  CtxP' : List Modeᵥ → List Modeᵥ → Set
  CtxP' µ µ' = ∀ m → (x : µ' ∋ m) →  (µ ▷▷ drop-∈ x µ') ⊢ ↑ₜ (m→M m)

pattern `_ x = `[ refl ] x

_▶▶ᵖ_ : µ ⊢ ℙ µ₁ → (µ ▷▷ µ₁) ⊢ ℙ µ₂ → µ ⊢ ℙ (µ₁ ▷▷ µ₂)
P₁ ▶▶ᵖ (`[_]_ {m = 𝕖} () _)
P₁ ▶▶ᵖ []ᵖ       = P₁
_▶▶ᵖ_ {µ} {µ₁} {µ₂ = µ₂ ▷ _} P₁ (P₂ ▶ᵖ t) =
  let sub = subst (_⊢ 𝕥) (sym (++-assoc µ₂ µ₁ µ)) in
  (P₁ ▶▶ᵖ P₂) ▶ᵖ sub t
-- _▶▶ᵖ_ {µ} {µ₁} {µ₂ = µ₂ ▷ _} P₁ (P₂ ▶ᵖ t) rewrite sym (++-assoc µ₂ µ₁ µ) = (P₁ ▶▶ᵖ P₂) ▶ᵖ t

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  p p₁ p₂ p₃ p' p₁' p₂' : µ ⊢ 𝕡 µ'
  P P₁ P₂ P₃ P' P₁' P₂' : µ ⊢ ℙ µ'
  c  c'                 : µ ⊢ 𝕔
  cs cs'                : µ ⊢ 𝕔𝕤
  C C'                  : µ ⊢ ℂ
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)
unquoteDecl D = derive 𝕄 _⊢_ D
open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeModes terms

-- Each variable mode corresponds to a term mode that represents its type.
type-modes : TypeModes
type-modes = record { ↑ₜ = ↑ₜ }

open TypeModes type-modes public hiding (↑ₜ)

open import Kitty.Typing.CtxRepr type-modes

ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

PatTy→Ctx' : µ ⊢ ℙ µ' → CtxP' µ µ' 
PatTy→Ctx' (`[_]_ {m = 𝕖} () x)
PatTy→Ctx' []ᵖ = λ _ ()
PatTy→Ctx' (P ▶ᵖ t) = PatTy→Ctx' P ▶' t

-- Type System -----------------------------------------------------------------

data Matches : µ₁ ⊢ 𝕖 → µ₂ ⊢ 𝕡 µ' → Set where
  M-` :
    Matches {µ₂ = µ₂} e `ᵖ
  M-tt :
    Matches {µ₂ = µ₂} (tt {µ = µ}) ttᵖ
  M-, :
    Matches e₁ p₁ →
    Matches e₂ p₂ →
    Matches (e₁ , e₂) (p₁ ,ᵖ p₂)
  M-inj₁ :
    Matches e p →
    Matches (inj₁ e) (inj₁ᵖ p)
  M-inj₂ :
    Matches e p →
    Matches (inj₂ e) (inj₂ᵖ p)

data Canonical : µ₁ ⊢ 𝕖 → µ₂ ⊢ 𝕥 → Set where
  C-λ :
    Canonical (λx e) (t₁ `→ t₂)
  C-tt :
    Canonical (tt {µ = µ₁}) (𝟙 {µ = µ₂})
  C-, :
    Canonical e₁ t₁ →
    Canonical e₂ t₂ →
    Canonical (e₁ , e₂) (t₁ `× t₂)
  C-inj₁ :
    Canonical e t₁ →
    Canonical (inj₁ e) (t₁ `⊎ t₂)
  C-inj₂ :
    Canonical e t₂ →
    Canonical (inj₂ e) (t₁ `⊎ t₂)

data _∈cs_ (c : µ ⊢ 𝕔) : µ ⊢ 𝕔𝕤 → Set where
  here : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ≡ c' → c ∈cs (c' ∷ cs)
  there : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ∈cs cs → c ∈cs (c' ∷ cs)

Exhaustive : µ ⊢ 𝕔𝕤 → µ ⊢ 𝕥 → Set
Exhaustive {µ} cs t =
  ∀ {µ'} {e : µ' ⊢ 𝕖} →
  Canonical e t →
  ∃[ µ' ] Σ[ p ∈ µ ⊢ 𝕡 µ' ] ∃[ e' ]
    (p ⇒ e') ∈cs cs × Matches e p

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  ⊢-` : ∀ {µ} {m} {Γ : Ctx µ} {T : µ ∶⊢ m→M m} {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢-λ : {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wknᵣ →
    Γ ⊢ λx e ∶ t₁ `→ t₂
  ⊢-· :
    Γ ⊢ e₁ ∶ t₁ `→ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢-tt :
    Γ ⊢ tt ∶ 𝟙
  ⊢-, :
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ e₂ ∶ t₂ →
    Γ ⊢ e₁ , e₂ ∶ t₁ `× t₂
  ⊢-inj₁ :
    Γ ⊢ e₁ ∶ t₁ →
    Γ ⊢ inj₁ e₁ ∶ t₁ `⊎ t₂
  ⊢-inj₂ :
    Γ ⊢ e₂ ∶ t₂ →
    Γ ⊢ inj₂ e₂ ∶ t₁ `⊎ t₂
  ⊢-match :
    Γ ⊢ e ∶ t →
    Γ ⊢ cs ∶ Clause t t' →
    Exhaustive cs t →
    Γ ⊢ match e cs ∶ t'
  ⊢-clause : ∀ {Γ : Ctx µ} {p : µ ⊢ 𝕡 µ'} {t' : µ ⊢ 𝕥} →
    Γ ⊢ p ∶ P →
    (Γ ▶▶ PatTy→Ctx' P) ⊢ e ∶ wk* µ' t' →
    Γ ⊢ (p ⇒ e) ∶ Clause t t' -- TODO: where does t come from...
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
  ⊢-,ᵖ : ∀ {µ µ₁ µ₂} {Γ : Ctx µ} {p₁ : µ ⊢ 𝕡 µ₁} {P₁ : µ ⊢ ℙ µ₁} {p₂ : µ ▷▷ µ₁ ⊢ 𝕡 µ₂} {P₂ : µ ▷▷ µ₁ ⊢ ℙ µ₂} →
    Γ ⊢ p₁ ∶ P₁ →
    (Γ ▶▶ PatTy→Ctx' P₁) ⊢ p₂ ∶ P₂ →
    Γ ⊢ p₁ ,ᵖ p₂ ∶ (P₁ ▶▶ᵖ P₂)
  ⊢-inj₁ᵖ :
    Γ ⊢ p ∶ P →
    Γ ⊢ inj₁ᵖ p ∶ P
  ⊢-inj₂ᵖ :
    Γ ⊢ p ∶ P →
    Γ ⊢ inj₂ᵖ p ∶ P

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `ⁿ_  : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    match : Neutral e₁ → Neutral (match e₁ cs)

  data Value : µ ⊢ M → Set where
    λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    _,_     : Value e₁ → Value e₂ → Value (e₁ , e₂)
    inj₁    : Value e → Value (inj₁ e)
    inj₂    : Value e → Value (inj₂ e)
    tt      : Value (tt {µ})
    neutral : Neutral e → Value e

matching-sub : ∀ {µ µ' µ''} {e : µ ⊢ 𝕖} {p : µ' ⊢ 𝕡 µ''} → Matches e p → µ'' →ₛ µ
matching-sub {e = e} M-` = ⦅ e ⦆ₛ₀
matching-sub M-tt        = []*
matching-sub (M-, m₁ m₂) = matching-sub m₁ ∥ₛ matching-sub m₂
matching-sub (M-inj₁ m)  = matching-sub m
matching-sub (M-inj₂ m)  = matching-sub m

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-match : ∀ {µ µ'} {e : µ ⊢ 𝕖} {cs : µ ⊢ 𝕔𝕤} {p : µ ⊢ 𝕡 µ'} {e' : µ ▷▷ µ' ⊢ 𝕖} {σ : µ' →ₛ µ} →
    (p ⇒ e') ∈cs cs →
    (m : Matches e p) →
    matching-sub m ≡ σ →
    match e cs ↪ e' ⋯ₛ (idₛ ∥ₛ σ)
  -- TODO: ξ-match ...
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
