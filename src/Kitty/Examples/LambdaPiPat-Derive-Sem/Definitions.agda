module Kitty.Examples.LambdaPiPat-Derive-Sem.Definitions where

open import Data.List.Relation.Unary.Any using (here; there) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.List.Properties using (++-assoc)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_; _▷▷_) public
open import Kitty.Term.Modes using (Modes)
open import Kitty.Util.Closures
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Data.Bool using (Bool; true; false)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _∈cs_
infixr  4  _⇒_
infixr  5  λx_  ∀[x∶_]_ Σ[x∶_]_ _∷_
infixl  6  _·_
infix   7  `_

-- Modes -----------------------------------------------------------------------

data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables

data Modeₜ : Set where
  𝕖 : Modeₜ                -- Expressions
  𝕡 : List Modeᵥ → Modeₜ   -- Patterns
  ℙ : List Modeᵥ → Modeₜ   -- Pattern Types
  𝕔 : Modeₜ                -- Clause
  𝕔𝕤 : Modeₜ               -- Clauses
  ℂ : Modeₜ                -- Clause Type
  𝕔𝕥𝕩 : List Modeᵥ → Modeₜ -- Contexts

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

↑ₜ : Modeₜ → Modeₜ
↑ₜ = λ { 𝕖 → 𝕖 ; (𝕡 µ) → ℙ µ ; 𝕔 → ℂ ; 𝕔𝕤 → ℂ ; (ℙ µ) → ℙ µ ; (𝕔𝕥𝕩 µ) → 𝕔𝕥𝕩 µ; ℂ → ℂ }

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
  -- Expressions
  `[_]_     : ∀ {m M}  →  M ≡ m→M m  →  µ ∋ m  →  µ ⊢ M

  ∀[x∶_]_ : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  λx_     : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_     : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  Σ[x∶_]_ : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _,_     : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  `Bool   : µ ⊢ 𝕖
  `bool   : Bool → µ ⊢ 𝕖

  ★       : µ ⊢ 𝕖

  match   : µ ⊢ 𝕖  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕖

  -- Clause Lists
  []      : µ ⊢ 𝕔𝕤
  _∷_     : µ ⊢ 𝕔  →  µ ⊢ 𝕔𝕤  →  µ ⊢ 𝕔𝕤

  -- Clauses
  _⇒_     : µ ⊢ 𝕡 µ'  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕔

  -- Patterns
  `ᵖ      : µ ⊢ 𝕡 ([] ▷ 𝕖)
  _,ᵖ_    : µ ⊢ 𝕡 µ₁  →  µ ▷▷ µ₁ ⊢ 𝕡 µ₂  →  µ ⊢ 𝕡 (µ₁ ▷▷ µ₂)
  `boolᵖ  : Bool → µ ⊢ 𝕡 []
  -- dotᵖ    : µ ⊢ 𝕖 → µ ⊢ 𝕡 []

  -- Contexts
  ∅ᵖ      : µ ⊢ 𝕔𝕥𝕩 []
  _▶ᵖ_    : µ ⊢ 𝕔𝕥𝕩 µ₁  →  (µ ▷▷ µ₁) ⊢ 𝕖  →  µ ⊢ 𝕔𝕥𝕩 (µ₁ ▷ 𝕖)

  -- Pattern Types
  Pattern : µ ⊢ 𝕖  →  µ ⊢ 𝕔𝕥𝕩 µ₁  →  µ ⊢ ℙ µ₁

  -- Clause Types
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
  b b₁ b₂ b₃ b' b₁' b₂' b₃' : Bool
  `Γ `Γ₁ `Γ₂ `Γ₃ `Γ' `Γ₁' `Γ₂' `Γ₃' : µ ⊢ 𝕔𝕥𝕩 µ'

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
    `ⁿ_   : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
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

    `Bool   : Value {µ} `Bool
    `bool   : Value {µ} (`bool b)

    ★       : Value {µ} ★

    neutral : Neutral e → Value e

data Matches : µ₁ ⊢ 𝕖 → µ₂ ⊢ 𝕡 µ' → Set where
  M-` :
    Matches {µ₂ = µ₂} e `ᵖ
  M-bool :
    Matches {µ₂ = µ₂} (`bool {µ = µ} b) (`boolᵖ b)
  M-, :
    Matches e₁ p₁ →
    Matches e₂ p₂ →
    Matches (e₁ , e₂) (p₁ ,ᵖ p₂)

matching-sub : ∀ {µ µ' µ''} {e : µ ⊢ 𝕖} {p : µ' ⊢ 𝕡 µ''} → Matches e p → µ'' →ₛ µ
matching-sub {e = e} M-` = ⦅ e ⦆ₛ₀
matching-sub M-bool      = []*
matching-sub (M-, m₁ m₂) = matching-sub m₁ ∥ₛ matching-sub m₂

data _∈cs_ (c : µ ⊢ 𝕔) : µ ⊢ 𝕔𝕤 → Set where
  here : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ≡ c' → c ∈cs (c' ∷ cs)
  there : ∀ {c' : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} → c ∈cs cs → c ∈cs (c' ∷ cs)

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  β-match : ∀ {µ µ'} {e : µ ⊢ 𝕖} {cs : µ ⊢ 𝕔𝕤} {p : µ ⊢ 𝕡 µ'} {e' : µ ▷▷ µ' ⊢ 𝕖} →
    (p ⇒ e') ∈cs cs →
    (m : Matches e p) →
    match e cs ↪ e' ⋯ₛ (idₛ ∥ₛ matching-sub m)
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
  C-bool :
    Canonical (`bool {µ = µ₁} b) (`Bool {µ = µ₂})
  C-, :
    Canonical e₁ t₁ →
    t₂ ⋯ₛ ⦅ e₁ ⦆ₛ ↪* t₂' →
    Canonical e₂ t₂' →
    Canonical (e₁ , e₂) (Σ[x∶ t₁ ] t₂)

Exhaustive : µ ⊢ 𝕔𝕤 → µ ⊢ 𝕖 → Set
Exhaustive {µ} cs t =
  ∀ {µ'} {e : µ' ⊢ 𝕖} →
  Canonical e t →
  ∃[ µ' ] Σ[ p ∈ µ ⊢ 𝕡 µ' ] ∃[ e' ]
    (p ⇒ e') ∈cs cs × Matches e p

pattern no-var = `[_]_ {m = 𝕖} () _

⟦_⟧ᶜ : µ ⊢ 𝕔𝕥𝕩 µ' → Ctx' µ µ' 
⟦ no-var ⟧ᶜ 
⟦ ∅ᵖ     ⟧ᶜ = ∅'
⟦ P ▶ᵖ t ⟧ᶜ = ⟦ P ⟧ᶜ ▶' t

_▶▶ᵖ_ : µ ⊢ 𝕔𝕥𝕩 µ₁ → (µ ▷▷ µ₁) ⊢ 𝕔𝕥𝕩 µ₂ → µ ⊢ 𝕔𝕥𝕩 (µ₁ ▷▷ µ₂)
P₁ ▶▶ᵖ no-var
P₁ ▶▶ᵖ ∅ᵖ       = P₁
_▶▶ᵖ_ {µ} {µ₁} {µ₂ = µ₂ ▷ _} P₁ (P₂ ▶ᵖ t) =
  let sub = subst (_⊢ 𝕖) (sym (++-assoc µ₂ µ₁ µ)) in
  (P₁ ▶▶ᵖ P₂) ▶ᵖ sub t

mutual
  data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
    ⊢` : ∀ {x : µ ∋ m} →
      Γ ∋ x ∶ T →
      Γ ⊢ ` x ∶ T

    ⊢∀ :
      Γ ⊢ t₁ ∶ ★ →
      Γ ▶ t₁ ⊢ t₂ ∶ ★ →
      Γ ⊢ ∀[x∶ t₁ ] t₂ ∶ ★
    ⊢λ :
      Γ ⊢ t₁ ∶ ★ →
      Γ ▶ t₁ ⊢ e ∶ t₂ →
      Γ ⊢ λx e ∶ ∀[x∶ t₁ ] t₂
    ⊢· :
      Γ ⊢ e₁ ∶ ∀[x∶ t₁ ] t₂ →
      Γ ⊢ e₂ ∶ t₁ →
      Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ

    ⊢Σ :
      Γ ⊢ t₁ ∶ ★ →
      Γ ▶ t₁ ⊢ t₂ ∶ ★ →
      Γ ⊢ Σ[x∶ t₁ ] t₂ ∶ ★
    ⊢, : ∀ {e₂ : µ ⊢ 𝕖} →
      Γ ⊢ e₁ ∶ t₁ →
      Γ ⊢ e₂ ∶ t₂ ⋯ₛ ⦅ e₁ ⦆ₛ →
      Γ ⊢ e₁ , e₂ ∶ Σ[x∶ t₁ ] t₂

    ⊢Bool :
      Γ ⊢ `Bool ∶ ★
    ⊢bool :
      Γ ⊢ `bool b ∶ `Bool

    ⊢★ :
      Γ ⊢ ★ ∶ ★

    ⊢≣ :
      t ≣ t' →
      Γ ⊢ e ∶ t →
      Γ ⊢ e ∶ t'

    ⊢match :
      Γ ⊢ e ∶ t →
      Γ ⊢ cs ∶ Clause t t' →
      Exhaustive cs t →
      Γ ⊢ match e cs ∶ t'

    ⊢clause-[] :
      Γ ⊢ [] ∶ Clause t t'
    ⊢clause-∷ : ∀ {Γ : Ctx µ} →
      Γ ⊢ c  ∶ Clause t t' →
      Γ ⊢ cs ∶ Clause t t' →
      Γ ⊢ (c ∷ cs) ∶ Clause t t'

    ⊢clause : ∀ {Γ : Ctx µ} {p : µ ⊢ 𝕡 µ'} {t' : µ ⊢ 𝕖} →
      Γ ⊢ p ∶ Pattern t `Γ →
      (Γ ▶▶ ⟦ `Γ ⟧ᶜ) ⊢ e ∶ wk* µ' t' →
      Γ ⊢ (p ⇒ e) ∶ Clause t t'

    ⊢`ᵖ :
      Γ ⊢ `ᵖ ∶ Pattern t (∅ᵖ ▶ᵖ t)
    ⊢boolᵖ :
      Γ ⊢ `boolᵖ b ∶ Pattern `Bool ∅ᵖ
    ⊢,ᵖ :
      ∀ {µ µ₁ µ₂} {Γ : Ctx µ}
        {t₁ : µ ⊢ 𝕖} {t₂ : µ ▷ 𝕖 ⊢ 𝕖}
        {`Γ₁ : µ ⊢ 𝕔𝕥𝕩 µ₁} {`Γ₂ : µ ▷▷ µ₁ ⊢ 𝕔𝕥𝕩 µ₂}
        {p₁ : µ ⊢ 𝕡 µ₁} {p₂ : µ ▷▷ µ₁ ⊢ 𝕡 µ₂} →
      Γ ⊢ p₁ ∶ Pattern t₁ `Γ₁ →
      Γ ▶▶ ⟦ `Γ₁ ⟧ᶜ ⊢ p₂ ∶ Pattern (t₂ ⋯ᵣ (wkₖ* _ id) ↑ 𝕖 ⋯ₛ ⦅ ⟦ p₁ ⟧ᵖ ⦆ₛ) `Γ₂ →
      Γ ⊢ p₁ ,ᵖ p₂ ∶ Pattern (Σ[x∶ t₁ ] t₂) (`Γ₁ ▶▶ᵖ `Γ₂)
      -- p₁ matches e₁ with arbitrary many variables such that e₁ ≡ ⟪ p₁ ⟫ ⋯ σ,
      -- hence we need to have something like Σ[x∶ t₁ ] (t₂ ⋯ ⦅ ⟪ p₁ ⟫ ⦆)

    ⊢≣ᵖ :
      t ≣ t' →
      Γ ⊢ p ∶ Pattern t `Γ →  -- TODO: eq also needed for `Γ ?
      Γ ⊢ p ∶ Pattern t' `Γ

  ⟦_⟧ᵖ : µ ⊢ 𝕡 µ₁ → µ ▷▷ µ₁ ⊢ 𝕖
  ⟦ no-var ⟧ᵖ
  ⟦ `ᵖ ⟧ᵖ = # 0
  ⟦ _,ᵖ_ {µ = µ} {µ₁} {µ₂} p₁ p₂ ⟧ᵖ = let sub = subst (_⊢ 𝕖) (sym (++-assoc µ₂ µ₁ µ))
                                      in sub (wk* µ₂ ⟦ p₁ ⟧ᵖ , ⟦ p₂ ⟧ᵖ)
  ⟦ `boolᵖ b ⟧ᵖ = `bool b

  -- ⊢⟦_⟧ᵖ : ∀ {p : µ ⊢ 𝕡 µ₁} →
  --   Γ ⊢ p ∶ Pattern t `Γ →
  --   Γ ▶▶ ⟦ `Γ ⟧ᶜ ⊢ ⟦ p ⟧ᵖ ∶ wk* µ₁ t
  -- ⊢⟦_⟧ᵖ = {!!}

module Examples where
  pattern `true = `bool true
  pattern `false = `bool false
  pattern `trueᵖ = `boolᵖ true
  pattern `falseᵖ = `boolᵖ false
  pattern [_;_] x y = x ∷ y ∷ []

  module Ex1 where
    test : [] ⊢ 𝕖
    test =
      λx match (# 0) [
        (`falseᵖ ,ᵖ `ᵖ) ⇒ # 0 ;
        (`trueᵖ  ,ᵖ `ᵖ) ⇒ # 0 · `true
      ]

    test-ty : [] ⊢ 𝕖
    test-ty =
      ∀[x∶ A ] `Bool where
      A = Σ[x∶ `Bool ] match (# 0) [
            `falseᵖ ⇒ `Bool ;
            `trueᵖ  ⇒ ∀[x∶ `Bool ] `Bool
          ]

    test-⊢ : ∅ ⊢ test ∶ test-ty
    test-⊢ =
      ⊢λ
        (⊢Σ
          ⊢Bool
          (⊢match
            (⊢` refl)
            (⊢clause-∷ (⊢clause ⊢boolᵖ ⊢Bool)
            (⊢clause-∷ (⊢clause ⊢boolᵖ (⊢∀ ⊢Bool ⊢Bool))
              ⊢clause-[]))
              λ where (C-bool {b = false}) → _ , _ , _ , here refl , M-bool
                      (C-bool {b = true}) → _ , _ , _ , there (here refl) , M-bool ))
        (⊢match
          (⊢` refl)
          (⊢clause-∷ (⊢clause (⊢,ᵖ ⊢boolᵖ ⊢`ᵖ)
                              (⊢≣ (≣-↪ (β-match (here refl) M-bool)) (⊢` refl)))
            (⊢clause-∷ (⊢clause (⊢,ᵖ ⊢boolᵖ ⊢`ᵖ)
                                (⊢· ((⊢≣ (≣-↪ (β-match (there (here refl)) M-bool)) (⊢` refl))) ⊢bool))
              ⊢clause-[]))
          {!!})

  module Ex2 where
    test : [] ⊢ 𝕖
    test =
      λx match (# 0) [
        (`falseᵖ ,ᵖ `falseᵖ) ⇒ `true ;
        (`trueᵖ  ,ᵖ (`falseᵖ ,ᵖ `falseᵖ)) ⇒ `true
      ]

    test-ty : [] ⊢ 𝕖
    test-ty =
      ∀[x∶ A ] `Bool where
      A = Σ[x∶ `Bool ] match (# 0) [
            `falseᵖ ⇒ `Bool ;
            `trueᵖ  ⇒ Σ[x∶ `Bool ] `Bool
          ]

    test-⊢ : ∅ ⊢ test ∶ test-ty
    test-⊢ =
      ⊢λ
        (⊢Σ
          ⊢Bool
          (⊢match (⊢` refl)
            (⊢clause-∷ (⊢clause ⊢boolᵖ ⊢Bool)
            (⊢clause-∷ (⊢clause ⊢boolᵖ (⊢Σ ⊢Bool ⊢Bool)) ⊢clause-[]))
            {!!}))
        (⊢match (⊢` refl)
          (⊢clause-∷ (⊢clause (⊢,ᵖ ⊢boolᵖ (⊢≣ᵖ (≣-↩ (β-match (here refl) M-bool)) ⊢boolᵖ))
                              ⊢bool)
            (⊢clause-∷ (⊢clause (⊢,ᵖ ⊢boolᵖ (⊢≣ᵖ (≣-↩ (β-match (there (here refl)) M-bool)) (⊢,ᵖ ⊢boolᵖ ⊢boolᵖ)))
                                ⊢bool) ⊢clause-[]))
          λ where (C-, (C-bool {b = false}) (step (β-match (here refl) M-bool) refl) C-bool) →
                    {!(C-bool {b = false})!})
