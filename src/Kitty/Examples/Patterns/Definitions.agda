module Kitty.Examples.Patterns.Definitions where

open import Kitty.Term.Prelude using (_∋_; _▷_; _▷▷_; List; []) public
open import Kitty.Term.Terms using (Terms; SortTy; Var; NoVar)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_; proj₂)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _∈cs_
infixr  5  λx_ _∷_
infixr  6  _⇒_
infixl  6  _·_
infix   7  `_

-- Sorts -----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖  : Sort Var                     -- Expressions
  𝕥  : Sort NoVar                   -- Types
  𝕡  : List (Sort Var) → Sort NoVar -- Patterns
  ℙ  : List (Sort Var) → Sort NoVar -- Pattern Types
  𝕔  : Sort NoVar                   -- Clause
  𝕔𝕤 : Sort NoVar                   -- Clauses
  ℂ  : Sort NoVar                   -- Clause Type

variable
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : List (Sort Var)
  x y z                     : S ∋ s

↑ᵗ : Sort st → ∃[ st' ] Sort st'
↑ᵗ 𝕖     = _ , 𝕥
↑ᵗ (𝕡 S) = _ , ℙ S
↑ᵗ 𝕥     = _ , 𝕥
↑ᵗ (ℙ S) = _ , ℙ S
↑ᵗ 𝕔     = _ , ℂ
↑ᵗ 𝕔𝕤    = _ , ℂ
↑ᵗ ℂ     = _ , ℂ

-- Syntax ----------------------------------------------------------------------

-- Expressions and Types
data _⊢_ : List (Sort Var) → Sort st → Set where
  `_        : S ∋ s  →  S ⊢ s

  -- Functions
  λx_       : S ▷ 𝕖 ⊢ 𝕖  →  S ⊢ 𝕖
  _·_       : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  _`→_       : S ⊢ 𝕥  →  S ⊢ 𝕥  →  S ⊢ 𝕥

  -- Bottom, Unit, Products, Sums
  𝟘 𝟙       : S ⊢ 𝕥
  _`×_ _`⊎_ : S ⊢ 𝕥  →  S ⊢ 𝕥  →  S ⊢ 𝕥
  tt        : S ⊢ 𝕖
  _,_       : S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
  inj₁ inj₂ : S ⊢ 𝕖  →  S ⊢ 𝕖

  -- Matching
  match     : S ⊢ 𝕖  →  S ⊢ 𝕔𝕤  →  S ⊢ 𝕖

  -- List of clauses (workaround, as we do not support `List (S ⊢ 𝕔)` yet)
  []        : S ⊢ 𝕔𝕤
  _∷_       : S ⊢ 𝕔  →  S ⊢ 𝕔𝕤  →  S ⊢ 𝕔𝕤

  -- Clause
  _⇒_       : S ⊢ 𝕡 S'  →  (S ▷▷ S') ⊢ 𝕖  →  S ⊢ 𝕔

  -- Patterns
  `ᵖ        : S ⊢ 𝕡 ([] ▷ 𝕖)
  _,ᵖ_      : S ⊢ 𝕡 S₁  →  (S ▷▷ S₁) ⊢ 𝕡 S₂  →  S ⊢ 𝕡 (S₁ ▷▷ S₂)
  inj₁ᵖ inj₂ᵖ : S ⊢ 𝕡 S'  →  S ⊢ 𝕡 S'
  ttᵖ       : S ⊢ 𝕡 []

  -- Pattern Types, i.e. type contexts.
  -- (workaround, as we do not support using real type contexts in the syntax yet)
  []ᵖ       : S ⊢ ℙ []
  _▶ᵖ_      : S ⊢ ℙ S₁ → (S ▷▷ S₁) ⊢ 𝕥 → S ⊢ ℙ (S₁ ▷ 𝕖)

  -- Clause Types
  Clause    : S ⊢ 𝕥  →  S ⊢ 𝕥  →  S ⊢ ℂ

-- Concatenation for the syntax of type contexts (pattern types).
_▶▶ᵖ_ : S ⊢ ℙ S₁ → (S ▷▷ S₁) ⊢ ℙ S₂ → S ⊢ ℙ (S₁ ▷▷ S₂)
P₁ ▶▶ᵖ []ᵖ       = P₁
_▶▶ᵖ_ {S} {S₁} {S₂ = S₂ ▷ _} P₁ (P₂ ▶ᵖ t) =
  let sub = subst (_⊢ 𝕥) (sym (++-assoc S₂ S₁ S)) in
  (P₁ ▶▶ᵖ P₂) ▶ᵖ sub t

variable
  e e₁ e₂ e₃ e' e₁' e₂' : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : S ⊢ 𝕥
  p p₁ p₂ p₃ p' p₁' p₂' : S ⊢ 𝕡 S'
  P P₁ P₂ P₃ P' P₁' P₂' : S ⊢ ℙ S'
  c  c'                 : S ⊢ 𝕔
  cs cs'                : S ⊢ 𝕔𝕤
  C C'                  : S ⊢ ℂ
  E E₁ E₂ E₃ E' E₁' E₂' : S ⊢ s

-- Reflection Time -------------------------------------------------------------

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Term.Reflection using (derive; module Derived)
unquoteDecl D = derive Sort _⊢_ D

-- We choose to represent substitutions as functions.
open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeSorts terms

type-sorts : TypeSorts
type-sorts = record { ↑ᵗ = ↑ᵗ }

open TypeSorts type-sorts public hiding (↑ᵗ)

open import Kitty.Typing.CtxRepr type-sorts

-- We choose to represent type contexts as functions.
ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

_∶⊢'_ : List (Sort Var) → Sort st → Set
S ∶⊢' s = S ⊢ proj₂ (↑ᵗ s)

CtxP' : List (Sort Var) → List (Sort Var) → Set
CtxP' S S' = ∀ s → (x : S' ∋ s) →  (S ▷▷ drop-∈ x S') ∶⊢' s

-- Converting syntactic type contexts (pattern types) to real type contexts.
PatTy→Ctx' : S ⊢ ℙ S' → CtxP' S S' 
PatTy→Ctx' []ᵖ = λ _ ()
PatTy→Ctx' (P ▶ᵖ t) = PatTy→Ctx' P ▶' t

-- Type System -----------------------------------------------------------------

-- `Matches e p` is proof that pattern `p` matches expression `e`.
data Matches : S₁ ⊢ 𝕖 → S₂ ⊢ 𝕡 S' → Set where
  M-` :
    Matches {S₂ = S₂} e `ᵖ
  M-tt :
    Matches {S₂ = S₂} (tt {S = S}) ttᵖ
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

-- `Canonical e t` is proof that expression `e` has the right shape to be of type `t`.
data Canonical : S₁ ⊢ 𝕖 → S₂ ⊢ 𝕥 → Set where
  C-λ :
    Canonical (λx e) (t₁ `→ t₂)
  C-tt :
    Canonical (tt {S = S₁}) (𝟙 {S = S₂})
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

-- List membership for our syntactic encoding of lists of clauses.
data _∈cs_ (c : S ⊢ 𝕔) : S ⊢ 𝕔𝕤 → Set where
  here : ∀ {c' : S ⊢ 𝕔} {cs : S ⊢ 𝕔𝕤} → c ≡ c' → c ∈cs (c' ∷ cs)
  there : ∀ {c' : S ⊢ 𝕔} {cs : S ⊢ 𝕔𝕤} → c ∈cs cs → c ∈cs (c' ∷ cs)

-- When a list of clauses is exhaustive for a given type.
Exhaustive : S ⊢ 𝕔𝕤 → S ⊢ 𝕥 → Set
Exhaustive {S} cs t =
  ∀ {S'} {e : S' ⊢ 𝕖} →
  Canonical e t →
  ∃[ S' ] Σ[ p ∈ S ⊢ 𝕡 S' ] ∃[ e' ]
    (p ⇒ e') ∈cs cs × Matches e p

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢-` : ∀ {S} {s} {Γ : Ctx S} {T : S ∶⊢ s} {x : S ∋ s} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢-λ : {Γ : Ctx S} →
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
  ⊢-clause : ∀ {Γ : Ctx S} {p : S ⊢ 𝕡 S'} {t' : S ⊢ 𝕥} →
    Γ ⊢ p ∶ P →
    (Γ ▶▶ PatTy→Ctx' P) ⊢ e ∶ t' ⋯ᵣ wkn* S'  →
    Γ ⊢ (p ⇒ e) ∶ Clause t t' -- `t` can be arbitrary, as it is already pinned
                              -- down by the `Exhaustive` proof in the match
  ⊢-clause-[] :
    Γ ⊢ [] ∶ Clause t t'
  ⊢-clause-∷ : ∀ {Γ : Ctx S} →
    Γ ⊢ c  ∶ Clause t t' →
    Γ ⊢ cs ∶ Clause t t' →
    Γ ⊢ (c ∷ cs) ∶ Clause t t'
  ⊢-ttᵖ :
    Γ ⊢ ttᵖ ∶ []ᵖ
  ⊢-`ᵖ :
    Γ ⊢ `ᵖ ∶ []ᵖ ▶ᵖ t
  ⊢-,ᵖ : ∀ {S S₁ S₂} {Γ : Ctx S} {p₁ : S ⊢ 𝕡 S₁} {P₁ : S ⊢ ℙ S₁}
           {p₂ : S ▷▷ S₁ ⊢ 𝕡 S₂} {P₂ : S ▷▷ S₁ ⊢ ℙ S₂} →
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
  data Neutral : S ⊢ s → Set where
    `ⁿ_  : ∀ (x : S ∋ 𝕖) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    match : Neutral e₁ → Neutral (match e₁ cs)

  data Value : S ⊢ s → Set where
    λx_     : ∀ (e : (S ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    _,_     : Value e₁ → Value e₂ → Value (e₁ , e₂)
    inj₁    : Value e → Value (inj₁ e)
    inj₂    : Value e → Value (inj₂ e)
    tt      : Value (tt {S})
    neutral : Neutral e → Value e

-- The substitution resulting from an expression `e` matching a pattern `p`.
matching-sub : ∀ {S S' S''} {e : S ⊢ 𝕖} {p : S' ⊢ 𝕡 S''} → Matches e p → S'' →ₛ S
matching-sub {e = e} M-` = ⦅ e ⦆ₛ₀
matching-sub M-tt        = []*
matching-sub (M-, m₁ m₂) = matching-sub m₁ ∥ₛ matching-sub m₂
matching-sub (M-inj₁ m)  = matching-sub m
matching-sub (M-inj₂ m)  = matching-sub m

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ : ∀ {e₂ : S ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-match : ∀ {S S'} {e : S ⊢ 𝕖} {cs : S ⊢ 𝕔𝕤} {p : S ⊢ 𝕡 S'} {e' : S ▷▷ S' ⊢ 𝕖} {σ : S' →ₛ S} →
    (p ⇒ e') ∈cs cs →
    (m : Matches e p) →
    matching-sub m ≡ σ →
    match e cs ↪ e' ⋯ₛ (idₛ ∥ₛ σ)
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
  ξ-match :
    e ↪ e' →
    match e cs ↪ match e' cs
