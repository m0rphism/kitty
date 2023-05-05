module Kitty.Examples.STLC-Kits.Definitions where

open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

open import Kitty.Term.Prelude using (_∋_; _▷_) public
open import Kitty.Term.Modes using (Modes; Terms)

open ≡-Reasoning

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

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions and Types
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `_    : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
  λx_   : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  𝟘     : µ ⊢ 𝕥

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Kitty Terms

terms : Terms 𝕄
terms = record { _⊢_ = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }

-- Kitty KitTraversal

open import Kitty.Term.Kit terms public
open Kit ⦃ … ⦄ public

open import Kitty.Term.Sub terms public
open import Kitty.Term.Sub.Functional terms using (Sub-→; SubWithLaws-→; module Fun-SubCompose) public

open SubWithLaws SubWithLaws-→
open Sub Sub-→

infixl  5  _⋯_
_⋯_   : ∀ ⦃ 𝕂 : Kit ⦄
        → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
(` x)     ⋯ ϕ = `/id (ϕ _ x)
(λx t)    ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(t₁ · t₂) ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ⇒ t₂) ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
𝟘         ⋯ ϕ = 𝟘

⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
        → (` x) ⋯ ϕ ≡ `/id (ϕ _ x)
⋯-var x ϕ = refl

⋯-id : ∀ {{𝕂 : Kit}} {µ M} (t : µ ⊢ M) → t ⋯ id {{𝕂}} ≡ t
⋯-id (` x)     = id/`/id x
⋯-id (λx t)    = cong λx_ (
                   t ⋯ (id ↑ _) ≡⟨ {!~-cong-⋯ t (id↑~id _ _)!} ⟩ -- TODO: Not possible here anymore, but we can move ⋯-id further back in the record chain
                   t ⋯ id       ≡⟨ ⋯-id t ⟩
                   t            ∎
                 )
⋯-id (t₁ · t₂) = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂) = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id 𝟘         = refl

open import Kitty.Term.Traversal terms SubWithLaws-→ public

traversal : Traversal
traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var; ⋯-id = ⋯-id }

open Traversal traversal public hiding (_⋯_; ⋯-var; ⋯-id)

-- Kitty KitHomotopy

open import Kitty.Term.KitT traversal
open KitT ⦃ … ⦄

open import Kitty.Term.KitHomotopy traversal

~-cong-⋯ :
  ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
    ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
    {µ₁ µ₂ M}
    {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} (t : µ₁ ⊢ M)
  → f ~ g
  → t ⋯ f ≡ t ⋯ g
~-cong-⋯ (` x)     f~g = f~g _ x
~-cong-⋯ (λx t)    f~g = cong λx_ (~-cong-⋯ t (~-cong-↑ f~g))
~-cong-⋯ (t₁ · t₂) f~g = cong₂ _·_ (~-cong-⋯ t₁ f~g) (~-cong-⋯ t₂ f~g)
~-cong-⋯ (t₁ ⇒ t₂) f~g = cong₂ _⇒_ (~-cong-⋯ t₁ f~g) (~-cong-⋯ t₂ f~g)
~-cong-⋯ 𝟘         f~g = refl

kit-homotopy : KitHomotopy
kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

-- Kitty KitCompose

open import Kitty.Term.ComposeKit kit-homotopy
open ComposeKit ⦃ … ⦄ public

open import Kitty.Term.SubCompose kit-homotopy
open Fun-SubCompose kit-homotopy
open SubCompose SubCompose-→ hiding (_·ₖ_)

open import Kitty.Term.ComposeTraversal SubCompose-→

⋯-assoc :
  ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit ⦄
    ⦃ W₁ : KitT 𝕂₁ ⦄
    ⦃ W₂ : KitT 𝕂₂ ⦄
    ⦃ W₁₂ : KitT 𝕂₁⊔𝕂₂ ⦄
    ⦃ 𝔸 : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
    (t : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
⋯-assoc (` x)     ϕ₁ ϕ₂ = tm-⋯-· ϕ₁ ϕ₂ x
⋯-assoc (λx t)    ϕ₁ ϕ₂ = cong λx_
  (t ⋯ (ϕ₁ ↑ _) ⋯ (ϕ₂ ↑ _)    ≡⟨ ⋯-assoc t (ϕ₁ ↑ _) (ϕ₂ ↑ _) ⟩
   t ⋯ ((ϕ₁ ↑ _) ·ₖ (ϕ₂ ↑ _)) ≡⟨ ~-cong-⋯ t (~-sym (dist-↑-· _ ϕ₁ ϕ₂)) ⟩
   t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ _)       ∎)
⋯-assoc (t₁ · t₂) ϕ₁ ϕ₂ = cong₂ _·_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂) ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc 𝟘         ϕ₁ ϕ₂ = refl

compose-traversal : ComposeTraversal
compose-traversal = record { ⋯-assoc = ⋯-assoc }

open ComposeTraversal compose-traversal public hiding (⋯-assoc)

-- Instances

instance
  kitᵣ'   = kitᵣ
  kitₛ'   = kitₛ
  ckitᵣ'  = ckitᵣ
  ckitₛᵣ' = ckitₛᵣ
  ckitₛₛ' = ckitₛₛ

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeModes terms

-- Each variable mode corresponds to a term mode that represents its type.
type-modes : TypeModes
type-modes = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

open TypeModes type-modes public

open import Kitty.Typing.CtxRepr type-modes

ctx-repr : CtxRepr
ctx-repr = List-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  τ-` : ∀ {µ} {m} {Γ : Ctx µ} {T : µ ∶⊢ m→M m} {x : µ ∋ m} →
    wk-telescope Γ x ≡ T →
    Γ ⊢ ` x ∶ T
  τ-λ : {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wknᵣ →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `_  : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

  data Value : µ ⊢ M → Set where
    λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
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
