module Kitty.Examples.STLC.Definitions where

open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

open import Kitty.Prelude using (_∋_; _▷_) public
open import Kitty.Homotopy using (_~_; ~-sym)
open import Kitty.Modes using (Modes; Terms)

open ≡-Reasoning

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _⊢*_∶_
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
  x y z                     : µ ∋ 𝕖

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
terms = record { _⊢_ = _⊢_ ; `_ = `_ }

-- Kitty KitTraversal

open import Kitty.Kit terms public
open Kit ⦃ … ⦄ public

infixl  5  _⋯_
_⋯_   : ∀ ⦃ 𝕂 : Kit ⦄
        → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
(` x)     ⋯ ϕ = `/id _ (ϕ _ x)
(λx t)    ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(t₁ · t₂) ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ⇒ t₂) ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
𝟘         ⋯ ϕ = 𝟘

⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
        → (` x) ⋯ ϕ ≡ `/id _ (ϕ _ x)
⋯-var x ϕ = refl

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

open KitTraversal kit-traversal public hiding (_⋯_; ⋯-var)

-- Kitty KitHomotopy

~-cong-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂} (t : µ₁ ⊢ M)
  → f ~ g
  → t ⋯ f ≡ t ⋯ g
~-cong-⋯ (` x)     f~g = cong (`/id _) (f~g _ x)
~-cong-⋯ (λx t)    f~g = cong λx_ (~-cong-⋯ t (~-cong-↑ f~g))
~-cong-⋯ (t₁ · t₂) f~g = cong₂ _·_ (~-cong-⋯ t₁ f~g) (~-cong-⋯ t₂ f~g)
~-cong-⋯ (t₁ ⇒ t₂) f~g = cong₂ _⇒_ (~-cong-⋯ t₁ f~g) (~-cong-⋯ t₂ f~g)
~-cong-⋯ 𝟘         f~g = refl

kit-homotopy : KitHomotopy kit-traversal
kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

-- Kitty KitCompose

open import Kitty.Compose terms kit-traversal kit-homotopy
open ComposeKit ⦃ … ⦄ public

⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
            (t : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) →
  t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ (ϕ₂ ∘ₖ ϕ₁)
⋯-assoc (` x)     ϕ₁ ϕ₂ = tm-⋯-∘ ϕ₁ ϕ₂ x
⋯-assoc (λx t)    ϕ₁ ϕ₂ = cong λx_
  (t ⋯ (ϕ₁ ↑ _) ⋯ (ϕ₂ ↑ _)    ≡⟨ ⋯-assoc t (ϕ₁ ↑ _) (ϕ₂ ↑ _) ⟩
   t ⋯ ((ϕ₂ ↑ _) ∘ₖ (ϕ₁ ↑ _)) ≡⟨ ~-cong-⋯ t (~-sym (dist-↑-∘ _ ϕ₂ ϕ₁)) ⟩
   t ⋯ ((ϕ₂ ∘ₖ ϕ₁) ↑ _)       ∎)
  
⋯-assoc (t₁ · t₂) ϕ₁ ϕ₂ = cong₂ _·_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂) ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc 𝟘         ϕ₁ ϕ₂ = refl

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc }

open KitAssoc kit-assoc public hiding (⋯-assoc)

-- Kitty KitCompose Identity

⋯-id : ∀ {{𝕂 : Kit}} {µ M} (t : µ ⊢ M) → t ⋯ idₖ {{𝕂}} ≡ t
⋯-id (` x)     = id/`/id x
⋯-id (λx t)    = cong λx_ (
                   t ⋯ (idₖ ↑ _) ≡⟨ ~-cong-⋯ t (id↑~id _ _) ⟩
                   t ⋯ idₖ       ≡⟨ ⋯-id t ⟩
                   t             ∎
                 )
⋯-id (t₁ · t₂) = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂) = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id 𝟘         = refl

kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id }

open KitAssocLemmas kit-assoc-lemmas public hiding (⋯-id)

-- Instances

instance
  kitᵣ'  = kitᵣ
  kitₛ'  = kitₛ
  kitᵣᵣ' = kitᵣᵣ
  kitᵣₛ' = kitᵣₛ
  kitₛᵣ' = kitₛᵣ
  kitₛₛ' = kitₛₛ

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Types terms

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

open KitType kit-type public

open import Kitty.OPE kit-assoc-lemmas kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set where
  τ-` :
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkᵣ →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂

_∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
_∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ 𝕖 → Set where
    `_  : ∀ (x : µ ∋ 𝕖) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

  data Value : µ ⊢ 𝕖 → Set where
    λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
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
