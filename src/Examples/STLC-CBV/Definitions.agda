module Examples.STLC-CBV.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import KitTheory.Prelude using (_∋_; _▷_) public
open import KitTheory.Modes using (Modes; Terms)
open import Data.Product using (_×_; ∃-syntax)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _↪*_  _⊢_∶_  _⊢*_∶_
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
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : 𝕖 ∈ µ
  X Y Z                     : m ∈ µ

-- Syntax ----------------------------------------------------------------------

-- Expressions and Types
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `_    : µ ∋ 𝕖  →  µ ⊢ 𝕖
  λx_   : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  𝟘     : µ ⊢ 𝕥

``_ : µ ∋ m → µ ⊢ m→M m
``_ {m = 𝕖} = `_

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = _⊢_ ; `_ = ``_ }

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Application of Renamings and Substitutions ----------------------------------

open import KitTheory.Kit 𝕋
open Kit {{...}} public

infixl  5  _⋯_

-- Traverse a term with a renaming or substitution (depending on the kit).
_⋯_ : ∀ {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
(` x)     ⋯ f = tm _ (f _ x)
(λx t)    ⋯ f = λx (t ⋯ (f ↑ 𝕖))
(t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
(t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
𝟘         ⋯ f = 𝟘
-- Applying a renaming or substitution to a variable does the expected thing.
⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (`` x) ⋯ f ≡ tm _ (f _ x)
⋯-var {m = 𝕖} _ _ = refl

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

open KitTraversal kit-traversal public hiding (_⋯_; ⋯-var)

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Composition of Renamings and Substitutions ----------------------------------

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    (v ⋯ f) ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc (` x) f g =
    tm _ (f _ x) ⋯ g    ≡⟨ tm-⋯-∘ f g x ⟩
    tm _ ((g ∘ₖ f) _ x) ∎
  ⋯-assoc (λx e) f g = cong λx_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc 𝟘         f g = refl

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                              = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λx t)    rewrite id↑≡id {{𝕂}} 𝕖 µ = cong λx_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                          = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               𝟘                                  = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts ----------------------------------------------------------

open import KitTheory.Types 𝕋

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

open KitType kit-type public

open import KitTheory.OPE 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕖 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- Semantics -------------------------------------------------------------------

data Value : µ ⊢ 𝕖 → Set where
  λxe     : Value (λx e)

data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    Value e₂ →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    Value e₁ →
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

data _↪*_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
  ↪*-refl :
    e ↪* e
  ↪*-step :
    e₁ ↪ e₂ →
    e₂ ↪* e₃ →
    e₁ ↪* e₃

↪*-trans :
  e₁ ↪* e₂ →
  e₂ ↪* e₃ →
  e₁ ↪* e₃
↪*-trans ↪*-refl                  e₂↪*e₃ = e₂↪*e₃
↪*-trans (↪*-step e₁↪e₁' e₁'↪*e₂) e₂↪*e₃ = ↪*-step e₁↪e₁' (↪*-trans e₁'↪*e₂ e₂↪*e₃)

_⇓ : µ ⊢ 𝕖 → Set
e ⇓ = ∃[ e' ] (e ↪* e' × Value e')
