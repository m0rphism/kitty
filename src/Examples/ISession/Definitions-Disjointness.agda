module Examples.ISession.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import KitTheory.Prelude using (_∋_; _,_) public
open import KitTheory.Modes using (Modes; Terms)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _⊢*_∶_
infixr  5  ∀α_  λx_  Λα_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `ᵅ_  `ˣ_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕕 : Modeᵥ  -- Domain Variables

-- Term Modes
data Modeₜ : Set where
  𝕔 : Modeₜ  -- Constraints
  𝕕 : Modeₜ  -- Domains

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕕 = 𝕕

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x x₁ x₂ x' x₁' x₂'        : 𝕕 ∈ µ
  X Y Z                     : m ∈ µ

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data Term : List Modeᵥ → Modeₜ → Set where
  true  : Term µ 𝕔
  _∧_   : Term µ 𝕔 → Term µ 𝕔 → Term µ 𝕔
  _#_   : Term µ 𝕕 → Term µ 𝕕 → Term µ 𝕔
  `ᵈ_   : µ ∋ 𝕕 → Term µ 𝕕
  _,ᵈ_  : Term µ 𝕕 → Term µ 𝕕 → Term µ 𝕕

-- data _⊢_∶ok :

`_ : µ ∋ m → Term µ (m→M m)
`_ {m = 𝕕} = `ᵈ_

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = Term ; `_ = `_ }

variable
  c c₁ c₂ c' c₁' c₂' : Term µ 𝕔
  d d₁ d₂ d' d₁' d₂' : Term µ 𝕕
  E E₁ E₂ E' E₁' E₂' : Term µ M

-- Application of Renamings and Substitutions ----------------------------------

open import KitTheory.Kit 𝕋
open Kit {{...}} public

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  -- Traverse a term with a renaming or substitution (depending on the kit).
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ M
  true       ⋯ f = true
  (c₁ ∧ c₂)  ⋯ f = (c₁ ⋯ f) ∧ (c₂ ⋯ f)
  (d₁ # d₂)  ⋯ f = (d₁ ⋯ f) # (d₂ ⋯ f)
  (`ᵈ x)     ⋯ f = tm _ (f _ x)
  (d₁ ,ᵈ d₂) ⋯ f = (d₁ ⋯ f) ,ᵈ (d₂ ⋯ f)

  -- Applying a renaming or substitution to a variable does the expected thing.
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (` x) ⋯ f ≡ tm _ (f _ x)
  ⋯-var {m = 𝕕} _ _ = refl

open KitTraversal kit-traversal public

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Composition of Renamings and Substitutions ----------------------------------

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : Term µ₁ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    (v ⋯ f) ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc true       f g = refl
  ⋯-assoc (c₁ ∧ c₂)  f g = cong₂ _∧_ (⋯-assoc c₁ f g) (⋯-assoc c₂ f g)
  ⋯-assoc (d₁ # d₂)  f g = cong₂ _#_ (⋯-assoc d₁ f g) (⋯-assoc d₂ f g)
  ⋯-assoc (`ᵈ x)     f g = tm-⋯-∘ f g x
  ⋯-assoc (d₁ ,ᵈ d₂) f g = cong₂ _,ᵈ_ (⋯-assoc d₁ f g) (⋯-assoc d₂ f g)

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id true       = refl
  ⋯-id (c₁ ∧ c₂)  = cong₂ _∧_ (⋯-id c₁) (⋯-id c₂)
  ⋯-id (d₁ # d₂)  = cong₂ _#_ (⋯-id d₁) (⋯-id d₂)
  ⋯-id (`ᵈ x)     = tm-vr x
  ⋯-id (d₁ ,ᵈ d₂) = cong₂ _,ᵈ_ (⋯-id d₁) (⋯-id d₂)

open KitAssocLemmas kit-assoc-lemmas public

-- -- Types and Contexts ----------------------------------------------------------

-- open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- -- Each variable mode corresponds to a term mode that represents its type.
-- kit-type : KitType
-- kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

-- open KitType kit-type public

-- variable
--   Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
--   T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- -- Type System -----------------------------------------------------------------

-- data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
--   τ-` : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕖 ∈ µ} →
--     wk-telescope Γ x ≡ t →
--     Γ ⊢ ` x ∶ t
--   τ-λ : ∀ {Γ : Ctx µ} →
--     Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
--     Γ ⊢ λx e ∶ t₁ ⇒ t₂
--   τ-Λ :
--     Γ ,, ★ ⊢ e ∶ t₂ →
--     Γ ⊢ Λα e ∶ ∀α t₂
--   τ-· :
--     Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--     Γ ⊢ e₂ ∶ t₁ →
--     Γ ⊢ e₁ · e₂ ∶ t₂
--   τ-∙ : ∀ {Γ : Ctx µ} →
--     Γ ⊢ e ∶ ∀α t₂ →
--     Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
--   τ-𝕥 :
--     Γ ⊢ t ∶ ★
--   τ-𝕜 :
--     Γ ⊢ ★ ∶ ★

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ 𝕖 → Set where
--     `x  : Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
--     _∙t : Neutral e → Neutral (e ∙ t)

--   data Value : µ ⊢ 𝕖 → Set where
--     λx_     : Value e → Value (λx e)
--     Λα_     : Value e → Value (Λα e)
--     neutral : Neutral e → Value e

-- data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
--   β-Λ : ∀ {t : µ ⊢ 𝕥} →
--     (Λα e) ∙ t ↪ e ⋯ ⦅ t ⦆
--   ξ-λ :
--     e ↪ e' →
--     λx e ↪ λx e'
--   ξ-Λ :
--     e ↪ e' →
--     Λα e ↪ Λα e'
--   ξ-·₁ :
--     e₁ ↪ e₁' →
--     e₁ · e₂ ↪ e₁' · e₂
--   ξ-·₂ :
--     e₂ ↪ e₂' →
--     e₁ · e₂ ↪ e₁ · e₂'
--   ξ-∙ :
--     e ↪ e' →
--     e ∙ t ↪ e' ∙ t
