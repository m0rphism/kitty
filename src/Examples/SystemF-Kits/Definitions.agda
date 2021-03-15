module Examples.SystemF-Kits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)

infixr  3  _↪_  _⊢_∶_  _⊢*_∶_
infixr  5  ∀→_  λ→_  Λ→_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Syntax ----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Value-level variables
  𝕥 : Modeᵥ  -- Type-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖
m→M 𝕥 = 𝕥

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  μ μ₁ μ₂ μ₃ μ' μ₁' μ₂' μ₃' : List Modeᵥ
  μ₁₁ μ₁₂ μ₂₁ μ₂₂           : List Modeᵥ
  x y z                     : 𝕖 ∈ μ
  α β γ                     : 𝕥 ∈ μ
  X Y Z                     : m ∈ μ

data Term : List Modeᵥ → Modeₜ → Set where
  `[_]_ : M ≡ m→M m → m ∈ μ → Term μ M  -- Expr and Type Variables
  λ→_   : Term (𝕖 ∷ μ) 𝕖 → Term μ 𝕖
  Λ→_   : Term (𝕥 ∷ μ) 𝕖 → Term μ 𝕖
  ∀→_   : Term (𝕥 ∷ μ) 𝕥 → Term μ 𝕥
  _·_   : Term μ 𝕖 → Term μ 𝕖 → Term μ 𝕖
  _∙_   : Term μ 𝕖 → Term μ 𝕥 → Term μ 𝕖
  _⇒_   : Term μ 𝕥 → Term μ 𝕥 → Term μ 𝕥
  ★     : Term μ 𝕜

pattern `_ x = `[ refl ] x

variable
  e e₁ e₂ e' e₁' e₂' : Term μ 𝕖
  t t₁ t₂ t' t₁' t₂' : Term μ 𝕥
  k k₁ k₂ k' k₁' k₂' : Term μ 𝕜
  E E₁ E₂ E' E₁' E₂' : Term μ M

-- Substitutions ---------------------------------------------------------------

open import KitTheory.Modes

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = Term ; `_ = `_ }

open import KitTheory.Kit 𝕋
open Kit {{...}} public
open KitTraversal {{...}} public

-- Traversing a term with a renaming/substitution f.
instance kit-traversal : KitTraversal
_⋯_ {{kit-traversal}} (` x)     f = tm' (f _ x)
_⋯_ {{kit-traversal}} (λ→ t)    f = λ→ (t ⋯ (f ↑ 𝕖))
_⋯_ {{kit-traversal}} (Λ→ t)    f = Λ→ (t ⋯ (f ↑ 𝕥))
_⋯_ {{kit-traversal}} (∀→ t)    f = ∀→ (t ⋯ (f ↑ 𝕥))
_⋯_ {{kit-traversal}} (t₁ · t₂) f = (t₁ ⋯ f) · (t₂ ⋯ f)
_⋯_ {{kit-traversal}} (t₁ ∙ t₂) f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
_⋯_ {{kit-traversal}} (t₁ ⇒ t₂) f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
_⋯_ {{kit-traversal}} ★         f = ★
⋯-var {{kit-traversal}} x f = refl

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public
open KitAssoc {{...}} public

-- Associativity of applying a renaming/substitution after a renaming/substitution.
instance kit-assoc : KitAssoc
⋯-assoc {{kit-assoc}} (` X) f g =
  tm' (f _ X) ⋯ g    ≡⟨ tm'-⋯-∘ f g X ⟩
  tm' ((g ∘ₖ f) _ X) ∎
⋯-assoc {{kit-assoc}} (λ→ e) f g = cong λ→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
⋯-assoc {{kit-assoc}} (Λ→ e) f g = cong Λ→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
⋯-assoc {{kit-assoc}} (∀→ e) f g = cong ∀→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
⋯-assoc {{kit-assoc}} (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
⋯-assoc {{kit-assoc}} (e₁ ∙ e₂) f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
⋯-assoc {{kit-assoc}} (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
⋯-assoc {{kit-assoc}} ★         f g = refl

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
instance kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term μ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                             = tm-vr x
  ⋯-id {μ = μ} {{𝕂}} (λ→ t)   rewrite id↑≡id {{𝕂}} 𝕖 μ = cong λ→_ (⋯-id t)
  ⋯-id {μ = μ} {{𝕂}} (Λ→ t)   rewrite id↑≡id {{𝕂}} 𝕥 μ = cong Λ→_ (⋯-id t)
  ⋯-id {μ = μ} {{𝕂}} (∀→ t)   rewrite id↑≡id {{𝕂}} 𝕥 μ = cong ∀→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                                 = refl

open KitAssocLemmas {{...}} public

open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
instance kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

Type : List Modeᵥ → Modeₜ → Set
Type = _∶⊢_

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx μ
  T T₁ T₂ T' T₁' T₂' : Type μ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx μ → Term μ M → Type μ M → Set where
  τ-` : ∀ {Γ : Ctx μ} {t : Type μ 𝕖} {x : 𝕖 ∈ μ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx μ} →
    Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λ→ e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ,, ★ ⊢ e ∶ t₂ →
    Γ ⊢ Λ→ e ∶ ∀→ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx μ} →
    Γ ⊢ e ∶ ∀→ t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-𝕥 :
    Γ ⊢ t ∶ ★
  τ-𝕜 :
    Γ ⊢ ★ ∶ ★

_⊢*_∶_ : Ctx μ₂ → μ₁ →ₛ μ₂ → Ctx μ₁ → Set
_⊢*_∶_ {μ₁ = μ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : μ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- Semantics -------------------------------------------------------------------

data Neutral : Term μ 𝕖 → Set where
  n-`  : Neutral (` x)
  n-·₁ : Neutral e₁ → Neutral (e₁ · e₂)
  n-∙₁ : Neutral e → Neutral (e ∙ t)

data Value : Term μ 𝕖 → Set where
  λ→_     : Value e → Value (λ→ e)
  Λ→_     : Value e → Value (Λ→ e)
  neutral : Neutral e → Value e

data _↪_ : Term μ 𝕖 → Term μ 𝕖 → Set where
  β-λ : ∀ {e₂ : Term μ 𝕖} →
    (λ→ e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t : Term μ 𝕥} →
    (Λ→ e) ∙ t ↪ e ⋯ ⦅ t ⦆
  ξ-λ :
    e ↪ e' →
    λ→ e ↪ λ→ e'
  ξ-Λ :
    e ↪ e' →
    Λ→ e ↪ Λ→ e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙ :
    e ↪ e' →
    e ∙ t ↪ e' ∙ t
