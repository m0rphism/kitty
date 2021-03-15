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
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : 𝕖 ∈ µ
  α β γ                     : 𝕥 ∈ µ
  X Y Z                     : m ∈ µ

data Term : List Modeᵥ → Modeₜ → Set where
  `[_]_ : M ≡ m→M m → m ∈ µ → Term µ M  -- Expr and Type Variables
  λ→_   : Term (𝕖 ∷ µ) 𝕖 → Term µ 𝕖
  Λ→_   : Term (𝕥 ∷ µ) 𝕖 → Term µ 𝕖
  ∀→_   : Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  _·_   : Term µ 𝕖 → Term µ 𝕖 → Term µ 𝕖
  _∙_   : Term µ 𝕖 → Term µ 𝕥 → Term µ 𝕖
  _⇒_   : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
  ★     : Term µ 𝕜

pattern `_ x = `[ refl ] x

variable
  e e₁ e₂ e' e₁' e₂' : Term µ 𝕖
  t t₁ t₂ t' t₁' t₂' : Term µ 𝕥
  k k₁ k₂ k' k₁' k₂' : Term µ 𝕜
  E E₁ E₂ E' E₁' E₂' : Term µ M

-- Substitutions ---------------------------------------------------------------

-- Modes and Terms

open import KitTheory.Modes

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = Term ; `_ = `_ }

-- Kits and Traversals

open import KitTheory.Kit 𝕋
open Kit {{...}} public

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ M
  (` x)     ⋯ f = tm' (f _ x)
  (λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ 𝕖))
  (Λ→ t)    ⋯ f = Λ→ (t ⋯ (f ↑ 𝕥))
  (∀→ t)    ⋯ f = ∀→ (t ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  (t₁ ∙ t₂) ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
  (t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
  ★         ⋯ f = ★
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
          (` x) ⋯ f ≡ tm' (f _ x)
  ⋯-var _ _ = refl

open KitTraversal kit-traversal public

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Traversal Composition

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : Term µ₁ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc (` X) f g =
    tm' (f _ X) ⋯ g    ≡⟨ tm'-⋯-∘ f g X ⟩
    tm' ((g ∘ₖ f) _ X) ∎
  ⋯-assoc (λ→ e) f g = cong λ→_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (Λ→ e) f g = cong Λ→_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (∀→ e) f g = cong ∀→_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ∙ e₂) f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc ★         f g = refl

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ M) →
         v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                             = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λ→ t)   rewrite id↑≡id {{𝕂}} 𝕖 µ = cong λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Λ→ t)   rewrite id↑≡id {{𝕂}} 𝕥 µ = cong Λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (∀→ t)   rewrite id↑≡id {{𝕂}} 𝕥 µ = cong ∀→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                                 = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts

open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

Type : List Modeᵥ → Modeₜ → Set
Type = _∶⊢_

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : Type µ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → Term µ M → Type µ M → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : Type µ 𝕖} {x : 𝕖 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λ→ e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ,, ★ ⊢ e ∶ t₂ →
    Γ ⊢ Λ→ e ∶ ∀→ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx µ} →
    Γ ⊢ e ∶ ∀→ t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-𝕥 :
    Γ ⊢ t ∶ ★
  τ-𝕜 :
    Γ ⊢ ★ ∶ ★

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- Semantics -------------------------------------------------------------------

data Neutral : Term µ 𝕖 → Set where
  n-`  : Neutral (` x)
  n-·₁ : Neutral e₁ → Neutral (e₁ · e₂)
  n-∙₁ : Neutral e → Neutral (e ∙ t)

data Value : Term µ 𝕖 → Set where
  λ→_     : Value e → Value (λ→ e)
  Λ→_     : Value e → Value (Λ→ e)
  neutral : Neutral e → Value e

data _↪_ : Term µ 𝕖 → Term µ 𝕖 → Set where
  β-λ : ∀ {e₂ : Term µ 𝕖} →
    (λ→ e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t : Term µ 𝕥} →
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
