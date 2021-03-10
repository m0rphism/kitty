module Examples.SystemF-Kits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)

infixr  3  _↪_  _⊢_∶_  _⊢*_∶_
infixr  4  ∀→_  λ→_  Λ→_
infixr  5  _⇒_
infixl  5  _·_  _∙_
infix   7  `_

-- Syntax ----------------------------------------------------------------------

data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Value-level variables.
  𝕥 : Modeᵥ  -- Type-level variables.

data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖
m→M 𝕥 = 𝕥

variable
  m m₁ m₂    : Modeᵥ
  m' m₁' m₂' : Modeᵥ
  M M₁ M₂    : Modeₜ
  M' M₁' M₂' : Modeₜ
  μ μ₁ μ₂ μ₃ : List Modeᵥ
  μ' μ₁' μ₂' : List Modeᵥ
  μ₁₁ μ₁₂    : List Modeᵥ
  μ₂₁ μ₂₂    : List Modeᵥ
  x y z      : 𝕖 ∈ μ
  α β γ      : 𝕥 ∈ μ
  X Y Z      : m ∈ μ

data Term : List Modeᵥ → Modeₜ → Set where
  `[_]_ : M ≡ m→M m → m ∈ μ → Term μ M  -- Expr and Type Variables
  λ→_   : Term (𝕖 ∷ μ) 𝕖 → Term μ 𝕖
  Λ→_   : Term (𝕥 ∷ μ) 𝕖 → Term μ 𝕖
  ∀→_   : Term (𝕥 ∷ μ) 𝕥 → Term μ 𝕥
  _·_   : Term μ 𝕖 → Term μ 𝕖 → Term μ 𝕖
  _∙_   : Term μ 𝕖 → Term μ 𝕥 → Term μ 𝕖
  _⇒_   : Term μ 𝕥 → Term μ 𝕥 → Term μ 𝕥
  ★   : Term μ 𝕜

pattern `_ x = `[ refl ] x

variable
  e  e₁  e₂  : Term μ 𝕖
  e' e₁' e₂' : Term μ 𝕖
  v  v₁  v₂  : Term μ M

-- Kits ------------------------------------------------------------------------

open import KitTheory.Everything Modeᵥ Modeₜ m→M Term `_ public

open Kit {{...}} public
open KitTraversal {{...}} public

instance traversal : KitTraversal
KitTraversal._⋯_ traversal (` x)     f = tm' (f _ x)
KitTraversal._⋯_ traversal (λ→ t)    f = λ→ (t ⋯ (f ↑ 𝕖))
KitTraversal._⋯_ traversal (Λ→ t)    f = Λ→ (t ⋯ (f ↑ 𝕥))
KitTraversal._⋯_ traversal (∀→ t)    f = ∀→ (t ⋯ (f ↑ 𝕥))
KitTraversal._⋯_ traversal (t₁ · t₂) f = (t₁ ⋯ f) · (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ∙ t₂) f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ⇒ t₂) f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
KitTraversal._⋯_ traversal ★       f = ★
KitTraversal.⋯-var traversal x f = refl

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

open AssocAssumptions {{...}} public
open KitCompose {{...}} public

instance ckit : KitCompose {{traversal}}
KitCompose.⋯-assoc ckit (` x) f g =
  tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  tm' ((g ∘ₖ f) _ x) ∎
KitCompose.⋯-assoc ckit (λ→ e) f g = cong λ→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (Λ→ e) f g = cong Λ→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (∀→ e) f g = cong ∀→_
  (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
KitCompose.⋯-assoc ckit (e₁ ∙ e₂) f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
KitCompose.⋯-assoc ckit (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
KitCompose.⋯-assoc ckit ★       f g = refl

instance AAᵣᵣ = AssocAssumptionsᵣᵣ
instance AAᵣₛ = AssocAssumptionsᵣₛ
instance AAₛᵣ = AssocAssumptionsₛᵣ
instance AAₛₛ = AssocAssumptionsₛₛ

instance kit-compose-lemmas : KitComposeLemmas
kit-compose-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term μ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                             = tm-vr x
  ⋯-id {μ = μ} {{𝕂}} (λ→ t)   rewrite id↑≡id {{𝕂}} 𝕖 μ = cong λ→_ (⋯-id t)
  ⋯-id {μ = μ} {{𝕂}} (Λ→ t)   rewrite id↑≡id {{𝕂}} 𝕥 μ = cong Λ→_ (⋯-id t)
  ⋯-id {μ = μ} {{𝕂}} (∀→ t)   rewrite id↑≡id {{𝕂}} 𝕥 μ = cong ∀→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                               = refl

open KitComposeLemmas {{...}} hiding (ckit) public

instance kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }
open KitType kit-type public hiding (kit-compose-lemmas)

Type : List Modeᵥ → Modeₜ → Set
Type = _∶⊢_

variable
  t  t₁  t₂  : Type μ 𝕖
  t' t₁' t₂' : Type μ 𝕖
  T  T₁  T₂  : Type μ M
  Γ  Γ₁  Γ₂  : Ctx μ

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
