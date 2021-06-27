module Examples.LambdaPi-Kits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_)
open import Level using (Level; _⊔_)
open import Function using (id; _∘_; const)
open import Data.String

open import KitTheory.Prelude using (_∋_; _,_) public

infix   3  _↪_  _↪*_  _⊢_∶_  _⊢*_∶_  _⇓_
infixr  5  λ→_
infixl  6  _·_
infix   7  `_

-- Syntax ----------------------------------------------------------------------

data Mode : Set where
  𝕥 : Mode

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Mode
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Mode
  x y z                     : 𝕥 ∈ µ
  ℓ ℓ₁ ℓ₂                    : Level
  A B C D E                 : Set ℓ

data Term : List Mode → Mode → Set where
  `_  : m ∈ µ → Term µ m
  _·_ : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
  λ→_ : Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  Π   : Term µ 𝕥 → Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  ★   : Term µ 𝕥

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Term µ 𝕥
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : Term µ 𝕥

-- Substitution ----------------------------------------------------------------

-- Modes and Terms

open import KitTheory.Modes

𝕄 : Modes
𝕄 = record { VarMode = Mode ; TermMode = Mode ; m→M = id }

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = Term ; `_ = `_ }

-- Kits and Traversals

open import KitTheory.Kit 𝕋
open Kit {{...}} public

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ m → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ m
  (` x)     ⋯ f = tm _ (f _ x)
  (λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ 𝕥))
  Π t₁ t₂   ⋯ f = Π (t₁ ⋯ f) (t₂ ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  ★         ⋯ f = ★
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
          (` x) ⋯ f ≡ tm _ (f _ x)
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
              (v : Term µ₁ m) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc (` x)     f g = tm-⋯-∘ f g x
  ⋯-assoc (t₁ · t₂) f g = cong₂ _·_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (λ→ t)    f g = cong λ→_
    (t ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t (f ↑ _) (g ↑ _) ⟩
     t ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     t ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (Π t₁ t₂) f g = cong₂ Π (⋯-assoc t₁ f g)
    (t₂ ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t₂ (f ↑ _) (g ↑ _) ⟩
     t₂ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t₂ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     t₂ ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc ★         f g = refl

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ m) →
         v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                              = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λ→ t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Π t₁ t₂) rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₂ Π (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                                  = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts

open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕥 → 𝕥 } }

open KitType kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : Term µ 𝕥 → Set where
    `x  : Neutral (` x)
    _·_ : Neutral t₁ → Value t₂ → Neutral (t₁ · t₂)

  data Value : Term µ 𝕥 → Set where
    λ→_     : Value t → Value (λ→ t)
    Π       : Value t₁ → Value t₂ → Value (Π t₁ t₂)
    ★       : Value {µ} ★
    neutral : Neutral t → Value t

data _↪_ : Term µ 𝕥 → Term µ 𝕥 → Set where
  β-λ : ∀ {t₂ : Term µ 𝕥} →
    (λ→ t₁) · t₂ ↪ t₁ ⋯ ⦅ t₂ ⦆
  ξ-λ :
    t ↪ t' →
    λ→ t ↪ λ→ t'
  ξ-·₁ :
    t₁ ↪ t₁' →
    t₁ · t₂ ↪ t₁' · t₂
  ξ-·₂ :
    t₂ ↪ t₂' →
    t₁ · t₂ ↪ t₁ · t₂'
  ξ-Π₁ :
    t₁ ↪ t₁' →
    Π t₁ t₂ ↪ Π t₁' t₂
  ξ-Π₂ :
    t₂ ↪ t₂' →
    Π t₁ t₂ ↪ Π t₁ t₂'

data _↪*_ : Term µ 𝕥 → Term µ 𝕥 → Set where
  *-refl : t ↪* t
  *-step : t₁ ↪* t₂ → t₂ ↪ t₃ → t₁ ↪* t₃

_⇓_ : Term µ 𝕥 → Term µ 𝕥 → Set
t₁ ⇓ t₂ = t₁ ↪* t₂ × Value t₂

-- Typing ----------------------------------------------------------------------

Values : Ctx µ → Set
Values Γ = ∀ x → Value (Γ {𝕥} x)

data _⊢_∶_ : Ctx µ → Term µ 𝕥 → Term µ 𝕥 → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : Term µ 𝕥} {x : 𝕥 ∈ µ} →
    Values Γ →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ⊢ t₁ ∶ ★ →
    t₁ ⇓ t₁' →
    Γ ,, t₁' ⊢ e ∶ t₂ →
    Γ ⊢ λ→ e ∶ Π t₁' t₂
  τ-· : ∀ {Γ : Ctx µ} →
    Γ ⊢ e₁ ∶ Π t₁ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    t₂ ⋯ ⦅ t₁ ⦆ ⇓ t₃ →
    Γ ⊢ e₁ · e₂ ∶ t₃
  τ-Π :
    t₁ ⇓ t₁' →
    Γ        ⊢ t₁      ∶ ★ →
    Γ ,, t₁' ⊢ t₂      ∶ ★ →
    Γ        ⊢ Π t₁ t₂ ∶ ★
  τ-★ :
    Values Γ →
    Γ ⊢ ★ ∶ ★

-- data _[_]⊢_∶_[_] : (Γ : Ctx µ) → Values Γ → Term µ 𝕥 → (t : Term µ 𝕥) → Value t → Set where
--   τ-` : ∀ {Γ : Ctx µ} {t : Term µ 𝕥} {x : 𝕥 ∈ µ} →
--     wk-telescope Γ x ≡ t →
--     Γ [ Γ-val ]⊢ ` x ∶ t [ ? ]
--   -- τ-λ : ∀ {Γ : Ctx µ} →
--   --   Γ ⊢ t₁ ∶ ★ →
--   --   t₁ ⇓ t₁' →
--   --   Γ ,, t₁' ⊢ e ∶ t₂ →
--   --   Γ ⊢ λ→ e ∶ Π t₁ t₂
--   -- τ-· : ∀ {Γ : Ctx µ} →
--   --   Γ ⊢ e₁ ∶ Π t₁ t₂ →
--   --   Γ ⊢ e₂ ∶ t₁ →
--   --   t₂ ⋯ ⦅ t₁ ⦆ ⇓ t₃ →
--   --   Γ ⊢ e₁ · e₂ ∶ t₃
--   -- τ-Π :
--   --   t₁ ⇓ t₁' →
--   --   Γ        ⊢ t₁      ∶ ★ →
--   --   Γ ,, t₁' ⊢ t₂      ∶ ★ →
--   --   Γ        ⊢ Π t₁ t₂ ∶ ★
--   -- τ-★ :
--   --   Γ ⊢ ★ ∶ ★

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = (x : µ₁ ∋ 𝕥) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
