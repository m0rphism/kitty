module Examples.SystemFLin-Kits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Substructural.Usage

infix   3  _↪_  _;_⊢_∶_  _;_⊢*_∶_
infixr  5  ∀[_]→_  λ→_  Λ→_
infixr  6  _⇒[_]_
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
  `[_]_  : M ≡ m→M m → m ∈ µ → Term µ M  -- Expr and Type Variables
  λ→_    : Term (𝕖 ∷ µ) 𝕖 → Term µ 𝕖
  Λ→_    : Term (𝕥 ∷ µ) 𝕖 → Term µ 𝕖
  ∀[_]→_ : Usage → Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  _·_    : Term µ 𝕖 → Term µ 𝕖 → Term µ 𝕖
  _∙_    : Term µ 𝕖 → Term µ 𝕥 → Term µ 𝕖
  _⇒[_]_ : Term µ 𝕥 → Usage → Term µ 𝕥 → Term µ 𝕥
  ★      : Usage → Term µ 𝕜

pattern `_ x = `[ refl ] x

variable
  e e₁ e₂ e' e₁' e₂' : Term µ 𝕖
  t t₁ t₂ t' t₁' t₂' : Term µ 𝕥
  k k₁ k₂ k' k₁' k₂' : Term µ 𝕜
  E E₁ E₂ E' E₁' E₂' : Term µ M
  u u₁ u₂ u' u₁' u₂' : Usage

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
  (` x)          ⋯ f = tm' (f _ x)
  (λ→ t)         ⋯ f = λ→ (t ⋯ (f ↑ 𝕖))
  (Λ→ t)         ⋯ f = Λ→ (t ⋯ (f ↑ 𝕥))
  (∀[ u ]→ t)    ⋯ f = ∀[ u ]→ (t ⋯ (f ↑ 𝕥))
  (t₁ · t₂)      ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  (t₁ ∙ t₂)      ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
  (t₁ ⇒[ u ] t₂) ⋯ f = (t₁ ⋯ f) ⇒[ u ] (t₂ ⋯ f)
  ★ u            ⋯ f = ★ u
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
  ⋯-assoc (∀[ u ]→ e) f g = cong ∀[ u ]→_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (e₁ · e₂)      f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ∙ e₂)      f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ⇒[ u ] e₂) f g = cong₂ _⇒[ u ]_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (★ u)          f g = refl

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
  ⋯-id               (` x)                                = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λ→ t)      rewrite id↑≡id {{𝕂}} 𝕖 µ = cong λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Λ→ t)      rewrite id↑≡id {{𝕂}} 𝕥 µ = cong Λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (∀[ u ]→ t) rewrite id↑≡id {{𝕂}} 𝕥 µ = cong ∀[ u ]→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                            = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                            = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒[ u ] t₂)                       = cong₂ _⇒[ u ]_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (★ u)                                = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts

open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

Type : List Modeᵥ → Modeₜ → Set
Type = _∶⊢_

UCtx : List Modeᵥ → Set
UCtx µ = ∀ m → (x : µ ∋ m) → Usage

⟦0⟧ ⟦1⟧ ⟦∞⟧ : ∀ {ks} → UCtx ks
⟦0⟧ _ _ = [0]
⟦1⟧ _ _ = [1]
⟦∞⟧ _ _ = [∞]

⟦_⟧ : ∀ {ks} → Usage → UCtx ks
⟦ u ⟧ _ _ = u

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  Ψ Ψ₁ Ψ₂ Ψ' Ψ₁' Ψ₂' : UCtx µ
  T T₁ T₂ T' T₁' T₂' : Type µ M

open Lattice {{...}} public
open Semiring {{...}} public
open Instances-∀ fun-ext using (Semiring-∀; Lattice-∀) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl) public
open import Data.List.Relation.Unary.Any using (here; there) public

instance
  _ = Semiring-Usage
  _ = Semiring-∀
  _ = Lattice-Usage
  _ = Lattice-∀

_,,Ψ_ : UCtx µ → Usage → UCtx (m ∷ µ)
(Ψ ,,Ψ u) _ (here refl) = u
(Ψ ,,Ψ u) _ (there x) = Ψ _ x

-- Type System -----------------------------------------------------------------

data _;_⊢_∶_ : Ctx µ → UCtx µ → Term µ M → Type µ M → Set where
  τ-x : ∀ {Γ : Ctx µ} {Ψ : UCtx µ} {t : Type µ 𝕖} {x : 𝕖 ∈ µ} →
    wk-telescope Γ x ≡ t →
    [1] ⊑ Ψ _ x →
    (∀ m → (y : µ ∋ m) → (y ≅ x) ⊎ (Ψ _ y ≢ [1])) →
    Γ ; Ψ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ; Ψ ⊢ t₁ ∶ ★ u →
    Ψ ≡ Ψ * ⟦ u ⟧ →
    Γ ,, t₁ ; Ψ ,,Ψ u ⊢ e ∶ wk _ t₂ →
    Γ ; Ψ ⊢ λ→ e ∶ t₁ ⇒[ u ] t₂
  τ-Λ :
    Γ ,, ★ u ; Ψ ,,Ψ [0] ⊢ e ∶ t₂ →
    Γ ; Ψ ⊢ Λ→ e ∶ ∀[ u ]→ t₂
  τ-· :
    Γ ; Ψ₁ ⊢ e₁ ∶ t₁ ⇒[ u ] t₂ →
    Γ ; Ψ₂ ⊢ e₂ ∶ t₁ →
    Γ ; Ψ₁ + Ψ₂ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx µ} →
    Γ ; Ψ ⊢ e ∶ ∀[ u ]→ t₂ →
    Γ ; Ψ ⊢ t ∶ ★ u →
    Γ ; Ψ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-α :
    wk-telescope Γ α ≡ ★ u →
    Γ ; Ψ ⊢ ` α ∶ ★ u
  τ-⇒ :
    Γ ; Ψ ⊢ t₁ ⇒[ u ] t₂ ∶ ★ u
  τ-∀ :
    Γ ,, ★ u₁ ; Ψ ,,Ψ [0] ⊢ t ∶ ★ u₂ →
    Γ ; Ψ ⊢ ∀[ u₁ ]→ t ∶ ★ u₂
  τ-★ :
    Γ ; Ψ ⊢ ★ u ∶ ★ [0]

_;_⊢*_∶_ : Ctx µ₂ → UCtx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_;_⊢*_∶_ {µ₁ = µ₁} Γ₂ Ψ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ; Ψ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : Term µ 𝕖 → Set where
    `x  : Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙t : Neutral e → Neutral (e ∙ t)

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
