module Kitty.Experimental.Examples.SystemF-TypingKits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Kitty.Prelude using (_∋_; _▷_) public
open import Kitty.Modes using (Modes; Terms)
open import Data.Product using (∃-syntax)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_  _⊢*_∶_  _⊢ᵢ_
infixr  5  ∀α_  λx_  Λα_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `ᵅ_  `ˣ_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables
  𝕥 : Modeᵥ  -- Type-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖
m→M 𝕥 = 𝕥

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : 𝕖 ∈ µ
  α β γ                     : 𝕥 ∈ µ
  X Y Z                     : m ∈ µ

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `ˣ_   : µ ∋ 𝕖  →  µ ⊢ 𝕖
  `ᵅ_   : µ ∋ 𝕥  →  µ ⊢ 𝕥
  λx_   : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  Λα_   : µ ▷ 𝕥 ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀α_   : µ ▷ 𝕥 ⊢ 𝕥  →  µ ⊢ 𝕥
  _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _∙_   : µ ⊢ 𝕖  →  µ ⊢ 𝕥  →  µ ⊢ 𝕖
  _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  ★     : µ ⊢ 𝕜

-- Common constructor for both expression and type variables.
`_ : µ ∋ m → µ ⊢ m→M m
`_ {m = 𝕖} = `ˣ_
`_ {m = 𝕥} = `ᵅ_

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = _⊢_ ; `_ = `_ }

variable
  e e₁ e₂ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t' t₁' t₂' : µ ⊢ 𝕥
  k k₁ k₂ k' k₁' k₂' : µ ⊢ 𝕜
  E E₁ E₂ E' E₁' E₂' : µ ⊢ M

-- Application of Renamings and Substitutions ----------------------------------

open import Kitty.Kit 𝕋
open Kit {{...}} public

infixl  5  _⋯_

-- Traverse a term with a renaming or substitution (depending on the kit).
_⋯_ : ∀ {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
(`ˣ x)    ⋯ f = `/id _ (f _ x)
(`ᵅ α)    ⋯ f = `/id _ (f _ α)
(λx t)    ⋯ f = λx (t ⋯ (f ↑ 𝕖))
(Λα t)    ⋯ f = Λα (t ⋯ (f ↑ 𝕥))
(∀α t)    ⋯ f = ∀α (t ⋯ (f ↑ 𝕥))
(t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
(t₁ ∙ t₂) ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
(t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
★         ⋯ f = ★

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  -- Applying a renaming or substitution to a variable does the expected thing.
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (` x) ⋯ f ≡ `/id _ (f _ x)
  ⋯-var {m = 𝕖} _ _ = refl
  ⋯-var {m = 𝕥} _ _ = refl

open KitTraversal kit-traversal public hiding (_⋯_)

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Composition of Renamings and Substitutions ----------------------------------

open import Kitty.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    (v ⋯ f) ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc (`ˣ x) f g =
    `/id _ (f _ x) ⋯ g    ≡⟨ tm-⋯-∘ f g x ⟩
    `/id _ ((g ∘ₖ f) _ x) ∎
  ⋯-assoc (`ᵅ α) f g =
    `/id _ (f _ α) ⋯ g    ≡⟨ tm-⋯-∘ f g α ⟩
    `/id _ ((g ∘ₖ f) _ α) ∎
  ⋯-assoc (λx e) f g = cong λx_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (Λα e) f g = cong Λα_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (∀α e) f g = cong ∀α_
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
  ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (`ˣ x)                             = id/`/id x
  ⋯-id               (`ᵅ α)                             = id/`/id α
  ⋯-id {µ = µ} {{𝕂}} (λx t)    rewrite id↑≡id {{𝕂}} 𝕖 µ = cong λx_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Λα t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong Λα_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (∀α t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong ∀α_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                          = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                          = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                                  = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

open import Kitty.ITerms 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕖 ∈ µ} →
    Γ ∋   x ∶ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ▶ t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ▶ ★ ⊢ e ∶ t₂ →
    Γ ⊢ Λα e ∶ ∀α t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx µ} →
    Γ ⊢ e ∶ ∀α t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-𝕥 :
    Γ ⊢ t ∶ ★
  τ-𝕜 :
    Γ ⊢ ★ ∶ ★

⊢` : ∀ {Γ : Ctx µ} {x : µ ∋ m} {t} →
      Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t
⊢` {m = 𝕖} = τ-`
⊢` {m = 𝕥} {t = t} ∋x with t
...                      | ★ = τ-𝕥

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open import Kitty.IKit 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type iterms
open IKit {{...}} public
open import Data.List.Relation.Unary.Any using (here; there)

-- ikit-traversal : IKitTraversal
-- ikit-traversal = record { _⊢⋯_ = _⊢⋯_ } where
--   _⊢⋯_ : ∀ {{𝕂 : Kit}} {{IK : IKit 𝕂}} {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {f : µ₁ –[ 𝕂 ]→ µ₂} →
--         Γ₁ ⊢ e ∶ t → Γ₂ ◆*[ IK ] f ∶ Γ₁ → Γ₂ ⊢ e ⋯ f ∶ t ⋯ f
--   τ-` ⊢x      ⊢⋯ f = ◆tm (f _ _ ⊢x)
--   τ-λ ⊢e      ⊢⋯ f = τ-λ {!⊢e ⋯ f!}
--   τ-Λ ⊢e      ⊢⋯ f = {!!}
--   τ-· ⊢e₁ ⊢e₂ ⊢⋯ f = τ-· (⊢e₁ ⊢⋯ f) (⊢e₂ ⊢⋯ f)
--   τ-∙ ⊢e      ⊢⋯ f = {!!}
--   τ-𝕥         ⊢⋯ f = τ-𝕥
--   τ-𝕜         ⊢⋯ f = τ-𝕜

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

_∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
_∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ∋ ρ _ x ∶ (wk-telescope Γ₁ x ⋯ ρ)

open import Data.List.Relation.Unary.Any using (here; there)

ope-id' : ∀ {Γ : Ctx µ} →
  Γ ∋* idᵣ ∶ Γ
ope-id' x = sym (⋯-idᵣ _)

ope-keep'  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₁ ∶⊢ m→M m} →
  Γ₂ ∋* ρ ∶ Γ₁ →
  (Γ₂ ,, (T ⋯ ρ)) ∋* (ρ ↑ m) ∶ (Γ₁ ,, T)
ope-keep' {ρ = ρ} {T = T} ope (here refl) =
  T ⋯ ρ ⋯ wk        ≡⟨ sym (dist-↑-ren T ρ) ⟩
  T ⋯ wk ⋯ (ρ ↑ᵣ _) ∎
ope-keep' {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope (there x) =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk   ≡⟨ cong (_⋯ wk) (ope x) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ ρ ⋯ wk           ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ (ρ ↑ᵣ _)    ∎

ope-drop'  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₂ ∶⊢ m→M m} →
   Γ₂       ∋* ρ         ∶ Γ₁ →
  (Γ₂ ,, T) ∋* (wk ∘ᵣ ρ) ∶ Γ₁
ope-drop' {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope x =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk ≡⟨ cong (_⋯ wk) (ope x) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ ρ ⋯ wk         ≡⟨ ⋯-assoc (wk-drop-∈ x (Γ₁ x)) ρ wk ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ wk ∘ₖ ρ        ∎

-- Intrinsically Typed Variables
_∋ᵢ_ : Ctx µ → µ ∶⊢ m→M m → Set
Γ ∋ᵢ t = ∃[ x ] (Γ ∋ x ∶ t)

-- Intrinsically Typed Terms
_⊢ᵢ_ : Ctx µ → µ ∶⊢ M → Set
Γ ⊢ᵢ t = ∃[ e ] (Γ ⊢ e ∶ t)

-- Intrinsically Typed Substitutions
_→ₛᵢ_ : Ctx µ₁ → Ctx µ₂ → Set
Γ₁ →ₛᵢ Γ₂ = ∃[ σ ] (Γ₂ ⊢* σ ∶ Γ₁)

-- Intrinsically Typed Renamings
_→ᵣᵢ_ : Ctx µ₁ → Ctx µ₂ → Set
-- Γ₁ →ᵣᵢ Γ₂ = ∃[ ρ ] (OPE ρ Γ₁ Γ₂)
Γ₁ →ᵣᵢ Γ₂ = ∃[ ρ ] (Γ₂ ∋* ρ ∶ Γ₁)

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ 𝕖 → Set where
    `x  : Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙t : Neutral e → Neutral (e ∙ t)

  data Value : µ ⊢ 𝕖 → Set where
    λx_     : Value e → Value (λx e)
    Λα_     : Value e → Value (Λα e)
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t : µ ⊢ 𝕥} →
    (Λα e) ∙ t ↪ e ⋯ ⦅ t ⦆
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-Λ :
    e ↪ e' →
    Λα e ↪ Λα e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙ :
    e ↪ e' →
    e ∙ t ↪ e' ∙ t
