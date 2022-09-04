module Examples.STLCRef.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import KitTheory.Prelude using (_∋_; _,_) public
open import KitTheory.Modes using (Modes; Terms)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _;_↪_;_  _⊢_∶_  _⊢*_∶_
infixr  5  λx_  _≔_
infixr  6  _⇒_
infixr  6  !_
infixl  7  _·_
infix   8  `ʳ_  `ˣ_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕧 : Modeᵥ  -- Variables
  𝕣 : Modeᵥ  -- References

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕧 = 𝕖
m→M 𝕣 = 𝕖

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : 𝕧 ∈ µ
  α β γ                     : 𝕣 ∈ µ
  X Y Z                     : m ∈ µ

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `ˣ_   : µ ∋ 𝕧  →  µ ⊢ 𝕖
  `ʳ_   : µ ∋ 𝕣  →  µ ⊢ 𝕖
  λx_   : µ , 𝕧 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  new   : µ ⊢ 𝕖  →  µ ⊢ 𝕖
  !_    : µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _≔_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  Ref   : µ ⊢ 𝕥  →  µ ⊢ 𝕥
  Unit  : µ ⊢ 𝕥
  unit  : µ ⊢ 𝕖
  ★     : µ ⊢ 𝕜

-- Common constructor for both expression and type variables.
`_ : µ ∋ m → µ ⊢ m→M m
`_ {m = 𝕧} = `ˣ_
`_ {m = 𝕣} = `ʳ_

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = _⊢_ ; `_ = `_ }

variable
  e e₁ e₂ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t' t₁' t₂' : µ ⊢ 𝕥
  E E₁ E₂ E' E₁' E₂' : µ ⊢ M

-- Application of Renamings and Substitutions ----------------------------------

open import KitTheory.Kit 𝕋
open Kit {{...}} public

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  -- Traverse a term with a renaming or substitution (depending on the kit).
  _⋯_ : ∀ {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  (`ˣ x)    ⋯ f = tm _ (f _ x)
  (`ʳ α)    ⋯ f = tm _ (f _ α)
  (λx t)    ⋯ f = λx (t ⋯ (f ↑ 𝕧))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  (t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
  (new t)   ⋯ f = new (t ⋯ f)
  (Ref t)   ⋯ f = Ref (t ⋯ f)
  (! t)     ⋯ f = ! (t ⋯ f)
  (t₁ ≔ t₂) ⋯ f = (t₁ ⋯ f) ≔ (t₂ ⋯ f)
  Unit      ⋯ f = Unit
  unit      ⋯ f = unit
  ★         ⋯ f = ★
  -- Applying a renaming or substitution to a variable does the expected thing.
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (` x) ⋯ f ≡ tm _ (f _ x)
  ⋯-var {m = 𝕧} _ _ = refl
  ⋯-var {m = 𝕣} _ _ = refl

open KitTraversal kit-traversal public

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
  ⋯-assoc (`ˣ x) f g =
    tm _ (f _ x) ⋯ g    ≡⟨ tm-⋯-∘ f g x ⟩
    tm _ ((g ∘ₖ f) _ x) ∎
  ⋯-assoc (`ʳ α) f g =
    tm _ (f _ α) ⋯ g    ≡⟨ tm-⋯-∘ f g α ⟩
    tm _ ((g ∘ₖ f) _ α) ∎
  ⋯-assoc (λx e) f g = cong λx_
    (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
    e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    e ⋯ (g ∘ₖ f) ↑ _         ∎)
  ⋯-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc (new e) f g = cong new (⋯-assoc e f g)
  ⋯-assoc (Ref e) f g = cong Ref (⋯-assoc e f g)
  ⋯-assoc (! e) f g = cong !_ (⋯-assoc e f g)
  ⋯-assoc (e₁ ≔ e₂) f g = cong₂ _≔_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
  ⋯-assoc Unit f g = refl
  ⋯-assoc unit f g = refl
  ⋯-assoc ★ f g = refl

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (`ˣ x)                             = tm-vr x
  ⋯-id               (`ʳ α)                             = tm-vr α
  ⋯-id {µ = µ} {{𝕂}} (λx t)    rewrite id↑≡id {{𝕂}} 𝕧 µ = cong λx_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                          = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (new t)                            = cong new (⋯-id t)
  ⋯-id               (Ref t)                            = cong Ref (⋯-id t)
  ⋯-id               (! t)                              = cong !_ (⋯-id t)
  ⋯-id               (t₁ ≔ t₂)                          = cong₂ _≔_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               Unit                               = refl
  ⋯-id               unit                               = refl
  ⋯-id               ★                                  = refl

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts ----------------------------------------------------------

open import KitTheory.Types 𝕋

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

open KitType kit-type public

open import KitTheory.OPE 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  τ-`ˣ : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕧 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-`ʳ : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕣 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-≔ :
    Γ ⊢ e₁ ∶ Ref t →
    Γ ⊢ e₂ ∶ t →
    Γ ⊢ e₁ ≔ e₂ ∶ Unit
  τ-! :
    Γ ⊢ e ∶ Ref t →
    Γ ⊢ ! e ∶ t
  τ-new :
    Γ ⊢ e ∶ t →
    Γ ⊢ new e ∶ Ref t
  τ-unit :
    Γ ⊢ unit ∶ Unit
  τ-𝕥 :
    Γ ⊢ t ∶ ★
  τ-𝕜 :
    Γ ⊢ ★ ∶ ★

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

Store : List Modeᵥ → Set
Store µ = (x : µ ∋ 𝕣) → µ ⊢ 𝕖

_↑Σ_ : Store µ → ∀ m → Store (µ , m)
(Σ ↑Σ .𝕣) (here refl) = `ʳ here refl
(Σ ↑Σ m) (there x) = wk _ (Σ x)

open import Relation.Nullary using (Dec; yes; no; _because_)
_∋≟_ : (x y : µ ∋ m) → Dec (x ≡ y)
here px ∋≟ here py rewrite px | py = yes refl
here px ∋≟ there y = no (λ ())
there x ∋≟ here py = no (λ ())
there x ∋≟ there y with x ∋≟ y
... | yes refl = yes refl
... | no  p = no (λ { refl → p refl })

_,Σ[_≔_] : Store µ → (α : µ ∋ 𝕣) → µ ⊢ 𝕖 → Store µ
(Σ ,Σ[ x ≔ e ]) y with x ∋≟ y
... | yes p = e
... | no  p = Σ x

_,Σ_ : Store µ → µ ⊢ 𝕖 → Store (µ , 𝕣)
(Σ ,Σ e) (here px) = wk _ e
(Σ ,Σ e) (there x) = wk _ (Σ x)

variable Σ Σ' Σ₁ Σ₂ : Store µ

-- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ 𝕖 → Set where
--     `x  : Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
--     _∙t : Neutral e → Neutral (e ∙ t)

--   data Value : µ ⊢ 𝕖 → Set where
--     λx_     : Value e → Value (λx e)
--     Λα_     : Value e → Value (Λα e)
--     neutral : Neutral e → Value e

data _;_↪_;_ : Store µ₁ → µ₁ ⊢ 𝕖 → Store µ₂ → µ₂ ⊢ 𝕖 → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} {Σ : Store µ} →
    Σ ; (λx e₁) · e₂ ↪ Σ ; e₁ ⋯ ⦅ e₂ ⦆
  β-! : ∀ {e₂ : µ ⊢ 𝕖} →
    Σ ; ! (`ʳ α) ↪ Σ ; Σ α
  β-≔ : ∀ {e₂ : µ ⊢ 𝕖} →
    Σ ; (`ʳ α) ≔ e ↪ (Σ ,Σ[ α ≔ e ]) ; unit
  β-new : ∀ {e₂ : µ ⊢ 𝕖} →
    Σ ; new e ↪ (Σ ,Σ e) ; `ʳ here refl
  ξ-! : ∀ {e : µ , 𝕧 ⊢ 𝕖} {Σ : Store µ} →
    Σ₁ ; e ↪ Σ₂ ; e' →
    Σ₁ ; ! e ↪ Σ₂ ; ! e'
  ξ-new : ∀ {e : µ , 𝕧 ⊢ 𝕖} {Σ : Store µ} →
    Σ₁ ; e ↪ Σ₂ ; e' →
    Σ₁ ; new e ↪ Σ₂ ; new e'
  ξ-≔₁ :
    Σ₁ ; e₁      ↪ Σ₂ ; e₁' →
    Σ₁ ; e₁ ≔ e₂ ↪ Σ₂ ; e₁' ≔ e₂
  ξ-≔₂ :
    Σ₁ ; e₂      ↪ Σ₂ ; e₂' →
    Σ₁ ; e₁ ≔ e₂ ↪ Σ₂ ; e₁ ≔ e₂'
  ξ-λ : ∀ {e : µ , 𝕧 ⊢ 𝕖} {Σ : Store µ} →
    (Σ₁ ↑Σ 𝕧) ; e ↪ (Σ₂ ↑Σ 𝕧) ; e' →
    Σ₁ ; λx e ↪ Σ₂ ; λx e'
  ξ-·₁ :
    Σ₁ ; e₁      ↪ Σ₂ ; e₁' →
    Σ₁ ; e₁ · e₂ ↪ Σ₂ ; e₁' · e₂
  ξ-·₂ :
    Σ₁ ; e₂      ↪ Σ₂ ; e₂' →
    Σ₁ ; e₁ · e₂ ↪ Σ₂ ; e₁ · e₂'
