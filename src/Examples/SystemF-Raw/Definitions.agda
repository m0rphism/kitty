module Examples.SystemF-Raw.Definitions where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _∘_; flip)
open import Data.Nat using (ℕ; zero; suc)

infixr  3  _↪_  _⊢_∶_  _⊢*_∶_
infixr  4  ∀α_  λx_  Λα_
infixr  5  _⇒_
infixl  5  _·_  _∙_
infixl  5  _,ₖ_  _,ₛ_  _,ᵣ_  _,,_
infix   5  _→ᵣ_  _→ₛ_
infixl  5  _⋯_  _⋯ₛ_  _⋯ᵣ_  _⋯ₜ_  _⋯ₜₛ_  _⋯ₜᵣ_
infixl  6  _↑_
infix   7  `_

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C      : Set ℓ

-- Syntax ----------------------------------------------------------------------

data Mode : Set where
  𝕧 : Mode -- The kind of value-level variables.
  𝕥 : Mode -- The kind of type-level variables.

variable
  m m₁ m₂    : Mode
  m' m₁' m₂' : Mode
  µ µ₁ µ₂ µ₃ : List Mode
  µ' µ₁' µ₂' : List Mode
  µ₁₁ µ₁₂    : List Mode
  µ₂₁ µ₂₂    : List Mode
  x y z      : 𝕧 ∈ µ
  α β γ      : 𝕥 ∈ µ
  X Y Z      : m ∈ µ

data Term : List Mode → Mode → Set where
  `_  : m ∈ µ → Term µ m                -- Expr and Type Variables
  λx_ : Term (𝕧 ∷ µ) 𝕧 → Term µ 𝕧
  Λα_ : Term (𝕥 ∷ µ) 𝕧 → Term µ 𝕧
  ∀α_ : Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  _·_ : Term µ 𝕧 → Term µ 𝕧 → Term µ 𝕧
  _∙_ : Term µ 𝕧 → Term µ 𝕥 → Term µ 𝕧
  _⇒_ : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥

Type : List Mode → Mode → Set
Type µ 𝕧 = Term µ 𝕥
Type µ 𝕥 = ⊤

variable
  e  e₁  e₂  : Term µ 𝕧
  e' e₁' e₂' : Term µ 𝕧
  t  t₁  t₂  : Type µ 𝕧
  t' t₁' t₂' : Type µ 𝕧
  v  v₁  v₂  : Term µ m
  T  T₁  T₂  : Type µ m

-- Kits ------------------------------------------------------------------------

infix  4  _∋_  _⊢_

_∋_ : {A : Set} → List A → A → Set
_∋_ = flip _∈_

_⊢_ : List Mode → Mode → Set
_⊢_ = Term

record Kit : Set₁ where
  constructor kit
  field
    _∋/⊢_   : List Mode → Mode → Set
    id/`    : ∀ m → µ ∋ m → µ ∋/⊢ m
    `/id    : ∀ m → µ ∋/⊢ m → µ ⊢ m
    id/`/id : ∀ (x    : µ ∋ m) → `/id _ (id/` _ x) ≡ ` x
    wk      : ∀ m → µ ∋/⊢ m → (m' ∷ µ) ∋/⊢ m
    wk-id/` : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (id/` _ x) ≡ id/` _ (there x)

  -- Substitution or Renaming - depending on which kit is used.
  _–→_ : List Mode → List Mode → Set
  _–→_ µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢ m

open Kit {{...}}

_–[_]→_ : List Mode → (K : Kit) → List Mode → Set
µ₁ –[ K ]→ µ₂ = Kit._–→_ K µ₁ µ₂

-- Lifting a substitution/renaming
_↑_ : {{K : Kit}} → µ₁ –[ K ]→ µ₂ → (m : Mode) → (m ∷ µ₁) –[ K ]→ (m ∷ µ₂)
(f ↑ m) _ (here p)  = id/` _ (here p)
(f ↑ m) _ (there x) = wk _ (f _ x)

-- Applying a substitution/renaming
_⋯_ : {{K : Kit}} → µ₁ ⊢ m → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ m
(` x)     ⋯ f = `/id _ (f _ x)
(λx t)    ⋯ f = λx (t ⋯ (f ↑ 𝕧))
(Λα t)    ⋯ f = Λα (t ⋯ (f ↑ 𝕥))
(∀α t)    ⋯ f = ∀α (t ⋯ (f ↑ 𝕥))
(t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
(t₁ ∙ t₂) ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
(t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)

-- Renaming Kit
instance kitᵣ : Kit
Kit._∋/⊢_   kitᵣ     = _∋_
Kit.id/`    kitᵣ _   = id
Kit.`/id    kitᵣ _   = `_
Kit.id/`/id kitᵣ _   = refl
Kit.wk      kitᵣ _   = there
Kit.wk-id/` kitᵣ _ _ = refl

_→ᵣ_ : List Mode → List Mode → Set
_→ᵣ_ = _–[ kitᵣ ]→_

-- Substitution Kit
instance kitₛ : Kit
Kit._∋/⊢_   kitₛ     = _⊢_
Kit.id/`    kitₛ _   = `_
Kit.`/id    kitₛ _   = id
Kit.id/`/id kitₛ _   = refl
Kit.wk      kitₛ _   = _⋯ wk
Kit.wk-id/` kitₛ _ _ = refl

_→ₛ_ : List Mode → List Mode → Set
_→ₛ_ = _–[ kitₛ ]→_

_⋯ₛ_ :  µ₁ ⊢ m → µ₁ →ₛ µ₂ → µ₂ ⊢ m
_⋯ₛ_ = _⋯_

_⋯ᵣ_ :  µ₁ ⊢ m → µ₁ →ᵣ µ₂ → µ₂ ⊢ m
_⋯ᵣ_ = _⋯_

_⋯ₜ_ : {{K : Kit}} → Type µ₁ m → µ₁ –[ K ]→ µ₂ → Type µ₂ m
_⋯ₜ_ {m = 𝕧} T f = T ⋯ f
_⋯ₜ_ {m = 𝕥} T f = tt

_⋯ₜₛ_ : Type µ₁ m → µ₁ →ₛ µ₂ → Type µ₂ m
_⋯ₜₛ_ = _⋯ₜ_

_⋯ₜᵣ_ : Type µ₁ m → µ₁ →ᵣ µ₂ → Type µ₂ m
_⋯ₜᵣ_ = _⋯ₜ_

wkt : Type µ m → Type (m' ∷ µ) m
wkt = _⋯ₜ wk

idₖ : {{K : Kit}} → µ –[ K ]→ µ
idₖ = id/`

idₛ : µ →ₛ µ
idₛ = idₖ

idᵣ : µ →ᵣ µ
idᵣ = idₖ

_,ₖ_ : {{K : Kit}} → µ₁ –[ K ]→ µ₂ → µ₂ ∋/⊢ m → (m ∷ µ₁) –[ K ]→ µ₂
(f ,ₖ t) _ (here refl) = t
(f ,ₖ t) _ (there x) = f _ x

_,ₛ_ : µ₁ →ₛ µ₂ → Term µ₂ m → (m ∷ µ₁) →ₛ µ₂
_,ₛ_ = _,ₖ_

_,ᵣ_ : µ₁ →ᵣ µ₂ → µ₂ ∋ m → (m ∷ µ₁) →ᵣ µ₂
_,ᵣ_ = _,ₖ_

⦅_⦆ : Term µ m → (m ∷ µ) →ₛ µ
⦅ v ⦆ = idₖ ,ₛ v

_∘ₛ_ : {{K₁ K₂ : Kit}} → µ₂ –[ K₂ ]→ µ₃ → µ₁ –[ K₁ ]→ µ₂ → µ₁ →ₛ µ₃
(f ∘ₛ g) _ x = `/id _ (g _ x) ⋯ f

_∘ᵣ_ : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
(ρ₁ ∘ᵣ ρ₂) _ = ρ₁ _ ∘ ρ₂ _

_∘ₛᵣ_ : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
(σ₁ ∘ₛᵣ ρ₂) _ = σ₁ _ ∘ ρ₂ _

_∘ᵣₛ_ : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
(ρ₁ ∘ᵣₛ σ₂) _ x = σ₂ _ x ⋯ ρ₁

-- Type System -----------------------------------------------------------------

-- Interpret a scoped debruijn index `x ∈ xs` as a natural number,
-- i.e.  the index of `x` in `xs`.
depth : ∀ {x : A} {xs : List A} → x ∈ xs → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

-- Given a scoped debruijn index `x ∈ xs` and some List, this function
-- interprets the `x ∈ xs` as a natural number `n` and drops `n+1`
-- elements from the list.
-- Used in and motivated by the definition of `Ctx` below.
-- We drop `n+1` instead of `n` elements, because otherwise the types
-- in the context would be allowed to use themselves.
drop-∈ : ∀ {x : A} {xs : List A} → x ∈ xs → List A → List A
drop-∈ = drop ∘ suc ∘ depth

Ctx : List Mode → Set
Ctx µ = ∀ {m} → (x : m ∈ µ) → Type (drop-∈ x µ) m

wk-drop-∈ : (x : m ∈ µ) → Type (drop-∈ x µ) m → Type µ m
wk-drop-∈ (here _)  t = wkt t
wk-drop-∈ (there x) t = wkt (wk-drop-∈ x t)

-- Access a `Ctx µ` and weaken the resulting type, such that it refers
-- to `µ` instead of a `µ`-suffix.
wk-telescope : Ctx µ → m ∈ µ → Type µ m
wk-telescope Γ x = wk-drop-∈ x (Γ x)

variable
  Γ  Γ₁  Γ₂  : Ctx µ

_,,_ : Ctx µ → Type µ m → Ctx (m ∷ µ)
(Γ ,, t) (here refl) = t
(Γ ,, t) (there x) = Γ x

data _⊢_∶_ : Ctx µ → Term µ m → Type µ m → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : Type µ 𝕧} {x : 𝕧 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ,, t₁ ⊢ e ∶ t₂ ⋯ wk →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ,, tt ⊢ e ∶ t₂ →
    Γ ⊢ Λα e ∶ ∀α t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx µ} →
    Γ ⊢ e ∶ ∀α t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-𝕥 :
    Γ ⊢ t ∶ tt

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : m₁ ∈ µ₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ₜ σ)

-- Semantics -------------------------------------------------------------------

data _↪_ : Term µ 𝕧 → Term µ 𝕧 → Set where
  β-λ : ∀ {e₂ : Term µ 𝕧} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t : Term µ 𝕥} →
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
