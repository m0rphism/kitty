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
infixr  4  ∀→_  λ→_  Λ→_
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

data Kind : Set where
  ★ : Kind -- The kind of value-level variables.
  ■ : Kind -- The kind of type-level variables.

variable
  k k₁ k₂    : Kind
  k' k₁' k₂' : Kind
  κ κ₁ κ₂ κ₃ : List Kind
  κ' κ₁' κ₂' : List Kind
  κ₁₁ κ₁₂    : List Kind
  κ₂₁ κ₂₂    : List Kind
  x y z      : ★ ∈ κ
  α β γ      : ■ ∈ κ
  X Y Z      : k ∈ κ

data Term : List Kind → Kind → Set where
  `_  : k ∈ κ → Term κ k                -- Expr and Type Variables
  λ→_ : Term (★ ∷ κ) ★ → Term κ ★
  Λ→_ : Term (■ ∷ κ) ★ → Term κ ★
  ∀→_ : Term (■ ∷ κ) ■ → Term κ ■
  _·_ : Term κ ★ → Term κ ★ → Term κ ★
  _∙_ : Term κ ★ → Term κ ■ → Term κ ★
  _⇒_ : Term κ ■ → Term κ ■ → Term κ ■

Type : List Kind → Kind → Set
Type κ ★ = Term κ ■
Type κ ■ = ⊤

variable
  e  e₁  e₂  : Term κ ★
  e' e₁' e₂' : Term κ ★
  t  t₁  t₂  : Type κ ★
  t' t₁' t₂' : Type κ ★
  v  v₁  v₂  : Term κ k
  T  T₁  T₂  : Type κ k

-- Kits ------------------------------------------------------------------------

infix  4  _∋_  _⊢_

_∋_ : {A : Set} → List A → A → Set
_∋_ = flip _∈_

_⊢_ : List Kind → Kind → Set
_⊢_ = Term

record Kit : Set₁ where
  constructor kit
  field
    _◆_ : List Kind → Kind → Set
    vr : κ ∋ k → κ ◆ k
    tm : κ ◆ k → κ ⊢ k
    wk : κ ◆ k → (k' ∷ κ) ◆ k
    wk-vr : ∀ k' (x : k ∈ κ) → wk {k' = k'} (vr x) ≡ vr (there x)
    tm-vr : ∀ (x : k ∈ κ) → tm (vr x) ≡ ` x

  _–→_ : List Kind → List Kind → Set
  _–→_ κ₁ κ₂ = ∀ k → κ₁ ∋ k → κ₂ ◆ k

open Kit {{...}}

_–[_]→_ : List Kind → (K : Kit) → List Kind → Set
κ₁ –[ K ]→ κ₂ = Kit._–→_ K κ₁ κ₂

_↑_ : {{K : Kit}} → κ₁ –[ K ]→ κ₂ → (k : Kind) → (k ∷ κ₁) –[ K ]→ (k ∷ κ₂)
(f ↑ k) _ (here p)  = vr (here p)
(f ↑ k) _ (there x) = wk (f _ x)

_⋯_ : {{K : Kit}} → κ₁ ⊢ k → κ₁ –[ K ]→ κ₂ → κ₂ ⊢ k
(` x)     ⋯ f = tm (f _ x)
(λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ ★))
(Λ→ t)    ⋯ f = Λ→ (t ⋯ (f ↑ ■))
(∀→ t)    ⋯ f = ∀→ (t ⋯ (f ↑ ■))
(t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
(t₁ ∙ t₂) ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
(t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)

instance kitᵣ : Kit
Kit._◆_   kitᵣ     = _∋_
Kit.vr    kitᵣ     = id
Kit.tm    kitᵣ     = `_
Kit.wk    kitᵣ     = there
Kit.wk-vr kitᵣ _ _ = refl
Kit.tm-vr kitᵣ _   = refl

_→ᵣ_ : List Kind → List Kind → Set
_→ᵣ_ = _–[ kitᵣ ]→_

there' : ∀ {k'} k → k ∈ κ → k ∈ (k' ∷ κ)
there' _ = there

instance kitₛ : Kit
Kit._◆_   kitₛ     = _⊢_
Kit.vr    kitₛ     = `_
Kit.tm    kitₛ     = id
Kit.wk    kitₛ     = _⋯ there'
Kit.wk-vr kitₛ _ _ = refl
Kit.tm-vr kitₛ _   = refl

_→ₛ_ : List Kind → List Kind → Set
_→ₛ_ = _–[ kitₛ ]→_

_⋯ₛ_ :  κ₁ ⊢ k → κ₁ →ₛ κ₂ → κ₂ ⊢ k
_⋯ₛ_ = _⋯_

_⋯ᵣ_ :  κ₁ ⊢ k → κ₁ →ᵣ κ₂ → κ₂ ⊢ k
_⋯ᵣ_ = _⋯_

_⋯ₜ_ : {{K : Kit}} → Type κ₁ k → κ₁ –[ K ]→ κ₂ → Type κ₂ k
_⋯ₜ_ {k = ★} T f = T ⋯ f
_⋯ₜ_ {k = ■} T f = tt

_⋯ₜₛ_ : Type κ₁ k → κ₁ →ₛ κ₂ → Type κ₂ k
_⋯ₜₛ_ = _⋯ₜ_

_⋯ₜᵣ_ : Type κ₁ k → κ₁ →ᵣ κ₂ → Type κ₂ k
_⋯ₜᵣ_ = _⋯ₜ_

wkt : Type κ k → Type (k' ∷ κ) k
wkt = _⋯ₜ there'

K-id : (K : Kit) → κ –[ K ]→ κ
K-id K = λ _ → Kit.vr K

ρ-id : κ →ᵣ κ
ρ-id = K-id kitᵣ

σ-id : κ →ₛ κ
σ-id = K-id kitₛ

_,ₖ_ : {{K : Kit}} → κ₁ –[ K ]→ κ₂ → κ₂ ◆ k → (k ∷ κ₁) –[ K ]→ κ₂
(f ,ₖ t) _ (here refl) = t
(f ,ₖ t) _ (there x) = f _ x

_,ₛ_ : κ₁ →ₛ κ₂ → Term κ₂ k → (k ∷ κ₁) →ₛ κ₂
_,ₛ_ = _,ₖ_

_,ᵣ_ : κ₁ →ᵣ κ₂ → κ₂ ∋ k → (k ∷ κ₁) →ᵣ κ₂
_,ᵣ_ = _,ₖ_

⦅_⦆ : Term κ k → (k ∷ κ) →ₛ κ
⦅ v ⦆ = σ-id ,ₛ v

_∘ₛ_ : {{K₁ K₂ : Kit}} → κ₂ –[ K₂ ]→ κ₃ → κ₁ –[ K₁ ]→ κ₂ → κ₁ →ₛ κ₃
(f ∘ₛ g) _ x = tm (g _ x) ⋯ f

_∘ᵣ_ : κ₂ →ᵣ κ₃ → κ₁ →ᵣ κ₂ → κ₁ →ᵣ κ₃
(ρ₁ ∘ᵣ ρ₂) _ = ρ₁ _ ∘ ρ₂ _

_∘ₛᵣ_ : κ₂ →ₛ κ₃ → κ₁ →ᵣ κ₂ → κ₁ →ₛ κ₃
(σ₁ ∘ₛᵣ ρ₂) _ = σ₁ _ ∘ ρ₂ _

_∘ᵣₛ_ : κ₂ →ᵣ κ₃ → κ₁ →ₛ κ₂ → κ₁ →ₛ κ₃
(ρ₁ ∘ᵣₛ σ₂) _ x = σ₂ _ x ⋯ ρ₁

-- Type System -----------------------------------------------------------------

depth : ∀ {x : A} {xs : List A} → x ∈ xs → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

-- We need to drop one extra using `suc`, because otherwise the types in a
-- context are allowed to use themselves.
drop-∈ : ∀ {x : A} {xs : List A} → x ∈ xs → List A → List A
drop-∈ = drop ∘ suc ∘ depth

-- wk-drop : ∀ n → Type (List.drop n κ) k → Type κ k
-- wk-drop              zero    t = t
-- wk-drop {κ = []}     (suc n) t = t -- This case (index > length) cannot happen with drop-∈
-- wk-drop {κ = k' ∷ κ} (suc n) t = wkt (wk-drop n t)

wk-drop-∈ : (x : k ∈ κ) → Type (drop-∈ x κ) k → Type κ k
wk-drop-∈ (here _)  t = wkt t
wk-drop-∈ (there x) t = wkt (wk-drop-∈ x t)

Ctx : List Kind → Set
Ctx κ = ∀ {k} → (x : k ∈ κ) → Type (drop-∈ x κ) k

-- Our context is defined as a telescope.
-- This function automatically weakens all the types in a `Ctx κ` such that they
-- refer to `κ` instead of a `κ`-suffix.
wk-telescope : Ctx κ → k ∈ κ → Type κ k
wk-telescope Γ x = wk-drop-∈ x (Γ x)

variable
  Γ  Γ₁  Γ₂  : Ctx κ

_,,_ : Ctx κ → Type κ k → Ctx (k ∷ κ)
(Γ ,, t) (here refl) = t
(Γ ,, t) (there x) = Γ x

data _⊢_∶_ : Ctx κ → Term κ k → Type κ k → Set where
  τ-` : ∀ {Γ : Ctx κ} {t : Type κ ★} {x : ★ ∈ κ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx κ} →
    Γ ,, t₁ ⊢ e ∶ wk t₂ →
    Γ ⊢ λ→ e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ,, tt ⊢ e ∶ t₂ →
    Γ ⊢ Λ→ e ∶ ∀→ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx κ} →
    Γ ⊢ e ∶ ∀→ t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-★ :
    Γ ⊢ t ∶ tt

_⊢*_∶_ : Ctx κ₂ → κ₁ →ₛ κ₂ → Ctx κ₁ → Set
_⊢*_∶_ {κ₁ = κ₁} Γ₂ σ Γ₁ = ∀ {k₁} → (x : k₁ ∈ κ₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ₜ σ)

-- Semantics -------------------------------------------------------------------

data _↪_ : Term κ ★ → Term κ ★ → Set where
  β-λ : ∀ {e₂ : Term κ ★} →
    (λ→ e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t : Term κ ■} →
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
