module Examples.SystemF-Kits.Definitions where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

infixr  3  _↪_  _⊢_∶_  _⊢*_∶_
infixr  4  ∀→_  λ→_  Λ→_
infixr  5  _⇒_
infixl  5  _·_  _∙_  _⋯ₜ_  _⋯ₜᵣ_  _⋯ₜₛ_
infixl  5  _,,_
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

variable
  e  e₁  e₂  : Term κ ★
  e' e₁' e₂' : Term κ ★
  v  v₁  v₂  : Term κ k

-- Kits ------------------------------------------------------------------------

open import KitTheory.Everything Kind Kind id Term `_ public

open Kit {{...}} public
open KitTraversal {{...}} public

instance traversal : KitTraversal
KitTraversal._⋯_ traversal (` x)     f = tm' (f _ x)
KitTraversal._⋯_ traversal (λ→ t)    f = λ→ (t ⋯ (f ↑ ★))
KitTraversal._⋯_ traversal (Λ→ t)    f = Λ→ (t ⋯ (f ↑ ■))
KitTraversal._⋯_ traversal (∀→ t)    f = ∀→ (t ⋯ (f ↑ ■))
KitTraversal._⋯_ traversal (t₁ · t₂) f = (t₁ ⋯ f) · (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ∙ t₂) f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ⇒ t₂) f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
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
  (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
   e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
   e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (Λ→ e) f g = cong Λ→_
  (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
   e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
   e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (∀→ e) f g = cong ∀→_
  (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
   e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
   e ⋯ (g ∘ₖ f) ↑ _         ∎)
KitCompose.⋯-assoc ckit (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
KitCompose.⋯-assoc ckit (e₁ ∙ e₂) f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
KitCompose.⋯-assoc ckit (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

instance AAᵣᵣ = AssocAssumptionsᵣᵣ
instance AAᵣₛ = AssocAssumptionsᵣₛ
instance AAₛᵣ = AssocAssumptionsₛᵣ
instance AAₛₛ = AssocAssumptionsₛₛ

Type : List Kind → Kind → Set
Type κ ★ = Term κ ■
Type κ ■ = ⊤

_∶⊢_ : List Kind → Kind → Set
_∶⊢_ = Type

_⋯ₜ_ : {{𝕂 : Kit}} → κ₁ ∶⊢ k → κ₁ –[ 𝕂 ]→ κ₂ → κ₂ ∶⊢ k
_⋯ₜ_ {k = ★} T f = T ⋯ f
_⋯ₜ_ {k = ■} T f = tt

_⋯ₜₛ_ : κ₁ ∶⊢ k → κ₁ →ₛ κ₂ → κ₂ ∶⊢ k
_⋯ₜₛ_ = _⋯ₜ_

_⋯ₜᵣ_ : κ₁ ∶⊢ k → κ₁ →ᵣ κ₂ → κ₂ ∶⊢ k
_⋯ₜᵣ_ = _⋯ₜ_

wkₜ : κ ∶⊢ k → (k' ∷ κ) ∶⊢ k
wkₜ = _⋯ₜ wk

variable
  t  t₁  t₂  : Type κ ★
  t' t₁' t₂' : Type κ ★
  T  T₁  T₂  : Type κ k

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
wk-drop-∈ (here _)  t = wkₜ t
wk-drop-∈ (there x) t = wkₜ (wk-drop-∈ x t)

Ctx : List Kind → Set
Ctx κ = ∀ {k} → (x : k ∈ κ) → Type (drop-∈ x κ) k

-- Our context is defined as a telescope.
-- This function automatically weakens all the types in a `Ctx κ` such that they
-- refer to `κ` instead of a `κ`-suffix.
wk-telescope : Ctx κ → k ∈ κ → Type κ k
wk-telescope Γ x = wk-drop-∈ x (Γ x)

variable
  Γ Γ₁ Γ₂ : Ctx κ

_,,_ : Ctx κ → Type κ k → Ctx (k ∷ κ)
(Γ ,, t) (here refl) = t
(Γ ,, t) (there x) = Γ x

data _⊢_∶_ : Ctx κ → Term κ k → Type κ k → Set where
  τ-` : ∀ {Γ : Ctx κ} {t : Type κ ★} {x : ★ ∈ κ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx κ} →
    Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
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
