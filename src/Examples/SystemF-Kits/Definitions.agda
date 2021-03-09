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
infixl  5  _·_  _∙_
infixl  5  _,,_
infix   7  `_

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C      : Set ℓ

-- Syntax ----------------------------------------------------------------------

data VKind : Set where
  ★ : VKind -- The kind of value-level variables.
  ■ : VKind -- The kind of type-level variables.

data TKind : Set where
  ★ : TKind -- The kind of expressions
  ■ : TKind -- The kind of types
  ● : TKind -- The kind of sorts ("kinds")

k→K : VKind → TKind
k→K ★ = ★
k→K ■ = ■

↑ₖ : TKind → TKind
↑ₖ ★ = ■
↑ₖ ■ = ●
↑ₖ ● = ●

variable
  k k₁ k₂    : VKind
  k' k₁' k₂' : VKind
  K K₁ K₂    : TKind
  K' K₁' K₂' : TKind
  κ κ₁ κ₂ κ₃ : List VKind
  κ' κ₁' κ₂' : List VKind
  κ₁₁ κ₁₂    : List VKind
  κ₂₁ κ₂₂    : List VKind
  x y z      : ★ ∈ κ
  α β γ      : ■ ∈ κ
  X Y Z      : k ∈ κ

data Term : List VKind → TKind → Set where
  -- `_  : k ∈ κ → Term κ (k→K k)                -- Expr and Type Variables
  `ᵉ_ : ★ ∈ κ → Term κ ★
  `ᵗ_ : ■ ∈ κ → Term κ ■
  λ→_ : Term (★ ∷ κ) ★ → Term κ ★
  Λ→_ : Term (■ ∷ κ) ★ → Term κ ★
  ∀→_ : Term (■ ∷ κ) ■ → Term κ ■
  _·_ : Term κ ★ → Term κ ★ → Term κ ★
  _∙_ : Term κ ★ → Term κ ■ → Term κ ★
  _⇒_ : Term κ ■ → Term κ ■ → Term κ ■
  [★] : Term κ ●

variable
  e  e₁  e₂  : Term κ ★
  e' e₁' e₂' : Term κ ★
  v  v₁  v₂  : Term κ K

-- Kits ------------------------------------------------------------------------

`_  : k ∈ κ → Term κ (k→K k)
`_ {k = ★} = `ᵉ_
`_ {k = ■} = `ᵗ_

open import KitTheory.Everything VKind TKind k→K Term `_ public

open Kit {{...}} public
open KitTraversal {{...}} public

instance traversal : KitTraversal
KitTraversal._⋯_ traversal (`ᵉ x)    f = tm' (f _ x)
KitTraversal._⋯_ traversal (`ᵗ x)    f = tm' (f _ x)
KitTraversal._⋯_ traversal (λ→ t)    f = λ→ (t ⋯ (f ↑ ★))
KitTraversal._⋯_ traversal (Λ→ t)    f = Λ→ (t ⋯ (f ↑ ■))
KitTraversal._⋯_ traversal (∀→ t)    f = ∀→ (t ⋯ (f ↑ ■))
KitTraversal._⋯_ traversal (t₁ · t₂) f = (t₁ ⋯ f) · (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ∙ t₂) f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
KitTraversal._⋯_ traversal (t₁ ⇒ t₂) f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
KitTraversal._⋯_ traversal [★]       f = [★]
KitTraversal.⋯-var traversal {k = ★} x f = refl
KitTraversal.⋯-var traversal {k = ■} x f = refl

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

open AssocAssumptions {{...}} public
open KitCompose {{...}} public

instance ckit : KitCompose {{traversal}}
KitCompose.⋯-assoc ckit (`ᵉ x) f g =
  tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  tm' ((g ∘ₖ f) _ x) ∎
KitCompose.⋯-assoc ckit (`ᵗ x) f g =
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
KitCompose.⋯-assoc ckit [★]       f g = refl

instance AAᵣᵣ = AssocAssumptionsᵣᵣ
instance AAᵣₛ = AssocAssumptionsᵣₛ
instance AAₛᵣ = AssocAssumptionsₛᵣ
instance AAₛₛ = AssocAssumptionsₛₛ

Type : List VKind → TKind → Set
Type κ K = Term κ (↑ₖ K)

_∶⊢_ : List VKind → TKind → Set
_∶⊢_ = Type

variable
  t  t₁  t₂  : Type κ ★
  t' t₁' t₂' : Type κ ★
  T  T₁  T₂  : Type κ K

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

wk-drop-∈ : (x : k ∈ κ) → Type (drop-∈ x κ) (k→K k) → Type κ (k→K k)
wk-drop-∈ (here _)  t = wk _ t
wk-drop-∈ (there x) t = wk _ (wk-drop-∈ x t)

Ctx : List VKind → Set
Ctx κ = ∀ {k} → (x : κ ∋ k) → Type (drop-∈ x κ) (k→K k)

-- Our context is defined as a telescope.
-- This function automatically weakens all the types in a `Ctx κ` such that they
-- refer to `κ` instead of a `κ`-suffix.
wk-telescope : Ctx κ → k ∈ κ → Type κ (k→K k)
wk-telescope Γ x = wk-drop-∈ x (Γ x)

variable
  Γ Γ₁ Γ₂ : Ctx κ

_,,_ : Ctx κ → Type κ (k→K k) → Ctx (k ∷ κ)
(Γ ,, t) (here refl) = t
(Γ ,, t) (there x) = Γ x

data _⊢_∶_ : Ctx κ → Term κ K → Type κ K → Set where
  τ-` : ∀ {Γ : Ctx κ} {t : Type κ ★} {x : ★ ∈ κ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx κ} →
    Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
    Γ ⊢ λ→ e ∶ t₁ ⇒ t₂
  τ-Λ :
    Γ ,, [★] ⊢ e ∶ t₂ →
    Γ ⊢ Λ→ e ∶ ∀→ t₂
  τ-· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  τ-∙ : ∀ {Γ : Ctx κ} →
    Γ ⊢ e ∶ ∀→ t₂ →
    Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
  τ-★ :
    Γ ⊢ t ∶ [★]
  τ-[★] :
    Γ ⊢ [★] ∶ [★]

_⊢*_∶_ : Ctx κ₂ → κ₁ →ₛ κ₂ → Ctx κ₁ → Set
_⊢*_∶_ {κ₁ = κ₁} Γ₂ σ Γ₁ = ∀ {k₁} → (x : κ₁ ∋ k₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

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
