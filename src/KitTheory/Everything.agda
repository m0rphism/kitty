open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Everything
    (VarKind  : Set)
    (TermKind : Set)
    (k→K      : VarKind → TermKind)
    (_⊢_      : List VarKind → TermKind → Set)
    (`_       : ∀ {κ k} → k ∈ κ → κ ⊢ k→K k)
  where

open import KitTheory.Kit           VarKind TermKind k→K _⊢_ `_ public
open import KitTheory.Compose       VarKind TermKind k→K _⊢_ `_ public
open import KitTheory.ComposeLemmas VarKind TermKind k→K _⊢_ `_ public

--------------------------------------------------------------------------------

-- open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
-- open ≡-Reasoning
-- open import Data.List using (List; []; _∷_)
-- open import Data.List.Relation.Unary.Any using (here; there)
-- open import Axiom.Extensionality.Propositional using (Extensionality)
-- open import Function using (id)

-- open Kit {{...}}
-- open KitTraversal {{...}}
-- open AssocAssumptions {{...}}
-- open KitCompose {{...}}

-- private instance _ = kitᵣ
-- private instance _ = kitₛ
-- private instance _ = AssocAssumptionsᵣᵣ
-- private instance _ = AssocAssumptionsᵣₛ
-- private instance _ = AssocAssumptionsₛᵣ
-- private instance _ = AssocAssumptionsₛₛ

-- private
--   variable
--     k k' k₁ k₂    : VarKind
--     κ κ' κ₁ κ₂ κ₃ : List VarKind
--     K K' K₁ K₂    : TermKind
--     x y z         : k ∈ κ
--     ℓ ℓ₃          : Level
--     A B C         : Set ℓ

-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Data.Unit using (⊤; tt)

-- record KitType : Set₁ where
--   field
--     {{term-traversal}} : KitTraversal
--     _∶⊢_ : List VarKind → VarKind → Set
--     k→Kₜ : VarKind → TermKind
--     lift-type : (κ₁ ⊢ k→Kₜ k → κ₂ ⊢ k→Kₜ k) → κ₁ ∶⊢ k → κ₂ ∶⊢ k

--   _⋯ₜ_ : {{𝕂 : Kit}} → κ₁ ∶⊢ k → κ₁ –[ 𝕂 ]→ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜ_ T f = lift-type (_⋯ f) T

--   _⋯ₜₛ_ : κ₁ ∶⊢ k → κ₁ →ₛ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜₛ_ = _⋯ₜ_

--   _⋯ₜᵣ_ : κ₁ ∶⊢ k → κ₁ →ᵣ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜᵣ_ = _⋯ₜ_

--   wkₜ : κ ∶⊢ k → (k' ∷ κ) ∶⊢ k
--   wkₜ = _⋯ₜ wk

-- record KitType : Set₁ where
--   field
--     {{term-traversal}} : KitTraversal
--     TypeF     : VarKind → TermKind ⊎ Set

--   _∶⊢_ : List VarKind → VarKind → Set
--   κ ∶⊢ k with TypeF k
--   ...       | inj₁ K = κ ⊢ K
--   ...       | inj₂ A = A

--   _⋯ₜ_ : {{𝕂 : Kit}} → κ₁ ∶⊢ k → κ₁ –[ 𝕂 ]→ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜ_ {k = k} T f with TypeF k
--   ...                 | inj₁ x = T ⋯ f
--   ...                 | inj₂ y = T

--   _⋯ₜₛ_ : κ₁ ∶⊢ k → κ₁ →ₛ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜₛ_ = _⋯ₜ_

--   _⋯ₜᵣ_ : κ₁ ∶⊢ k → κ₁ →ᵣ κ₂ → κ₂ ∶⊢ k
--   _⋯ₜᵣ_ = _⋯ₜ_

--   wkₜ : κ ∶⊢ k → (k' ∷ κ) ∶⊢ k
--   wkₜ = _⋯ₜ wk
