module Kitty.Examples.SystemF-Paper.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Kitty.Examples.SystemF-Paper.Kits
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- -- Modes -----------------------------------------------------------------------

data Mode : ModeTy → Set where
  𝕖 : Mode Var   -- Expressions
  𝕥 : Mode Var   -- Types
  𝕜 : Mode Term  -- Kinds

variable
  mt                        : ModeTy
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode mt
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List (Mode Var)
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List (Mode Var) → Mode mt → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m
  λx_       : (𝕖 ∷ µ) ⊢ 𝕖  →  µ ⊢ 𝕖
  Λα_       : (𝕥 ∷ µ) ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀[α∶_]_   : µ ⊢ 𝕜  →  (𝕥 ∷ µ) ⊢ 𝕥  →  µ ⊢ 𝕥
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _∙_       : µ ⊢ 𝕖  →  µ ⊢ 𝕥  →  µ ⊢ 𝕖
  _⇒_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  ★         : µ ⊢ 𝕜

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂' : µ ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ m

-- Substitution & Lemmas -------------------------------------------------------

terms : Terms
terms = record
  { Mode        = Mode
  ; _⊢_         = _⊢_
  ; `_          = `_
  ; `-injective = λ { refl → refl }
  }

open Terms terms hiding (Mode; _⊢_; `_)

_⋯_ :
  ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} 
  → µ₁ ⊢ m → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ m
(` x)          ⋯ ϕ = `/id (ϕ _ x)
(λx t)         ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(Λα t)         ⋯ ϕ = Λα (t ⋯ (ϕ ↑ 𝕥))
(∀[α∶ t₁ ] t₂) ⋯ ϕ = ∀[α∶ t₁ ⋯ ϕ ] (t₂ ⋯ (ϕ ↑ 𝕥))
(t₁ · t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ∙ t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
(t₁ ⇒ t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
★              ⋯ ϕ = ★

⋯-id :
  ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ} (t : µ ⊢ m)
  → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id (` x)          = id/`/id x
⋯-id (λx t)         = cong λx_ {!⋯-id t!}
⋯-id (Λα t)         = cong Λα_ {!!}
⋯-id (∀[α∶ t₁ ] t₂) = cong₂ ∀[α∶_]_ (⋯-id t₁) {!!}
⋯-id (t₁ · t₂)      = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ∙ t₂)      = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)      = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★              = refl

traversal : Traversal
traversal = record
  { _⋯_   = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id  = ⋯-id
  }

open Traversal traversal hiding (_⋯_; ⋯-id)

⋯-assoc :
  ∀ {_∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : Scoped}
    ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄
    ⦃ C : ComposeKit K₁ K₂ K ⦄
    {µ₁ µ₂ µ₃}
    (t : µ₁ ⊢ m) (ϕ₁ : µ₁ –[ K₁ ]→ µ₂) (ϕ₂ : µ₂ –[ K₂ ]→ µ₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₘ ϕ₂)
⋯-assoc (` x)          ϕ₁ ϕ₂ = {!!}
⋯-assoc (λx t)         ϕ₁ ϕ₂ = cong λx_ {!!}
⋯-assoc (Λα t)         ϕ₁ ϕ₂ = cong Λα_ {!!}
⋯-assoc (∀[α∶ t₁ ] t₂) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ {!!} {!!}
⋯-assoc (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ∙ t₂)      ϕ₁ ϕ₂ = cong₂ _∙_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc ★              ϕ₁ ϕ₂ = refl

compose-traversal : ComposeTraversal
compose-traversal = record { ⋯-assoc = ⋯-assoc }

open ComposeTraversal compose-traversal hiding (⋯-assoc)

types : Types
types = record { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 } }

-- -- Types and Contexts ----------------------------------------------------------

-- open import Kitty.Typing.TypeModes terms

-- -- Each variable mode corresponds to a term mode that represents its type.
-- type-modes : TypeModes
-- type-modes = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

-- open TypeModes type-modes public

-- open import Kitty.Typing.CtxRepr type-modes

-- ctx-repr : CtxRepr
-- ctx-repr = List-CtxRepr

-- open CtxRepr ctx-repr public

-- open import Kitty.Typing.OPE compose-traversal ctx-repr public

-- variable
--   Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
--   T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- -- Type System -----------------------------------------------------------------

-- data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
--   ⊢` : ∀ {x : µ ∋ m} →
--     Γ ∋ x ∶ T →
--     Γ ⊢ ` x ∶ T
--   ⊢λ : ∀ {e : µ ▷ 𝕖 ⊢ 𝕖} →
--     Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkₖ _ id →
--     Γ ⊢ λx e ∶ t₁ ⇒ t₂
--   ⊢Λ :
--     Γ ▶ k ⊢ e ∶ t₂ →
--     Γ ⊢ Λα e ∶ ∀[α∶ k ] t₂
--   ⊢· :
--     Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--     Γ ⊢ e₂ ∶ t₁ →
--     Γ ⊢ e₁ · e₂ ∶ t₂
--   ⊢∙ : {Γ : Ctx µ} →
--     Γ ▶ k₂ ⊢ t₁ ∶ k₁ →
--     Γ ⊢ t₂ ∶ k₂ →
--     Γ ⊢ e₁ ∶ ∀[α∶ k₂ ] t₁ →
--     Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆ₛ
--   ⊢τ :
--     Γ ⊢ t ∶ ★

-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ M → Set where
--     `[_]_  : ∀ (eq : m→M m ≡ M) (x : µ ∋ m) → Neutral (`[ eq ] x)
--     _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
--     _∙t    : Neutral e₁ → Neutral (e₁ ∙ t₂)

--   data Value : µ ⊢ M → Set where
--     λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
--     Λα_     : ∀ (e : (µ ▷ 𝕥) ⊢ 𝕖) → Value (Λα e)
--     neutral : Neutral e → Value e

-- pattern `ⁿ_ x = `[ refl ] x  

-- data _↪_ : µ ⊢ M → µ ⊢ M → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
--   β-Λ : ∀ {t₂ : µ ⊢ 𝕥} →
--     (Λα e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆ₛ
--   ξ-λ :
--     e ↪ e' →
--     λx e ↪ λx e'
--   ξ-Λ :
--     e ↪ e' →
--     Λα e ↪ Λα e'
--   ξ-·₁ :
--     e₁ ↪ e₁' →
--     e₁ · e₂ ↪ e₁' · e₂
--   ξ-·₂ :
--     e₂ ↪ e₂' →
--     e₁ · e₂ ↪ e₁ · e₂'
--   ξ-∙₁ :
--     e₁ ↪ e₁' →
--     e₁ ∙ t₂ ↪ e₁' ∙ t₂
