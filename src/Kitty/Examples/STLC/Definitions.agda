-- {-# OPTIONS --rewriting #-}

module Kitty.Examples.STLC.Definitions where

-- open import Data.List using (List; [])
-- open import Relation.Binary.PropositionalEquality using (_≡_)

-- open import Kitty.Prelude using (_∋_; _▷_) public
-- open import Kitty.Modes using (Modes; Terms)
-- open import Kitty.Derive using (deriveIso)
-- open import Kitty.Generics using (module FromIso)

-- -- Fixities --------------------------------------------------------------------

-- infix   3  _⊢_  _↪_  _⊢_∶_  _⊢*_∶_
-- infixr  5  λx_
-- infixr  6  _⇒_
-- infixl  6  _·_
-- infix   7  `_

-- -- Modes -----------------------------------------------------------------------

-- -- Variable Modes
-- data Modeᵥ : Set where
--   𝕖 : Modeᵥ  -- Expression-level variables

-- -- Term Modes
-- data Modeₜ : Set where
--   𝕖 : Modeₜ  -- Expressions
--   𝕥 : Modeₜ  -- Types

-- -- Mapping variable modes to the term modes they represent.
-- m→M : Modeᵥ → Modeₜ
-- m→M 𝕖 = 𝕖

-- 𝕄 : Modes
-- 𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

-- variable
--   m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
--   M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
--   µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
--   x y z                     : µ ∋ 𝕖

-- -- Syntax ----------------------------------------------------------------------

-- -- Expressions and Types
-- data _⊢_ : List Modeᵥ → Modeₜ → Set where
--   `_    : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
--   λx_   : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
--   _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
--   _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
--   𝟘     : µ ⊢ 𝕥

-- variable
--   e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
--   t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
--   E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- open import Kitty.Derive

-- unquoteDecl desc    = deriveDesc   (quote 𝕄) (quote _⊢_) desc
-- unquoteDecl to      = deriveTo     (quote 𝕄) (quote _⊢_) (quote desc) to
-- unquoteDecl from    = deriveFrom   (quote 𝕄) (quote _⊢_) (quote desc) from
-- unquoteDecl from∘to = deriveFromTo (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) from∘to
-- unquoteDecl to∘from = deriveToFrom (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) to∘from

-- open import Kitty.Iso
-- open import Agda.Builtin.Equality.Rewrite
-- open import Kitty.Generics

-- {-# REWRITE from∘to #-}
-- {-# REWRITE to∘from #-}

-- -- unquoteDecl iso' = deriveIso 𝕄 _⊢_ iso'

-- iso' : ∀ {µ M} → (µ ⊢ M) ≃ (Tm 𝕄 desc µ M)
-- iso' = iso to from from∘to to∘from

-- open FromIso 𝕄 iso' public


-- -- Types and Contexts ----------------------------------------------------------

-- open import Kitty.Types terms

-- -- Each variable mode corresponds to a term mode that represents its type.
-- kit-type : KitType
-- kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

-- open KitType kit-type public

-- open import Kitty.OPE terms kit-traversal kit-assoc kit-assoc-lemmas kit-type public

-- variable
--   Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
--   T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- -- Type System -----------------------------------------------------------------

-- data _⊢_∶_ : Ctx µ → µ ⊢ 𝕖 → µ ∶⊢ 𝕖 → Set where
--   τ-` :
--     wk-telescope Γ x ≡ t →
--     Γ ⊢ ` x ∶ t
--   τ-λ : {Γ : Ctx µ} →
--     Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkᵣ →
--     Γ ⊢ λx e ∶ t₁ ⇒ t₂
--   τ-· :
--     Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--     Γ ⊢ e₂ ∶ t₁ →
--     Γ ⊢ e₁ · e₂ ∶ t₂

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ 𝕖 → Set where
--     `x  : Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

--   data Value : µ ⊢ 𝕖 → Set where
--     λxe     : Value (λx e)
--     neutral : Neutral e → Value e

-- data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     Value e₂ →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
--   -- ξ-λ :
--   --   e ↪ e' →
--   --   λx e ↪ λx e'
--   ξ-·₁ :
--     e₁ ↪ e₁' →
--     e₁ · e₂ ↪ e₁' · e₂
--   ξ-·₂ :
--     Value e₁ →
--     e₂ ↪ e₂' →
--     e₁ · e₂ ↪ e₁ · e₂'
