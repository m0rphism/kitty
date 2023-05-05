module Kitty.Examples.MutRef-Derive.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_; _▷▷_) public
open import Kitty.Term.Modes using (Modes)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  -- 𝕤 : Modeₜ  -- States
  -- 𝕡 : Modeₜ  -- Programs

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
  λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _⇒_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥

  new       : µ ⊢ 𝕖  →  µ ⊢ 𝕖
  *_        : µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _≔_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  Ref       : µ ⊢ 𝕥  →  µ ⊢ 𝕥

  `tt       : µ ⊢ 𝕖
  `⊤        : µ ⊢ 𝕥

  -- []        : µ ⊢ 𝕤
  -- _∷_       : µ ⊢ 𝕖  →  µ ⊢ 𝕤  →  µ ⊢ 𝕤

  -- ⟨_,_⟩     : µ ⊢ 𝕤  →  µ ⊢ 𝕖  →  µ ⊢ 𝕡

  -- ⟨_,_⟩     : µ →ₛ µ  →  µ ⊢ 𝕖  →  µ ⊢ 𝕡

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)

unquoteDecl D = derive 𝕄 _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.TypeModes terms

-- Each variable mode corresponds to a term mode that represents its type.
type-modes : TypeModes
type-modes = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

open TypeModes type-modes public

open import Kitty.Typing.CtxRepr type-modes

ctx-repr : CtxRepr
ctx-repr = Functional-CtxRepr

open CtxRepr ctx-repr public

open import Kitty.Typing.OPE compose-traversal type-modes ctx-repr public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  ⊢` : ∀ {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ :
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkₖ _ id →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢new :
    Γ ⊢ e ∶ t →
    Γ ⊢ new e ∶ Ref t
  ⊢get :
    Γ ⊢ e ∶ Ref t →
    Γ ⊢ * e ∶ t
  ⊢≔ :
    Γ ⊢ e₁ ∶ Ref t →
    Γ ⊢ e₂ ∶ t →
    Γ ⊢ (e₁ ≔ e₂) ∶ t

open import Kitty.Typing.ITerms compose-traversal ctx-repr

≡ᶜ-cong-⊢ : ∀ {µ M} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} → 
  Γ₁ ≡ᶜ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ e ∶ t
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢` {x = x} ∋x) = ⊢` (≡ᶜ-cong-∋ x Γ₁≡Γ₂ ∋x)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢λ ⊢e)         = ⊢λ (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶ Γ₁≡Γ₂ refl) ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢· ⊢e₁ ⊢e₂)    = ⊢· (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢new ⊢e)       = ⊢new (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢get ⊢e)       = ⊢get (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢≔ ⊢e₁ ⊢e₂)    = ⊢≔ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = ≡ᶜ-cong-⊢ }

open ITerms iterms hiding (_⊢_∶_; ⊢`; ≡ᶜ-cong-⊢) public
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.List.Properties using (++-identityʳ)

MapRef : Ctx µ → Ctx µ
MapRef Σ 𝕖 x = Ref (Σ _ x)

wk*' : ∀ {M} µ → [] ⊢ M → µ ⊢ M
wk*' µ t = subst (_⊢ _) (++-identityʳ µ) (wk* µ t)

-- open import Data.List.Relation.Unary.Any using (here; there)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; module ≡-Reasoning)
-- open ≡-Reasoning

-- MapRef-∋x : {Σ : Ctx µ} {x : µ ∋ 𝕖} {t : µ ⊢ 𝕥}
--   → MapRef Σ ∋ x ∶ Ref t
--   → Σ ∋ x ∶ t
-- MapRef-∋x {x = here refl} refl = refl
-- MapRef-∋x {Σ = Σ} {x = there x} {t} ∋x =
--   let Σ' = λ {m} x → Σ {m} (there x) in
--   let tmp = MapRef-∋x {Σ = Σ'} {x} {!!} in
--   wk-telescope Σ (there x) ≡⟨ ope-pres-telescope x (ope-drop {Γ₁ = Σ'} ope-id) ⟩
--   wk-telescope Σ' x ⋯ᵣ wknᵣ ≡⟨ {!!} ⟩
--   t                        ∎

data _⊢⟨_,_⟩∶_ : Ctx µ → µ →ₛ µ → µ ⊢ M → [] ∶⊢ M → Set where
  ⊢⟨⟩ : ∀ {Σ : Ctx µ} {σ : µ →ₛ µ} {e : µ ⊢ 𝕖} {t : [] ⊢ 𝕥} →
    Σ ⊢* σ ∶ Σ →
    MapRef Σ ⊢ e ∶ wk*' µ t →
    Σ ⊢⟨ σ , e ⟩∶ t

-- Semantics -------------------------------------------------------------------

mutual
  data Value : µ ⊢ M → Set where
    λx_     : ∀ (e : (µ ▷ 𝕖) ⊢ 𝕖) → Value (λx e)
    new     : ∀ (e : µ ⊢ 𝕖) → Value e → Value (new e)

data ⟨_,_⟩↪⟨_,_⟩ : µ₁ →ₛ µ₁ → µ₁ ⊢ M → µ₂ →ₛ µ₂ → µ₂ ⊢ M → Set where
  β-λ : ∀ {σ : µ →ₛ µ} {e₂ : µ ⊢ 𝕖} →
    ⟨ σ , (λx e₁) · e₂ ⟩↪⟨ σ , e₁ ⋯ ⦅ e₂ ⦆ₛ ⟩
  β-new : ∀ {σ : µ →ₛ µ} {e : µ ⊢ 𝕖} →
    ⟨ σ , new e ⟩↪⟨ wkₖ 𝕖 (σ ,ₛ e) , # 0 ⟩
  β-* : ∀ {σ : µ →ₛ µ} {x : µ ∋ 𝕖} →
    ⟨ σ , * (` x) ⟩↪⟨ σ , x & σ ⟩
  β-≔ : ∀ {σ : µ →ₛ µ} {x : µ ∋ 𝕖} →
    ⟨ σ , (` x) ≔ e ⟩↪⟨ σ , `tt ⟩ -- TODO
  ξ-·₁ : ∀ {σ : µ →ₛ µ} →
    ⟨ σ , e₁      ⟩↪⟨ σ , e₁'      ⟩ →
    ⟨ σ , e₁ · e₂ ⟩↪⟨ σ , e₁' · e₂ ⟩
  ξ-·₂ : ∀ {σ : µ →ₛ µ} →
    ⟨ σ ,      e₂ ⟩↪⟨ σ ,      e₂' ⟩ →
    ⟨ σ , e₁ · e₂ ⟩↪⟨ σ , e₁ · e₂' ⟩

  -- Not possible to reduce under binders with this architecture.
  -- Actually, it might be possible if we allow the `e`s to have µ ▷▷ µ'.
  -- ξ-λ : ∀ {σ : µ →ₛ µ} {e e' : (µ ▷ 𝕖) ⊢ 𝕖} →
  --   ⟨ σ ,    e ⟩↪⟨ σ ,    e' ⟩ →
  --   ⟨ σ , λx e ⟩↪⟨ σ , λx e' ⟩
