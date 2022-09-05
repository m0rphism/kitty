module Examples.ISession.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import KitTheory.Prelude using (_∋_; _▷_; _▷▷_) public
open import KitTheory.Modes using (Modes; Terms)

-- Fixities --------------------------------------------------------------------

-- infix   3  _⊢_  _↪_  _⊢_∶_  _⊢*_∶_
infixr  5  ∀α[_]→_  λx→_  Λα→_ λα→_
infixr  6  _⇒_
infixl  6  _·_  _∙_ _·ᵗ_
infix   7  `_  `ᵗ_  `ᵛ_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕧 : Modeᵥ  -- Expression Variables
  𝕥 : Modeᵥ  -- Type Variables

-- Term Modes
data Modeₜ : Set where
  𝕔 : Modeₜ  -- Configurations
  𝕖 : Modeₜ  -- Expressions
  𝕧 : Modeₜ  -- Values
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds
  𝕤 : Modeₜ  -- Sorts

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂ µ''       : List Modeᵥ
  x x₁ x₂ x' x₁' x₂'        : 𝕧 ∈ µ
  α α₁ α₂ α' α₁' α₂'        : 𝕥 ∈ µ
  X Y Z                     : m ∈ µ

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕧 = 𝕧
m→M 𝕥 = 𝕥

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

-- Syntax ----------------------------------------------------------------------

data Label : Set where
  [0] [1] : Label

mutual
  -- Expressions, Types, and Kinds
  data Term : List Modeᵥ → Modeₜ → Set where
    -- Configurations
    ⟨_⟩      : Term µ 𝕖 → Term µ 𝕔
    _∥_      : Term µ 𝕔 → Term µ 𝕔 → Term µ 𝕔
    ν[α,x]→_ : Term (µ ▷ 𝕥 ▷ 𝕧) 𝕔 → Term µ 𝕔

    -- Expressions
    ⟨_⟩ᵥ         : Term µ 𝕧 → Term µ 𝕖
    let[x=_]in_  : Term µ 𝕖 → Term (µ ▷▷ µ' ▷ 𝕧) 𝕖 → Term µ 𝕖
    fork         : Term µ 𝕖 → Term µ 𝕖
    _·_          : Term µ 𝕧 → Term µ 𝕧 → Term µ 𝕖
    send_on_     : Term µ 𝕧 → Term µ 𝕧 → Term µ 𝕖
    recv         : Term µ 𝕧 → Term µ 𝕖
    select_on_   : Label → Term µ 𝕧 → Term µ 𝕖
    case_of[_,_] : Term µ 𝕧 → Term µ 𝕖 → Term µ 𝕖 → Term µ 𝕖
    close        : Term µ 𝕧 → Term µ 𝕖
    π            : Label → Term µ 𝕧 → Term µ 𝕖
    _∙_          : Term µ 𝕧 → Term µ 𝕥 → Term µ 𝕖

    -- Values
    `ᵛ_   : µ ∋ 𝕧 → Term µ 𝕧
    λx→_  : Term (µ ▷ 𝕧) 𝕖 → Term µ 𝕧
    Λα→_  : Term (µ ▷ 𝕥 ▷ 𝕧) 𝕧 → Term µ 𝕧
    unit  : Term µ 𝕧
    _,ᵉ_ : Term µ 𝕧 → Term µ 𝕧 → Term µ 𝕧

    -- Kinds
    Type    : Term µ 𝕜
    Session : Term µ 𝕜
    State   : Term µ 𝕜
    Shape   : Term µ 𝕜
    Dom     : Term µ 𝕥 → Term µ 𝕜
    Cstr    : Term µ 𝕜
    _⇒_     : Term µ 𝕜 → Term µ 𝕜 → Term µ 𝕜

    -- Sorts
    Kind : Term µ 𝕤

    -- Types
    `ᵗ_   : µ ∋ 𝕥 → Term µ 𝕥
    _·ᵗ_  : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    λα→_  : Term (µ ▷ 𝕥) 𝕥 → Term µ 𝕥

    --   Expression Types
    ∀α[_]→_       : Term (µ ▷ 𝕥) 𝕥 → Term (µ ▷ 𝕥 ▷ 𝕧) 𝕥 → Term µ 𝕥
    ⟨_;_–→∃_;_;_⟩ : Term µ 𝕥 → Term µ 𝕥 → Ctx'' µ µ' → Term (µ ▷▷ µ') 𝕥 → Term (µ ▷▷ µ') 𝕥 → Term µ 𝕥
    Chan          : Term µ 𝕥 → Term µ 𝕥
    Unit          : Term µ 𝕥
    _×_           : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥

    --   Session Types
    ![∃α→_;_]_ : Term (µ ▷ 𝕥) 𝕥 → Term (µ ▷ 𝕥) 𝕥 → Term µ 𝕥 → Term µ 𝕥
    ?[∃α→_;_]_ : Term (µ ▷ 𝕥) 𝕥 → Term (µ ▷ 𝕥) 𝕥 → Term µ 𝕥 → Term µ 𝕥
    _⊕_        : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    _&_        : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    End        : Term µ 𝕥
    Dual       : Term µ 𝕥 → Term µ 𝕥

    --   Shape Types
    [1]  : Term µ 𝕥
    _+_  : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥

    --   Domain Types
    _,ᵈ_ : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    πᵈ   : Label → Term µ 𝕥 → Term µ 𝕥

    --   Session State Types
    []    : Term µ 𝕥
    _∶_   : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    _∶♯_  : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    _,ˢ_  : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥

    --   Constraint Types
    True  : Term µ 𝕥
    _∧_   : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
    _#_   : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥

  `_ : µ ∋ m → Term µ (m→M m)
  `_ {m = 𝕧} = `ᵛ_
  `_ {m = 𝕥} = `ᵗ_

  𝕋 : Terms 𝕄
  𝕋 = record { _⊢_ = Term ; `_ = `_ }

  open Terms 𝕋 using (_⊢_) public

  open import KitTheory.Types 𝕋 public

  -- Each variable mode corresponds to a term mode that represents its type.
  kit-type : KitType
  kit-type = record { ↑ₜ = λ { 𝕔 → 𝕥 ; 𝕧 → 𝕥 ; 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕤 ; 𝕤 → 𝕤 } }

  open KitType kit-type public

  variable
    Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' : Ctx µ
    τ τ₁ τ₂ τ₃ τ' τ₁' τ₂' : µ ∶⊢ M

data EvalCtx : List Modeᵥ → Modeₜ → List Modeᵥ → Modeₜ → Set where
  -- Hole
  □           : EvalCtx µ M µ M

  -- Expressions
  let[x=_]in_ : EvalCtx µ 𝕖 µ' 𝕖 → Term (µ ▷ 𝕧) 𝕖 → EvalCtx µ 𝕖 µ' 𝕖

  -- Configurations
  _∥_         : EvalCtx µ 𝕔 µ' 𝕔 → Term µ 𝕔 → EvalCtx µ 𝕔 µ' 𝕔
  ν[α,x]→_    : EvalCtx (µ ▷ 𝕥 ▷ 𝕧) 𝕔 µ' 𝕔 → EvalCtx µ 𝕔 µ' 𝕔

_[_] : EvalCtx µ M µ' M' → Term µ' M' → Term µ M
□                [ t ] = t
(let[x= E ]in e) [ t ] = let[x= E [ t ] ]in e
(E ∥ C)          [ t ] = (E [ t ]) ∥ C
(ν[α,x]→ E)      [ t ] = ν[α,x]→ (E [ t ])

variable
  C C₁ C₂ C₃ C' C₁' C₂' C₁₁ C₁₂ C₂₁ C₂₂ : Term µ 𝕔
  ℂ ℂ₁ ℂ₂ ℂ₃ ℂ' ℂ₁' ℂ₂' ℂ₁₁ ℂ₁₂ ℂ₂₁ ℂ₂₂ : Term µ 𝕥
  T T₁ T₂ T₃ T' T₁' T₂' T₁₁ T₁₂ T₂₁ T₂₂ : Term µ 𝕥
  Σ Σ₁ Σ₂ Σ₃ Σ' Σ₁' Σ₂' Σ₁₁ Σ₁₂ Σ₂₁ Σ₂₂ : Term µ 𝕥
  N N₁ N₂ N₃ N' N₁' N₂' N₁₁ N₁₂ N₂₁ N₂₂ : Term µ 𝕥
  d d₁ d₂ d₃ d' d₁' d₂' d₁₁ d₁₂ d₂₁ d₂₂ : Term µ 𝕥
  S S₁ S₂ S₃ S' S₁' S₂' S₁₁ S₁₂ S₂₁ S₂₂ : Term µ 𝕥
  e e₁ e₂ e₃ e' e₁' e₂' e₁₁ e₁₂ e₂₁ e₂₂ : Term µ 𝕖
  v v₁ v₂ v₃ v' v₁' v₂' v₁₁ v₁₂ v₂₁ v₂₂ : Term µ 𝕧
  k k₁ k₂ k₃ k' k₁' k₂' k₁₁ k₁₂ k₂₁ k₂₂ : Term µ 𝕜
  s s₁ s₂ s₃ s' s₁' s₂' s₁₁ s₁₂ s₂₁ s₂₂ : Term µ 𝕤
  t t₁ t₂ t₃ t' t₁' t₂' t₁₁ t₁₂ t₂₁ t₂₂ : Term µ M

-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ 𝕖 → Set where
--     `x  : Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
--     _∙t : Neutral e → Neutral (e ∙ t)

--   data Value : µ ⊢ 𝕖 → Set where
--     λx_     : Value e → Value (λx e)
--     Λα_     : Value e → Value (Λα e)
--     neutral : Neutral e → Value e

-- data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
--   β-Λ : ∀ {t : µ ⊢ 𝕥} →
--     (Λα e) ∙ t ↪ e ⋯ ⦅ t ⦆
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
--   ξ-∙ :
--     e ↪ e' →
--     e ∙ t ↪ e' ∙ t
