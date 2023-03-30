module Kitty.Examples.LambdaPi-Derive.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Modes using (Modes)
open import Data.List.Relation.Unary.Any using (here; there) public

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _↪β_  _↪*_  _≣_  _⊢_∶_
infixr  5  λx_  ∀[x∶_]_
-- infixr  6  _⇒_
infixl  6  _·_
infix   7  `_

-- Modes -----------------------------------------------------------------------

-- Variable and Term Modes
data Mode : Set where
  𝕖 : Mode  -- Expression-level variables

-- Mapping variable modes to the term modes they represent.
m→M : Mode → Mode
m→M m = m

𝕄 : Modes
𝕄 = record { VarMode = Mode ; TermMode = Mode ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Mode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Mode
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Mode → Mode → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m→M m
  λx_       : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀[x∶_]_   : µ ⊢ 𝕖  →  µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  ★         : µ ⊢ 𝕖

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕖
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ M

-- Deriving Renaming/Substitution and related lemmas.
open import Kitty.Derive using (derive; module Derived)

unquoteDecl D = derive 𝕄 _⊢_ D

open Derived.Functional D public

-- Types and Contexts ----------------------------------------------------------

open import Kitty.Typing.Types terms

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { m → m } }

open KitType kit-type public

open import Kitty.Typing.OPE compose-traversal kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ M → Set where
    `_     : ∀ (x : µ ∋ m) → Neutral (` x)
    _·_    : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)

  data Value : µ ⊢ M → Set where
    λx_     : ∀ {e : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value e
              → Value (λx e)
    ∀[x∶_]_ : ∀ {t₁ : µ ⊢ 𝕖} {t₂ : (µ ▷ 𝕖) ⊢ 𝕖}
              → Value t₁
              → Value t₂
              → Value (∀[x∶ t₁ ] t₂)
    ★       : Value {µ} ★
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ M → µ ⊢ M → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆ₛ
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-∀₁ :
    t₁ ↪ t₁' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂
  ξ-∀₂ :
    t₂ ↪ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁ ] t₂'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'

-- data _↪β_ : µ ⊢ M → µ ⊢ M → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪β e₁ ⋯ ⦅ e₂ ⦆ₛ

-- -- Closes `R` under term congruency. Can be derived!
-- data Cong (R : ∀ {µ M} → µ ⊢ M → µ ⊢ M → Set) : µ ⊢ M → µ ⊢ M → Set where 
--   ξ-R :
--     R e e' →
--     Cong R e e'
--   ξ-λ :
--     Cong R e e' →
--     Cong R (λx e) (λx e')
--   ξ-∀₁ :
--     Cong R t₁ t₁' →
--     Cong R (∀[x∶ t₁ ] t₂) (∀[x∶ t₁' ] t₂)
--   ξ-∀₂ :
--     Cong R t₂ t₂' →
--     Cong R (∀[x∶ t₁ ] t₂) (∀[x∶ t₁ ] t₂')
--   ξ-·₁ :
--     Cong R e₁ e₁' →
--     Cong R (e₁ · e₂) (e₁' · e₂)
--   ξ-·₂ :
--     Cong R e₂ e₂' →
--     Cong R (e₁ · e₂) (e₁ · e₂')
--   -- Alternative: more concise, but not suitable for small-step. We can derive two Closures!
--   -- ξ-· :
--   --   Cong R e₁ e₁' →
--   --   Cong R e₂ e₂' →
--   --   Cong R (e₁ · e₂) (e₁' · e₂')

-- _↪'_ : µ ⊢ M → µ ⊢ M → Set
-- _↪'_ = Cong (_↪β_)

-- -- _↪*'_ : µ ⊢ M → µ ⊢ M → Set
-- -- _↪*'_ = ReflTrans (Cong (_↪β_))

-- -- _≣'_ : µ ⊢ M → µ ⊢ M → Set
-- -- _≣'_ = ReflTrans (Sym (Cong (_↪β_)))
  
-- module Test where
--   open import Kitty.Examples.LambdaPi-Derive.Closures
--   open SymmetricClosure₂ {C = _⊢_} _↪_ renaming (Sym to _≣_)

--   ≣-sym : e₁ ≣ e₂ → e₂ ≣ e₁
--   ≣-sym = sym

--   ≣-f :
--     ∀ {µ} {µ'} {M} {M'}
--       {f : µ ⊢ M → µ' ⊢ M'}
--       (F : ∀ {e e' : µ ⊢ M} → e ↪ e' → f e ↪ f e')
--       {e e' : µ ⊢ M}
--     → e ≣ e'
--     → f e ≣ f e'
--   ≣-f = map-Sym

data _≣_ : µ ⊢ M → µ ⊢ M → Set where
  ≣-refl : e ≣ e
  ≣-step-↪ : e₁ ↪ e₂ → e₂ ≣ e₃ → e₁ ≣ e₃
  ≣-step-↩ : e₂ ↪ e₁ → e₂ ≣ e₃ → e₁ ≣ e₃

≣-trans : e₁ ≣ e₂ → e₂ ≣ e₃ → e₁ ≣ e₃
≣-trans ≣-refl        e₂≣e₃ = e₂≣e₃
≣-trans {e₂ = e₃} {e₃ = e₄} (≣-step-↪ e₁↪e₂ e₂≣e₃) e₃≣e₄ = ≣-step-↪ e₁↪e₂ (≣-trans e₂≣e₃ e₃≣e₄)
≣-trans {e₂ = e₃} {e₃ = e₄} (≣-step-↩ e₂↪e₁ e₂≣e₃) e₃≣e₄ = ≣-step-↩ e₂↪e₁ (≣-trans e₂≣e₃ e₃≣e₄)

≣-sym : e₁ ≣ e₂ → e₂ ≣ e₁
≣-sym ≣-refl                           = ≣-refl
≣-sym {e₂ = e₃} (≣-step-↪ e₁↪e₂ e₂≣e₃) = ≣-trans (≣-sym e₂≣e₃) (≣-step-↩ e₁↪e₂ ≣-refl)
≣-sym {e₂ = e₃} (≣-step-↩ e₂↪e₁ e₂≣e₃) = ≣-trans (≣-sym e₂≣e₃) (≣-step-↪ e₂↪e₁ ≣-refl)

≣-f :
  ∀ {µ} {µ'} {M}
    {f : µ ⊢ M → µ' ⊢ M}
    (F : ∀ {e e' : µ ⊢ M} → e ↪ e' → f e ↪ f e')
    {e e' : µ ⊢ M}
  → e ≣ e'
  → f e ≣ f e'
≣-f F ≣-refl = ≣-refl
≣-f F {e' = e''} (≣-step-↪ e↪e' e'≣e'') = ≣-step-↪ (F e↪e') (≣-f F e'≣e'')
≣-f F {e' = e''} (≣-step-↩ e'↪e e'≣e'') = ≣-step-↩ (F e'↪e) (≣-f F e'≣e'')

≣-↪ : e ↪ e' → e ≣ e'
≣-↪ e↪e' = ≣-step-↪ e↪e' ≣-refl

≣-↩ : e' ↪ e → e ≣ e'
≣-↩ e'↪e = ≣-step-↩ e'↪e ≣-refl

≣-λ : e ≣ e' → λx e ≣ λx e'
≣-λ = ≣-f ξ-λ

≣-·₁ : e₁ ≣ e₁' → e₁ · e₂ ≣ e₁' · e₂
≣-·₁ = ≣-f ξ-·₁

≣-·₂ : e₂ ≣ e₂' → e₁ · e₂ ≣ e₁ · e₂'
≣-·₂ = ≣-f ξ-·₂

≣-∀₁ : e₁ ≣ e₁' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁' ] e₂
≣-∀₁ = ≣-f ξ-∀₁

≣-∀₂ : e₂ ≣ e₂' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁ ] e₂'
≣-∀₂ = ≣-f ξ-∀₂

data _↪*_ : µ ⊢ M → µ ⊢ M → Set where
  refl :
    ∀ {t : µ ⊢ 𝕖}
    → t ↪* t
  step :
    ∀ {t : µ ⊢ 𝕖}
    → t₁ ↪  t₂
    → t₂ ↪* t₃
    → t₁ ↪* t₃

data _⇓_ (e₁ e₂ : µ ⊢ M) : Set where
  ⇓[_,_] :
      e₁ ↪* e₂  
    → Value e₂
    → e₁ ⇓ e₂

-- Type System -----------------------------------------------------------------

data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
  ⊢` : ∀ {x : µ ∋ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ :
    Γ ⊢ t₁ ∶ ★ →
    Γ ▶ t₁ ⊢ e ∶ t₂ →
    Γ ⊢ λx e ∶ ∀[x∶ t₁ ] t₂
  ⊢∀ :
    Γ ⊢ t₁ ∶ ★ →
    Γ ▶ t₁ ⊢ t₂ ∶ ★ →
    Γ ⊢ ∀[x∶ t₁ ] t₂ ∶ ★
  ⊢· :
    Γ ⊢ e₁ ∶ ∀[x∶ t₁ ] t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ
  ⊢★ :
    Γ ⊢ ★ ∶ ★
  -- ⊢↪ :
  --   t ↪ t' →
  --   Γ ⊢ e ∶ t →
  --   Γ ⊢ e ∶ t'
  ⊢≣ :
    t ≣ t' →
    Γ ⊢ e ∶ t →
    Γ ⊢ e ∶ t'

-- Values : Ctx µ → Set
-- Values {µ} Γ = ∀ {m} (x : µ ∋ m) → Value (Γ x) 

-- Values-ext : ∀ {Γ : Ctx µ} → Values Γ → Value t → Values (Γ ▶ t)
-- Values-ext {µ} VΓ Vt (here refl) = Vt
-- Values-ext {µ} VΓ Vt (there x) = VΓ x

-- postulate
--   Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- Value-wk-telescope : Value (Γ x) → Value (wk-telescope Γ x)
-- -- Value-wk-telescope {x = here refl} VΓx = {!VΓx!}
-- -- Value-wk-telescope {x = there x} VΓx = {!!}

-- ⊢-Value :
--   ∀ {µ} {Γ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M}
--   → Values Γ
--   → Γ ⊢ e ∶ t
--   → Value t
-- ⊢-Value {Γ = Γ} VΓ (⊢` {x = x} refl) = Value-wk-telescope {Γ = Γ} (VΓ x)
-- ⊢-Value VΓ (⊢λ Vt₁ ⊢e₁ ⊢e₂)          = ∀[x∶ Vt₁ ] ⊢-Value (Values-ext VΓ Vt₁) ⊢e₂
-- ⊢-Value VΓ (⊢∀ t₁⇓t₁' ⊢t₁ ⊢t₂)       = ★
-- ⊢-Value VΓ (⊢· ⊢e₁ ⊢e₂ ⇓[ _ , Vt ])  = Vt
-- ⊢-Value VΓ ⊢★                        = ★
