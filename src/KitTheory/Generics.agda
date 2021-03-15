open import KitTheory.Modes

module KitTheory.Generics (𝕄 : Modes) where
-- module KitTheory.Generics where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Size

open Modes 𝕄

data Desc : Set₁ where
  `σ : (A : Set) → (A → Desc) → Desc
  `X : List VarMode → TermMode → Desc → Desc
  `■ : TermMode → Desc

Scoped : Set₁
Scoped = List VarMode → TermMode → Set

⟦_⟧ : Desc → Scoped → Scoped
⟦ `σ A d     ⟧ X µ M = Σ[ a ∈ A ] (⟦ d a ⟧ X µ M)
⟦ `X µ' M' d ⟧ X µ M = X (µ' ++ µ) M' × ⟦ d ⟧ X µ M
⟦ `■ M'      ⟧ X µ M = M ≡ M'

data Tm (d : Desc) : Scoped where
  `var : ∀ {µ m} → µ ∋ m → Tm d µ (m→M m)
  `con : ∀ {µ M} → ⟦ d ⟧ (Tm d) µ M → Tm d µ M

_⊢[_]_ : List VarMode → Desc → TermMode → Set
µ ⊢[ d ] M = Tm d µ M

-- -- module DescKit (d : Desc) where
-- module DescKit where

--   𝕋⟦⟧ : Desc → Terms 𝕄 → Terms 𝕄
--   𝕋⟦⟧ d t = record { _⊢_ = ⟦ d ⟧ (Terms._⊢_ t)
--                    ; `_ = {!!}
--                    }

--   𝕋 : Desc → Terms 𝕄
--   𝕋 d = record { _⊢_ = Tm d
--                ; `_ = `var
--                }

--   open import KitTheory.Kit
--   open Kit {{...}}

--   private

--     Traversal : Set → Set → Set₁
--     Traversal _⊢_ _⊢'_ = ∀ {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

--     -- trav : (d : Desc) → (_⊢'_ : Scoped) → KitTraversal 𝕋' → KitTraversal (𝕋⟦⟧ d 𝕋')

--     kit-traversal' : (d : Desc) → (𝕋' : Terms 𝕄) → KitTraversal 𝕋' → KitTraversal (𝕋⟦⟧ d 𝕋')
--     KitTraversal._⋯_ (kit-traversal' (`σ A dA)   𝕋' T') (a , t)  f = a , {!KitTraversal._⋯_ (kit-traversal' (dA a) 𝕋' T') t f!}
--     KitTraversal._⋯_ (kit-traversal' (`X µ' M d) 𝕋' T') (t' , t) f = {!KitTraversal._⋯_ T' t' (f ↑* µ')!}
--     KitTraversal._⋯_ (kit-traversal' (`■ x₁)     𝕋' T') refl     f = refl
--     KitTraversal.⋯-var (kit-traversal' d 𝕋' T') = {!!}

-- --     kit-traversal : (d : Desc) → KitTraversal (𝕋 d)
-- --     KitTraversal._⋯_ (kit-traversal d)            (`var x) f = {!x!}
-- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f with dA a
-- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , a₁ , x)) f    | `σ A₁ x₁    = {!x!}
-- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f    | `X x₁ x₂ xx = {!!}
-- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f    | `■ x₁       = {!!}
-- --     KitTraversal._⋯_ (kit-traversal (`X x₁ x₂ d)) (`con x) f = {!x!}
-- --     KitTraversal._⋯_ (kit-traversal (`■ x₁))      (`con x) f = {!x!}
-- --     KitTraversal.⋯-var (kit-traversal d) = {!!}
-- --     -- KitTraversal._⋯_ kit-traversal (`var x) f = tm' (f _ x)
-- --     -- KitTraversal._⋯_ kit-traversal (`con x) f = {!!}
-- --     -- KitTraversal.⋯-var kit-traversal x f = refl

-- -- --   -- kit-traversal : KitTraversal
-- -- --   -- KitTraversal._⋯_ kit-traversal (`var x) f = tm' (f _ x)
-- -- --   -- KitTraversal._⋯_ kit-traversal (`con x) f = {!!}
-- -- --   -- KitTraversal.⋯-var kit-traversal x f = refl

-- -- --   -- open import KitTheory.Kit           VarMode' TermMode' m→M' _⊢'_ `'_
-- -- --   -- open import KitTheory.Compose       VarMode' TermMode' m→M' _⊢'_ `'_
-- -- --   -- open import KitTheory.ComposeLemmas VarMode' TermMode' m→M' _⊢'_ `'_
-- -- --   -- open import KitTheory.Types         VarMode' TermMode' m→M' _⊢'_ `'_ public

-- -- --   -- open Kit {{...}} public
-- -- --   -- open KitTraversal {{...}} public

-- -- -- data Desc (I : Set) : Set₁ where
-- -- --   `σ : (A : Set) → (A → Desc I) → Desc I
-- -- --   `X : List I → I → Desc I → Desc I
-- -- --   `■ : I → Desc I

-- -- -- _−Scoped : Set → Set₁
-- -- -- I −Scoped = I → List I → Set

-- -- -- ⟦_⟧ : ∀ {I : Set} → Desc I → (List I → I −Scoped) → I −Scoped
-- -- -- ⟦ `σ A d   ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
-- -- -- ⟦ `X ∆ j d ⟧ X i Γ = X ∆ j Γ × ⟦ d ⟧ X i Γ
-- -- -- ⟦ `■ j     ⟧ X i Γ = i ≡ j

-- -- -- data Tm {I : Set} (d : Desc I) : Size → I −Scoped where
-- -- --   `var : ∀ {Γ i s} → Γ ∋ i → Tm d (↑ s) i Γ
-- -- --   `con : ∀ {Γ i s} → ⟦ d ⟧ (λ Δ i Γ → Tm d s i (Δ ++ Γ)) i Γ → Tm d (↑ s) i Γ

-- -- -- module Example where
-- -- --   open import Data.Unit
-- -- --   open import Data.Bool

-- -- --   data `UTLC : Set where
-- -- --     `app `abs : `UTLC

-- -- --   UTLC : Desc ⊤
-- -- --   UTLC = `σ `UTLC λ where
-- -- --     `app → `X [] tt (`X [] tt (`■ tt))
-- -- --     `abs → `X (tt ∷ []) tt (`■ tt)

-- -- --   UTLC-id : Tm UTLC ∞ tt []
-- -- --   UTLC-id = `con (`abs , `var (here refl) , refl)
