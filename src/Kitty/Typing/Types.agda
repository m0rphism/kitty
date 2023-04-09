open import Kitty.Term.Modes

module Kitty.Typing.Types {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude
open import Kitty.Util.List public

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level

record KitType : Set₁ where
  field
    ↑ₜ : TermMode → TermMode

  infix  3  _∶⊢_

  _∶⊢_ : List VarMode → TermMode → Set
  µ ∶⊢ M = µ ⊢ ↑ₜ M

-- open import Kitty.Term.Kit 𝕋
-- open import Kitty.Term.Traversal 𝕋
-- open import Kitty.Term.Sub 𝕋

-- module KitTypeSubst {ℓ} (KT : KitType) (𝕊 : SubWithLaws ℓ) (T : Traversal 𝕊) where
--   private instance _ = 𝕊

--   open KitType KT
--   open Traversal 𝕊 T
--   open Kit ⦃ … ⦄
--   open Sub ⦃ … ⦄
--   open SubWithLaws ⦃ … ⦄

--   infixl  5  _⋯Ctx'_
--   _⋯Ctx'_ : ∀ ⦃ 𝕂 : Kit ⦄ → Ctx' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx' µ₂ µ'
--   _⋯Ctx'_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ f' where
--     f' = subst₂
--            (λ x y → x –[ 𝕂 ]→ y)
--            (sym (drop-∈-▷▷ x))
--            (sym (drop-∈-▷▷ x))
--            (f ↑* drop-∈ x µ')

--   infixl  5  _⋯Ctx''_
--   _⋯Ctx''_ : ∀ {{𝕂 : Kit}} → Ctx'' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx'' µ₂ µ'
--   _⋯Ctx''_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ (f ↑* drop-∈ x µ')
