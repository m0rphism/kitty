open import Kitty.Term.Modes

module Kitty.Term.Sub.Syntax {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function using (_$_)

open Modes 𝕄
open Terms 𝕋

open import Kitty.Term.Kit 𝕋 using (Kit; _∋/⊢[_]_)
open import Kitty.Term.Sub 𝕋

open Kit ⦃ … ⦄ hiding (_,ₖ_; _↑_; _↑*_; _–→_; ~-cong-↑; ~-cong-↑*; _∥_; ⦅_⦆; _↓)

-- data _–[_]→_ : List VarMode → Kit → List VarMode → Set where
--   []ₖ  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→ []
--   _,ₖ_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
--   wkₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)

-- ap : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
-- ap (ϕ ,ₖ x/t) m (here refl) = x/t
-- ap (ϕ ,ₖ x/t) m (there x) = ap ϕ m x
-- ap (wkₖ m' ϕ) m x = wk _ (ap ϕ m x)

-- instance
--   Sub-Sub : Sub
--   Sub._–[_]→_      Sub-Sub = _–[_]→_
--   Sub.[]ₖ          Sub-Sub = []ₖ
--   Sub._,ₖ_         Sub-Sub = _,ₖ_
--   Sub.wkₖ          Sub-Sub = wkₖ
--   Sub.apₖ          Sub-Sub = ap
--   Sub.apₖ-,ₖ-here  Sub-Sub = λ ϕ x/t → refl
--   Sub.apₖ-,ₖ-there Sub-Sub = λ ϕ x/t x → refl
--   Sub.apₖ-wkₖ-wk   Sub-Sub = λ ϕ x/t → refl
