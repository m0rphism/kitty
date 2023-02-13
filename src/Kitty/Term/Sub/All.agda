open import Kitty.Term.Modes

module Kitty.Term.Sub.All {𝕄 : Modes} (𝕋 : Terms 𝕄) where

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

-- open import Data.List.Relation.Unary.All

-- ap-all : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
-- ap-all (x/t ∷ ϕ) m (here refl) = x/t
-- ap-all (x/t ∷ ϕ) m (there x) = ap-all ϕ m x

-- instance
--   Sub-All : Sub
--   Sub._–[_]→_      Sub-All = λ µ₁ 𝕂 µ₂ → All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁
--   Sub.[]ₖ          Sub-All = []
--   Sub._,ₖ_         Sub-All = λ ϕ x/t → x/t ∷ ϕ
--   Sub.wkₖ          Sub-All = λ m ϕ → map (wk _) ϕ
--   Sub.apₖ          Sub-All = ap-all
--   Sub.apₖ-,ₖ-here  Sub-All = λ ϕ x/t → refl
--   Sub.apₖ-,ₖ-there Sub-All = λ ϕ x/t x → refl
--   Sub.apₖ-wkₖ-wk   Sub-All = λ ϕ x/t → {!!}
