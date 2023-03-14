open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitHomotopy {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
-- open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT 𝕋 T 𝕊
open import Kitty.Term.KitOrder 𝕋 hiding (_⊑ₖ_)
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open KitT ⦃ … ⦄
open Sub ⦃ … ⦄ hiding (_–[_]→_)
open SubWithLaws ⦃ … ⦄
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private instance _ = 𝕊
private instance _ = kittᵣ; _ = kittₛ

record KitHomotopy : Set₁ where
  field
    ~-cong-⋯ :
      ∀ ⦃ 𝕂₁ 𝕂₂ : KitT ⦄
        {µ₁ µ₂ M}
        {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} (t : µ₁ ⊢ M)
      → f ~ g
      → t ⋯ f ≡ t ⋯ g

  ⋯-ι-→ :
    ∀ ⦃ 𝕂₁ 𝕂₂ : KitT ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄
      {µ₁ µ₂ M}
      (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → t ⋯ ϕ ≡ t ⋯ ι-→ ϕ
  ⋯-ι-→ t ϕ = ~-cong-⋯ t (~-ι-→ ϕ)

  ren→sub : ∀ {µ₁ µ₂ M} (t : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
            t ⋯ᵣ ρ ≡ t ⋯ₛ ι-→ ⦃ 𝕂₁⊑𝕂₂ = ⊑-ᵣₛ ⦄ ρ
  ren→sub = ⋯-ι-→ ⦃ 𝕂₁⊑𝕂₂ = ⊑-ᵣₛ ⦄

-- open import Axiom.Extensionality.Propositional using (Extensionality)

-- Extensionality→KitHomotopy : ∀ {T} → Extensionality 0ℓ 0ℓ → KitHomotopy T
-- Extensionality→KitHomotopy {T} fun-ext =
--   let open Traversal T in record
--   { ~-cong-⋯ = λ t f~g → cong (t ⋯_) (fun-ext (λ m → fun-ext (λ x → f~g m x))) }
