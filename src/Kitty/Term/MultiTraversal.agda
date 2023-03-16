open import Kitty.Term.Modes

-- Version of KitAlt with a simpler KitTraversal.⋯-↑ field.

module Kitty.Term.MultiTraversal {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (_⊔_; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Kit 𝕋
open import Kitty.Term.MultiSub 𝕋
open import Kitty.Term.Prelude
open import Kitty.Term.Sub 𝕋
open import Kitty.Term.Traversal 𝕋
open import Kitty.Util.Star

open Modes 𝕄
open Terms 𝕋
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄

open import Kitty.Util.SubstProperties

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Alternative KitTraversal ----------------------------------------------------

record MultiTraversal : Setω where
  constructor mkMultiTraversal
  infixl  5  _⋯_

  field
    _⋯_   : ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ ⦃ 𝕂 : Kit ⦄ →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

  open TraversalOps _⋯_ public

  field
    ⋯-var : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (f : µ₁ –[ 𝕂 ]→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-↑ : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s₁ ]→* µ₂) (gs : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → fs ≈ₓ gs
          → fs ≈ₜ gs
