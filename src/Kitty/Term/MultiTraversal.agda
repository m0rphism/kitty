open import Kitty.Term.Terms

-- Version of KitAlt with a simpler KitTraversal.⋯-↑ field.

module Kitty.Term.MultiTraversal (𝕋 : Terms) where

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

open Terms 𝕋
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄

open import Kitty.Util.SubstProperties

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx

-- Alternative KitTraversal ----------------------------------------------------

record MultiTraversal : Setω where
  constructor mkMultiTraversal
  infixl  5  _⋯_

  field
    _⋯_ :
      ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ →
      S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s

  open TraversalOps _⋯_ public

  field
    ⋯-var :
      ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
        (x : S₁ ∋ s) (f : S₁ –[ K ]→ S₂) →
      (` x) ⋯ f ≡ `/id (x & f)

    ⋯-↑ :
      ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {Ks₁ Ks₂ : List KitPkg} {S₁} {S₂}
        (fs : S₁ –[ Ks₁ ]→* S₂) (gs : S₁ –[ Ks₂ ]→* S₂) →
      fs ≈ₓ gs →
      fs ≈ₜ gs
