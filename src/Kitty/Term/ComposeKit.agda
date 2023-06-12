open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.ComposeKit
    {𝕋 : Terms}
    {ℓ} {𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ}
    {T : Traversal 𝕋 𝕊}
    (H : KitHomotopy T)
    where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT T
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Terms 𝕋
open Traversal T
open KitHomotopy H
open Kit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : SortCtx
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

private instance
  _ = kitᵣ
  _ = kitₛ
  _ = kittᵣ
  _ = kittₛ

record ComposeKit (𝕂₁ : Kit _∋/⊢₁_) (𝕂₂ : Kit _∋/⊢₂_) (𝕂₁⊔𝕂₂ : Kit _∋/⊢_) : Set (lsuc ℓ) where
  infixl  8  _&/⋯_

  private instance _ = 𝕂₁; _ = 𝕂₂; _ = 𝕂₁⊔𝕂₂

  field
    ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₁ ⊑ₖ 𝕂₁⊔𝕂₂
    ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₂ ⊑ₖ 𝕂₁⊔𝕂₂

    _&/⋯_ :
      ∀ {S₁} {S₂} {s}
      → S₁ ∋/⊢[ 𝕂₁ ] s
      → S₁ –[ 𝕂₂ ]→ S₂
      → S₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] s

    &/⋯-⋯ :
      ∀ {S₁} {S₂} {s} (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂) 
      → `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ

    &/⋯-wk-↑ :
      ∀ {S₁} {S₂} {s'} {s} (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂)
      → wk s' (x/t &/⋯ ϕ) ≡ wk s' x/t &/⋯ (ϕ ↑ s')

    ~-cong-&/⋯ :
      ∀ {x/t₁ x/t₂ : S₁ ∋/⊢[ 𝕂₁ ] s} {ϕ₁ ϕ₂ : S₁ –[ 𝕂₂ ]→ S₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ &/⋯ ϕ₁ ≡ x/t₂ &/⋯ ϕ₂

  -- TODO: If this is possible, it might simplify instantiating the compose kit hierarchy quite a bit.
  -- &/⋯-wk-↑' :
  --   ∀ ⦃ W : KitT 𝕂₁ ⦄ ⦃ W : KitT 𝕂₁⊔𝕂₂ ⦄ {S₁} {S₂} {s'} {s} (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂)
  --   → wk s' (x/t &/⋯ ϕ) ≡ wk s' x/t &/⋯ (ϕ ↑ s')
  -- &/⋯-wk-↑' {S₁} {S₂} {s'} {s} x/t ϕ = `/id-injective (
  --   `/id (wk s' (x/t &/⋯ ϕ))      ≡⟨ sym (wk-`/id s' (x/t &/⋯ ϕ)) ⟩
  --   wk s' (`/id (x/t &/⋯ ϕ))      ≡⟨ cong (wk s') (&/⋯-⋯ x/t ϕ) ⟩
  --   wk s' (`/id x/t ⋯ ϕ)          ≡⟨ {!!} ⟩
  --   wk s' (`/id x/t) ⋯ (ϕ ↑ s')   ≡⟨ cong (_⋯ ϕ ↑ s') (wk-`/id s' x/t) ⟩
  --   `/id (wk s' x/t) ⋯ (ϕ ↑ s')   ≡⟨ sym (&/⋯-⋯ (wk s' x/t) (ϕ ↑ s')) ⟩
  --   `/id (wk s' x/t &/⋯ (ϕ ↑ s')) ∎)

  &/⋯-& :
    ∀ {S₁} {S₂} {s} (x : S₁ ∋ s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂) 
    → id/` ⦃ 𝕂₁ ⦄ x &/⋯ ϕ ≡ ι-∋/⊢ (x & ϕ)
  &/⋯-& {S₁} {S₂} {s} x ϕ = `/id-injective (
      `/id (id/` x &/⋯ ϕ)             ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
      `/id ⦃ 𝕂₁ ⦄ (id/` x) ⋯ ϕ        ≡⟨ cong (_⋯ ϕ) (id/`/id ⦃ 𝕂₁ ⦄ x) ⟩
      ` x ⋯ ϕ                         ≡⟨ ⋯-var ⦃ 𝕂₂ ⦄ x ϕ ⟩
      `/id ⦃ 𝕂₂ ⦄ (x & ϕ)             ≡⟨ ι-`/id (x & ϕ) ⟩
      `/id ⦃ 𝕂₁⊔𝕂₂ ⦄  (ι-∋/⊢ (x & ϕ)) ∎)

  &/⋯-wk :
    ∀ ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ {s' s} (x/t : S₁ ∋/⊢[ 𝕂₁ ] s)
    → x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s' id ≡ ι-∋/⊢ (wk s' x/t)
  &/⋯-wk {S₁} ⦃ W ⦄ {s'} {s} x/t = `/id-injective (
    `/id (x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s' id) ≡⟨ &/⋯-⋯ x/t (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s' id) ⟩
    `/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s' id     ≡⟨ ⋯-x/t-wk x/t ⟩
    `/id (wk s' x/t)                     ≡⟨ ι-`/id (wk s' x/t) ⟩
    `/id (ι-∋/⊢ (wk s' x/t))             ∎)

infixl  8  _&/⋯[_]_

_&/⋯[_]_ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₁⊔𝕂₂ : Kit _∋/⊢_ ⦄ {s}
            → S₁ ∋/⊢[ 𝕂₁ ] s
            → (C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂)
            → S₁ –[ 𝕂₂ ]→ S₂
            → S₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] s
x/t &/⋯[ C ] ϕ = x/t &/⋯ ϕ where open ComposeKit C

open ComposeKit ⦃ … ⦄

-- ComposeKit for Renamings ----------------------------------------------------

&/⋯-⋯ᵣ :
  ∀ ⦃ 𝕂₂ : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (x : S₁ ∋ s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂) 
  → `/id (x & ϕ) ≡ ` x ⋯ ϕ
&/⋯-⋯ᵣ ⦃ 𝕂₂ ⦄ {S₁} {S₂} {s} x ϕ = sym (⋯-var x ϕ)

&/⋯-wk-↑ᵣ :
  ∀ ⦃ 𝕂₂ : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {sx}
    (x : S₁ ∋ sx)
    (ϕ : S₁ –[ 𝕂₂ ]→ S₂)
  → wk _ (x & ϕ) ≡ there x & (ϕ ↑ s)
&/⋯-wk-↑ᵣ ⦃ 𝕂₂ ⦄ {S₁} {S₂} {s} {sx} x ϕ = sym (&-↑-there ϕ x)

ckitᵣ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ → ComposeKit kitᵣ 𝕂 𝕂
ckitᵣ ⦃ 𝕂 ⦄ = record
  { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄
  ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ 𝕂 ⦄
  ; _&/⋯_      = _&_
  ; &/⋯-⋯      = &/⋯-⋯ᵣ
  ; &/⋯-wk-↑   = &/⋯-wk-↑ᵣ
  ; ~-cong-&/⋯ = λ { refl ϕ₁~ϕ₂ → use-~-hom ϕ₁~ϕ₂ _ _ }
  }

-- &/⋯-wk-↑ₛ : ∀ ⦃ 𝕂 ⦄ {S₁} {S₂} {s} {sx}
--               (t : S₁ ⊢ sx)
--               (ϕ : S₁ –[ 𝕂 ]→ S₂)
--             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ s)
-- &/⋯-wk-↑ₛ ⦃ 𝕂 ⦄ {S₁} {S₂} {s} {sx} t ϕ =
--   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
--   t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
--   t ⋯ (ϕ ↑* []) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* [])       ≡⟨⟩
--   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ []) ↑** []        ≡⟨
--     ⋯-↑ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ [])
--         ((ϕ ↑ s) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ [])
--         (λ {S'} x →
--           ` x ⋯ (ϕ ↑* S') ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* S')           ≡⟨ cong (_⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* S')) (⋯-var x (ϕ ↑* S')) ⟩
--           `/id (x & (ϕ ↑* S')) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* S')       ≡⟨ {!!} ⟩
--           `/id (x & (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* S')) ⋯ ((ϕ ↑ s) ↑* S') ≡⟨ cong (_⋯ ϕ ↑ s ↑* S') (sym (⋯-var x (wkₖ _ id ↑* S'))) ⟩
--           ` x ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* S') ⋯ ((ϕ ↑ s) ↑* S')      ∎
--         )
--         t ⟩
--   t ⋯* ((ϕ ↑ s) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ []) ↑** []  ≡⟨⟩
--   t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* []) ⋯ ((ϕ ↑ s) ↑* []) ≡⟨ {!!} ⟩
--   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ s)                 ≡⟨ {!!} ⟩
--   wk _ t ⋯ (ϕ ↑ s)                                    ∎

-- ckitₛ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitₛ 𝕂 kitₛ
-- ckitₛ ⦃ 𝕂 ⦄ = record
--   { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ kitₛ ⦄
--   ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄
--   ; _&/⋯_      = _⋯_
--   ; &/⋯-⋯      = {!&/⋯-⋯ᵣ!}
--   ; &/⋯-ap     = λ x ϕ → {!!}
--   ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ
--   ; ~-cong-&/⋯ = {!λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }!}
  -- }
