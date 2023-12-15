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
open _⊑ₖ_ ⦃ … ⦄

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : SortCtx
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

private instance
  _ = Kᵣ
  _ = Kₛ
  _ = Wᵣ
  _ = Wₛ

record ComposeKit (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) (K₁⊔K₂ : Kit _∋/⊢_) : Set (lsuc ℓ) where
  infixl  8  _&/⋯_

  private instance _ = K₁; _ = K₂; _ = K₁⊔K₂

  field
    ⦃ K₁⊑K₁⊔K₂ ⦄ : K₁ ⊑ₖ K₁⊔K₂
    ⦃ K₂⊑K₁⊔K₂ ⦄ : K₂ ⊑ₖ K₁⊔K₂

    _&/⋯_ :
      ∀ {S₁} {S₂} {s}
      → S₁ ∋/⊢[ K₁ ] s
      → S₁ –[ K₂ ]→ S₂
      → S₂ ∋/⊢[ K₁⊔K₂ ] s

    &/⋯-⋯ :
      ∀ {S₁} {S₂} {s} (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) 
      → `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ

    &/⋯-wk-↑ :
      ∀ {S₁} {S₂} {s'} {s} (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂)
      → wk s' (x/t &/⋯ ϕ) ≡ wk s' x/t &/⋯ (ϕ ↑ s')

    ~-cong-&/⋯ :
      ∀ {x/t₁ x/t₂ : S₁ ∋/⊢[ K₁ ] s} {ϕ₁ ϕ₂ : S₁ –[ K₂ ]→ S₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ &/⋯ ϕ₁ ≡ x/t₂ &/⋯ ϕ₂

  -- TODO: If this is possible, it might simplify instantiating the compose kit hierarchy quite a bit.
  -- &/⋯-wk-↑' :
  --   ∀ ⦃ W : KitT K₁ ⦄ ⦃ W : KitT K₁⊔K₂ ⦄ {S₁} {S₂} {s'} {s} (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂)
  --   → wk s' (x/t &/⋯ ϕ) ≡ wk s' x/t &/⋯ (ϕ ↑ s')
  -- &/⋯-wk-↑' {S₁} {S₂} {s'} {s} x/t ϕ = `/id-injective (
  --   `/id (wk s' (x/t &/⋯ ϕ))      ≡⟨ sym (wk-`/id s' (x/t &/⋯ ϕ)) ⟩
  --   wk s' (`/id (x/t &/⋯ ϕ))      ≡⟨ cong (wk s') (&/⋯-⋯ x/t ϕ) ⟩
  --   wk s' (`/id x/t ⋯ ϕ)          ≡⟨ {!!} ⟩
  --   wk s' (`/id x/t) ⋯ (ϕ ↑ s')   ≡⟨ cong (_⋯ ϕ ↑ s') (wk-`/id s' x/t) ⟩
  --   `/id (wk s' x/t) ⋯ (ϕ ↑ s')   ≡⟨ sym (&/⋯-⋯ (wk s' x/t) (ϕ ↑ s')) ⟩
  --   `/id (wk s' x/t &/⋯ (ϕ ↑ s')) ∎)

  &/⋯-& :
    ∀ {S₁} {S₂} {s} (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) 
    → id/` ⦃ K₁ ⦄ x &/⋯ ϕ ≡ ι-∋/⊢ (x & ϕ)
  &/⋯-& {S₁} {S₂} {s} x ϕ = `/id-injective (
    let open ≡-Reasoning in
    `/id (id/` x &/⋯ ϕ)             ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
    `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ        ≡⟨ cong (_⋯ ϕ) (id/`/id ⦃ K₁ ⦄ x) ⟩
    ` x ⋯ ϕ                         ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
    `/id ⦃ K₂ ⦄ (x & ϕ)             ≡⟨ ι-`/id (x & ϕ) ⟩
    `/id ⦃ K₁⊔K₂ ⦄  (ι-∋/⊢ (x & ϕ)) ∎)

  &/⋯-wk :
    ∀ ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄ {s' s} (x/t : S₁ ∋/⊢[ K₁ ] s)
    → x/t &/⋯ wkₖ ⦃ K = K₂ ⦄ s' id ≡ ι-∋/⊢ (wk s' x/t)
  &/⋯-wk {S₁} ⦃ W ⦄ {s'} {s} x/t = `/id-injective (
    let open ≡-Reasoning in
    `/id (x/t &/⋯ wkₖ ⦃ K = K₂ ⦄ s' id) ≡⟨ &/⋯-⋯ x/t (wkₖ ⦃ K = K₂ ⦄ s' id) ⟩
    `/id x/t ⋯ wkₖ ⦃ K = K₂ ⦄ s' id     ≡⟨ ⋯-x/t-wk x/t ⟩
    `/id (wk s' x/t)                     ≡⟨ ι-`/id (wk s' x/t) ⟩
    `/id (ι-∋/⊢ (wk s' x/t))             ∎)

infixl  8  _&/⋯[_]_

_&/⋯[_]_ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₁⊔K₂ : Kit _∋/⊢_ ⦄ {s}
            → S₁ ∋/⊢[ K₁ ] s
            → (C : ComposeKit K₁ K₂ K₁⊔K₂)
            → S₁ –[ K₂ ]→ S₂
            → S₂ ∋/⊢[ K₁⊔K₂ ] s
x/t &/⋯[ C ] ϕ = x/t &/⋯ ϕ where open ComposeKit C

open ComposeKit ⦃ … ⦄

-- ComposeKit for Renamings ----------------------------------------------------

&/⋯-⋯ᵣ :
  ∀ ⦃ K₂ : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) 
  → `/id (x & ϕ) ≡ ` x ⋯ ϕ
&/⋯-⋯ᵣ ⦃ K₂ ⦄ {S₁} {S₂} {s} x ϕ = sym (⋯-var x ϕ)

&/⋯-wk-↑ᵣ :
  ∀ ⦃ K₂ : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {sx}
    (x : S₁ ∋ sx)
    (ϕ : S₁ –[ K₂ ]→ S₂)
  → wk _ (x & ϕ) ≡ there x & (ϕ ↑ s)
&/⋯-wk-↑ᵣ ⦃ K₂ ⦄ {S₁} {S₂} {s} {sx} x ϕ = sym (&-↑-there ϕ x)

Cᵣ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K K
Cᵣ ⦃ K ⦄ = record
  { K₁⊑K₁⊔K₂   = ⊑ₖ-⊥ ⦃ K = K ⦄
  ; K₂⊑K₁⊔K₂   = ⊑ₖ-refl ⦃ K ⦄
  ; _&/⋯_      = _&_
  ; &/⋯-⋯      = &/⋯-⋯ᵣ
  ; &/⋯-wk-↑   = &/⋯-wk-↑ᵣ
  ; ~-cong-&/⋯ = λ { refl ϕ₁~ϕ₂ → use-~-hom ϕ₁~ϕ₂ _ _ }
  }

-- &/⋯-wk-↑ₛ : ∀ ⦃ K ⦄ {S₁} {S₂} {s} {sx}
--               (t : S₁ ⊢ sx)
--               (ϕ : S₁ –[ K ]→ S₂)
--             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ s)
-- &/⋯-wk-↑ₛ ⦃ K ⦄ {S₁} {S₂} {s} {sx} t ϕ =
--   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
--   t ⋯ ϕ ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
--   t ⋯ (ϕ ↑* []) ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* [])       ≡⟨⟩
--   t ⋯* (wkₖ ⦃ K = Kᵣ ⦄ _ id ∷ ϕ ∷ []) ↑** []        ≡⟨
--     ⋯-↑ (wkₖ ⦃ K = Kᵣ ⦄ _ id ∷ ϕ ∷ [])
--         ((ϕ ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ _ id ∷ [])
--         (λ {S'} x →
--           ` x ⋯ (ϕ ↑* S') ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* S')           ≡⟨ cong (_⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* S')) (⋯-var x (ϕ ↑* S')) ⟩
--           `/id (x & (ϕ ↑* S')) ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* S')       ≡⟨ {!!} ⟩
--           `/id (x & (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* S')) ⋯ ((ϕ ↑ s) ↑* S') ≡⟨ cong (_⋯ ϕ ↑ s ↑* S') (sym (⋯-var x (wkₖ _ id ↑* S'))) ⟩
--           ` x ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* S') ⋯ ((ϕ ↑ s) ↑* S')      ∎
--         )
--         t ⟩
--   t ⋯* ((ϕ ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ _ id ∷ []) ↑** []  ≡⟨⟩
--   t ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ↑* []) ⋯ ((ϕ ↑ s) ↑* []) ≡⟨ {!!} ⟩
--   t ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ⋯ (ϕ ↑ s)                 ≡⟨ {!!} ⟩
--   wk _ t ⋯ (ϕ ↑ s)                                    ∎

-- Cₛ : ∀ ⦃ K ⦄ → ComposeKit Kₛ K Kₛ
-- Cₛ ⦃ K ⦄ = record
--   { K₁⊑K₁⊔K₂   = ⊑ₖ-refl ⦃ Kₛ ⦄
--   ; K₂⊑K₁⊔K₂   = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ K ⦄
--   ; _&/⋯_      = _⋯_
--   ; &/⋯-⋯      = {!&/⋯-⋯ᵣ!}
--   ; &/⋯-ap     = λ x ϕ → {!!}
--   ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ
--   ; ~-cong-&/⋯ = {!λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }!}
  -- }
