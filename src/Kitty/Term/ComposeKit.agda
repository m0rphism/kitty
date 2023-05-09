open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.ComposeKit
    {𝕄 : Modes}
    {𝕋 : Terms 𝕄}
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

open Modes 𝕄
open Terms 𝕋
open Traversal T
open KitHomotopy H
open Kit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

private variable
  KitMode KitMode₁ KitMode₂ : Set
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : List VarMode → KitMode → Set

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
      ∀ {µ₁} {µ₂} {m}
      → µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m
             → µ₁ –[ 𝕂₂ ]→ µ₂
      → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] id/m→M m

    &/⋯-⋯ :
      ∀ {µ₁} {µ₂} {m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
      → `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ

    &/⋯-wk-↑ :
      ∀ {µ₁} {µ₂} {m'} {m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
      → wk m' (x/t &/⋯ ϕ) ≡ wk m' x/t &/⋯ (ϕ ↑ m')

    ~-cong-&/⋯ :
      ∀ {x/t₁ x/t₂ : µ₁ ∋/⊢[ 𝕂₁ ] (id/m→M m)} {ϕ₁ ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ &/⋯ ϕ₁ ≡ x/t₂ &/⋯ ϕ₂

  -- TODO: If this is possible, it might simplify instantiating the compose kit hierarchy quite a bit.
  -- &/⋯-wk-↑' :
  --   ∀ ⦃ W : KitT 𝕂₁ ⦄ ⦃ W : KitT 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {m'} {m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
  --   → wk m' (x/t &/⋯ ϕ) ≡ wk m' x/t &/⋯ (ϕ ↑ m')
  -- &/⋯-wk-↑' {µ₁} {µ₂} {m'} {m} x/t ϕ = `/id-injective (
  --   `/id (wk m' (x/t &/⋯ ϕ))      ≡⟨ sym (wk-`/id m' (x/t &/⋯ ϕ)) ⟩
  --   wk m' (`/id (x/t &/⋯ ϕ))      ≡⟨ cong (wk m') (&/⋯-⋯ x/t ϕ) ⟩
  --   wk m' (`/id x/t ⋯ ϕ)          ≡⟨ {!!} ⟩
  --   wk m' (`/id x/t) ⋯ (ϕ ↑ m')   ≡⟨ cong (_⋯ ϕ ↑ m') (wk-`/id m' x/t) ⟩
  --   `/id (wk m' x/t) ⋯ (ϕ ↑ m')   ≡⟨ sym (&/⋯-⋯ (wk m' x/t) (ϕ ↑ m')) ⟩
  --   `/id (wk m' x/t &/⋯ (ϕ ↑ m')) ∎)

  &/⋯-& :
    ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    → id/` ⦃ 𝕂₁ ⦄ x &/⋯ ϕ ≡ ι-∋/⊢ (x & ϕ)
  &/⋯-& {µ₁} {µ₂} {m} x ϕ = `/id-injective (
      `/id (id/` x &/⋯ ϕ)             ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
      `/id ⦃ 𝕂₁ ⦄ (id/` x) ⋯ ϕ        ≡⟨ cong (_⋯ ϕ) (id/`/id ⦃ 𝕂₁ ⦄ x) ⟩
      ` x ⋯ ϕ                         ≡⟨ ⋯-var ⦃ 𝕂₂ ⦄ x ϕ ⟩
      `/id ⦃ 𝕂₂ ⦄ (x & ϕ)             ≡⟨ ι-`/id (x & ϕ) ⟩
      `/id ⦃ 𝕂₁⊔𝕂₂ ⦄  (ι-∋/⊢ (x & ϕ)) ∎)

  -- &/⋯-wk :
  --   ∀ ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ {m' m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m)
  --   → x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id ≡ ι-∋/⊢ (wk m' x/t)
  -- &/⋯-wk {µ₁} ⦃ W ⦄ {m'} {m} x/t = `/id-injective (
  --   `/id (x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id) ≡⟨ &/⋯-⋯ x/t (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id) ⟩
  --   `/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id     ≡⟨ ⋯-x/t-wk x/t ⟩
  --   `/id (wk m' x/t)                     ≡⟨ ι-`/id (wk m' x/t) ⟩
  --   `/id (ι-∋/⊢ (wk m' x/t))            ∎)

-- infixl  8  _&/⋯[_]_

-- _&/⋯[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {m}
--             → µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m
--             → (C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂)
--             → µ₁ –[ 𝕂₂ ]→ µ₂
--             → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] id/m→M m
-- x/t &/⋯[ C ] ϕ = x/t &/⋯ ϕ where open ComposeKit C

-- open ComposeKit ⦃ … ⦄

-- -- ComposeKit for Renamings ----------------------------------------------------

-- &/⋯-⋯ᵣ :
--   ∀ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
--   → `/id (x & ϕ) ≡ ` x ⋯ ϕ
-- &/⋯-⋯ᵣ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} x ϕ = sym (⋯-var x ϕ)

-- &/⋯-wk-↑ᵣ : ∀ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {mx}
--               (x : µ₁ ∋ mx)
--               (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
--             → wk _ (x & ϕ) ≡ there x & (ϕ ↑ m)
-- &/⋯-wk-↑ᵣ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {mx} x ϕ = sym (&-↑-there ϕ x)

-- ckitᵣ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitᵣ 𝕂 𝕂
-- ckitᵣ ⦃ 𝕂 ⦄ = record
--   { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄
--   ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ 𝕂 ⦄
--   ; _&/⋯_      = _&_
--   ; &/⋯-⋯      = &/⋯-⋯ᵣ
--   ; &/⋯-wk-↑   = &/⋯-wk-↑ᵣ
--   ; ~-cong-&/⋯ = λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }
--   }

-- -- -- &/⋯-wk-↑ₛ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx}
-- -- --               (t : µ₁ ⊢ mx)
-- -- --               (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
-- -- --             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
-- -- -- &/⋯-wk-↑ₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} t ϕ =
-- -- --   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
-- -- --   t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
-- -- --   t ⋯ (ϕ ↑* []) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* [])       ≡⟨⟩
-- -- --   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ []) ↑** []        ≡⟨
-- -- --     ⋯-↑ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ [])
-- -- --         ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ [])
-- -- --         (λ {µ'} x →
-- -- --           ` x ⋯ (ϕ ↑* µ') ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')           ≡⟨ cong (_⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) (⋯-var x (ϕ ↑* µ')) ⟩
-- -- --           `/id (x & (ϕ ↑* µ')) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')       ≡⟨ {!!} ⟩
-- -- --           `/id (x & (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) ⋯ ((ϕ ↑ m) ↑* µ') ≡⟨ cong (_⋯ ϕ ↑ m ↑* µ') (sym (⋯-var x (wkₖ _ id ↑* µ'))) ⟩
-- -- --           ` x ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ') ⋯ ((ϕ ↑ m) ↑* µ')      ∎
-- -- --         )
-- -- --         t ⟩
-- -- --   t ⋯* ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ []) ↑** []  ≡⟨⟩
-- -- --   t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* []) ⋯ ((ϕ ↑ m) ↑* []) ≡⟨ {!!} ⟩
-- -- --   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)                 ≡⟨ {!!} ⟩
-- -- --   wk _ t ⋯ (ϕ ↑ m)                                    ∎

-- -- -- ckitₛ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitₛ 𝕂 kitₛ
-- -- -- ckitₛ ⦃ 𝕂 ⦄ = record
-- -- --   { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ kitₛ ⦄
-- -- --   ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄
-- -- --   ; _&/⋯_      = _⋯_
-- -- --   ; &/⋯-⋯      = {!&/⋯-⋯ᵣ!}
-- -- --   ; &/⋯-ap     = λ x ϕ → {!!}
-- -- --   ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ
-- -- --   ; ~-cong-&/⋯ = {!λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }!}
-- --   -- }
