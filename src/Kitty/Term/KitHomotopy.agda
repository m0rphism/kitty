open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitHomotopy {𝕄 : Modes} (𝕋 : Terms 𝕄) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) (T : Traversal 𝕋 𝕊) where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws 𝕊
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private instance _ = kitᵣ; _ = kitₛ
private instance _ = kittᵣ; _ = kittₛ

record KitHomotopy : Set₁ where
  field
    ~-cong-⋯ :
      ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
        ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
        {µ₁ µ₂ M}
        {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} (t : µ₁ ⊢ M)
      → f ~ g
      → t ⋯ f ≡ t ⋯ g

  ⋯-ι-→ :
    ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
      ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄
      {µ₁ µ₂ M}
      (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → t ⋯ ϕ ≡ t ⋯ ι-→ ϕ
  ⋯-ι-→ t ϕ = ~-cong-⋯ t (~-ι-→ ϕ)

  ren→sub :
    ∀ {µ₁ µ₂ M} (t : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂)
    → t ⋯ᵣ ρ ≡ t ⋯ₛ ι-→ ⦃ 𝕂₁⊑𝕂₂ = ⊑-ᵣₛ ⦄ ρ
  ren→sub = ⋯-ι-→ ⦃ 𝕂₁⊑𝕂₂ = ⊑-ᵣₛ ⦄

  wk~wk :
    ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
      {m} {µ}
    → wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m id ~ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m (id {µ = µ})
  wk~wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {m} {µ} mx x =
    `/id ⦃ 𝕂₁ ⦄ (x & wkₖ    m id) ≡⟨ cong (`/id ⦃ 𝕂₁ ⦄) (&-wkₖ-wk id x) ⟩
    `/id ⦃ 𝕂₁ ⦄ (wk _ (x & id))   ≡⟨ cong (λ ■ → `/id ⦃ 𝕂₁ ⦄ (wk ⦃ 𝕂₁ ⦄ _ ■)) (&-id x) ⟩
    `/id ⦃ 𝕂₁ ⦄ (wk _ (id/` x ))  ≡⟨ cong (`/id ⦃ 𝕂₁ ⦄) (wk-id/` _ x) ⟩
    `/id ⦃ 𝕂₁ ⦄ (id/` (there x))  ≡⟨ id/`/id (there x) ⟩
    ` there x                     ≡⟨ sym (id/`/id (there x)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (id/` (there x))  ≡⟨ cong (`/id ⦃ 𝕂₂ ⦄) (sym (wk-id/` _ x)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk _ (id/` x ))  ≡⟨ cong (λ ■ → `/id ⦃ 𝕂₂ ⦄ (wk ⦃ 𝕂₂ ⦄ _ ■)) (sym (&-id x)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk _ (x & id))   ≡⟨ cong (`/id ⦃ 𝕂₂ ⦄) (sym (&-wkₖ-wk id x)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (x & wkₖ m id)    ∎

  ⋯-x/t-wk' :
    ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
      {µ₁} {m'} {m/M : VarMode/TermMode ⦃ 𝕂₁ ⦄} (x/t : µ₁ ∋/⊢ m/M)
    → (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id) ≡ `/id' (wk m' x/t)
  ⋯-x/t-wk' ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ₁} {m'} {m/M} x/t =
    `/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id   ≡⟨ ~-cong-⋯ (`/id' x/t) wk~wk ⟩
    `/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨ wkₖ-⋯' ⟩
    `/id' (wk m' x/t)                  ∎

  ⋯-x/t-wk :
    ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄
      {µ} {m'} {m} (x/t : µ ∋/⊢[ 𝕂₁ ] id/m→M m)
    → (`/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id) ≡ `/id (wk m' x/t)
  ⋯-x/t-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ} {m'} {m} x/t =
    `/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id   ≡⟨ ~-cong-⋯ (`/id x/t) wk~wk ⟩
    `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨ wkₖ-⋯ ⟩
    `/id (wk m' x/t)                  ∎

  ⊑ₖ-⊤ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ KT : KitT 𝕂 ⦄ → 𝕂 ⊑ₖ kitₛ
  ⊑ₖ-⊤ ⦃ 𝕂 ⦄ = record
    { ι-Mode   = m→M/id
    ; ι-id/m→M = id/m→M/id
    ; ι-m→M/id = λ m/M → refl
    ; ι-∋/⊢    = `/id'
    ; ι-id/`   = id/`/id'
    ; ι-`/id   = λ {µ} {m} x/t →
        let sub = subst (µ ⊢_) (id/m→M/id m) in
        `/id x/t        ≡⟨ `/id≡`/id' x/t ⟩
        sub (`/id' x/t) ∎
    ; ι-`/id'  = λ x/t → refl
    ; ι-wk     = λ {m'} {m} {µ} {m/M} x/t →
        `/id' (wk _ x/t)                  ≡⟨ sym (⋯-x/t-wk' x/t) ⟩
        `/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨⟩
        wk _ (`/id' x/t)   ∎
    ; ι-∋/⊢-id = λ { refl x/t → refl }
    ; ι-∋/⊢-~ₜ = λ {µ} {m} x/t →
        let sub = subst (µ ⊢_) (id/m→M/id m) in
        sub (`/id' ⦃ 𝕂 ⦄ x/t) ≡⟨ sym (`/id≡`/id' x/t) ⟩
        `/id x/t              ∎
    ; ι-∋/⊢-~ₜ[] = λ x/t → refl
    }

-- open import Axiom.Extensionality.Propositional using (Extensionality)

-- Extensionality→KitHomotopy : ∀ {T} → Extensionality 0ℓ 0ℓ → KitHomotopy T
-- Extensionality→KitHomotopy {T} fun-ext =
--   let open Traversal T in record
--   { ~-cong-⋯ = λ t f~g → cong (t ⋯_) (fun-ext (λ m → fun-ext (λ x → f~g m x))) }