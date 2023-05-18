open import Kitty.Term.Modes

module Kitty.Term.KitOrder {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Kit ⦃ … ⦄

private variable
  KitMode KitMode₁ KitMode₂ : Set
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : List VarMode → KitMode → Set
  ⦃ 𝕂 ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂  ⦄ : Kit _∋/⊢_

record _⊑ₖ_ (𝕂₁ : Kit _∋/⊢₁_) (𝕂₂ : Kit _∋/⊢₂_) : Set₁ where 
  private instance _ = 𝕂₁; _ = 𝕂₂
  field
    ι-Mode : mode 𝕂₁ → mode 𝕂₂
    ι-id/m→M : ∀ m → ι-Mode (Kit.id/m→M 𝕂₁ m) ≡ Kit.id/m→M 𝕂₂ m
    ι-m→M/id : ∀ m/M → Kit.m→M/id 𝕂₁ m/M ≡ Kit.m→M/id 𝕂₂ (ι-Mode m/M)

    ι-∋/⊢  : ∀ {µ} {m} → µ ∋/⊢[ 𝕂₁ ] id/m→M m → µ ∋/⊢[ 𝕂₂ ] id/m→M m
    ι-id/` : ∀ {µ} {m} (x : µ ∋ m)
             → ι-∋/⊢ (Kit.id/` 𝕂₁ x) ≡ Kit.id/` 𝕂₂ x
    ι-`/id : ∀ {µ} {m} (x/t : µ ∋/⊢[ 𝕂₁ ] Kit.id/m→M 𝕂₁ m)
             → Kit.`/id 𝕂₁ x/t ≡ Kit.`/id 𝕂₂ (ι-∋/⊢ x/t)

    ι-wk : ∀ {m'} {m} {µ} (x/t : µ ∋/⊢[ 𝕂₁ ] id/m→M m)
             → ι-∋/⊢ (Kit.wk 𝕂₁ m' x/t) ≡ Kit.wk 𝕂₂ m' (ι-∋/⊢ x/t)

  -- _,ₖ'_ : ∀ {µ₁} {µ₂} {m}
  --         → µ₁ –[ 𝕂₂ ]→ µ₂
  --         → µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m
  --         → (µ₁ ▷ m) –[ 𝕂₂ ]→ µ₂
  -- _,ₖ'_ {µ₁} {µ₂} {m} ϕ x/t =
  --   let sub = subst (µ₂ ∋/⊢[ 𝕂₂ ]_) (ι-id/m→M m) in
  --   ϕ ,ₖ  sub (ι-∋/⊢ x/t)

⊑ₖ-refl : 𝕂 ⊑ₖ 𝕂
⊑ₖ-refl = record
  { ι-Mode   = λ m/M → m/M
  ; ι-id/m→M = λ m → refl
  ; ι-m→M/id = λ m/M → refl
  ; ι-∋/⊢    = λ x → x
  ; ι-id/`   = λ x → refl
  ; ι-`/id   = λ x/t → refl
  ; ι-wk     = λ x/t → refl
  }

-- -- Probably not needed
-- ⊑ₖ-trans : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ : Kit ⦄ → 𝕂₁ ⊑ₖ 𝕂₂ → 𝕂₂ ⊑ₖ 𝕂₃ → 𝕂₁ ⊑ₖ 𝕂₃
-- _⊑ₖ_.ι-Mode (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) m/M =
--   ι-Mode 𝕂₂⊑𝕂₃ (ι-Mode 𝕂₁⊑𝕂₂ m/M)
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-id/m→M (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) m =
--   ι-Mode 𝕂₂⊑𝕂₃ (ι-Mode 𝕂₁⊑𝕂₂ (Kit.id/m→M 𝕂₁ m)) ≡⟨ cong (ι-Mode 𝕂₂⊑𝕂₃) (ι-id/m→M 𝕂₁⊑𝕂₂ m) ⟩
--   ι-Mode 𝕂₂⊑𝕂₃ (Kit.id/m→M 𝕂₂ m)                 ≡⟨ ι-id/m→M 𝕂₂⊑𝕂₃ m ⟩
--   Kit.id/m→M 𝕂₃ m                                 ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-m→M/id (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) m/M =
--   Kit.m→M/id 𝕂₁ m/M                                 ≡⟨ ι-m→M/id 𝕂₁⊑𝕂₂ m/M ⟩
--   Kit.m→M/id 𝕂₂ (ι-Mode 𝕂₁⊑𝕂₂ m/M)                 ≡⟨ ι-m→M/id 𝕂₂⊑𝕂₃ (ι-Mode 𝕂₁⊑𝕂₂ m/M) ⟩
--   Kit.m→M/id 𝕂₃ (ι-Mode 𝕂₂⊑𝕂₃ (ι-Mode 𝕂₁⊑𝕂₂ m/M)) ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-∋/⊢ (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) x =
--   ι-∋/⊢ 𝕂₂⊑𝕂₃ (ι-∋/⊢ 𝕂₁⊑𝕂₂ x)
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-id/` (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) {µ} {m} x =
--   let sub = subst (µ ∋/⊢[ 𝕂₃ ]_) (sym (ι-id/m→M (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) m)) in
--   let sub₁ = subst (µ ∋/⊢[ 𝕂₂ ]_) (sym (ι-id/m→M 𝕂₁⊑𝕂₂ m)) in
--   let sub₂ = subst (µ ∋/⊢[ 𝕂₃ ]_) (sym (ι-id/m→M 𝕂₂⊑𝕂₃ m)) in
--   let sub₂' = subst (µ ∋/⊢[ 𝕂₃ ]_) (ι-id/m→M 𝕂₂⊑𝕂₃ m) in
--   ι-∋/⊢ 𝕂₂⊑𝕂₃ (ι-∋/⊢ 𝕂₁⊑𝕂₂ (Kit.id/` 𝕂₁ m x)) ≡⟨ cong (ι-∋/⊢ 𝕂₂⊑𝕂₃) (ι-id/` 𝕂₁⊑𝕂₂ x) ⟩
--   ι-∋/⊢ 𝕂₂⊑𝕂₃ (sub₁ (Kit.id/` 𝕂₂ m x))         ≡⟨ {!!} ⟩
--   sub (sub₂' (ι-∋/⊢ 𝕂₂⊑𝕂₃ (Kit.id/` 𝕂₂ m x)))  ≡⟨ cong sub (cong sub₂' (ι-id/` 𝕂₂⊑𝕂₃ x)) ⟩
--   sub (sub₂' (sub₂ (Kit.id/` 𝕂₃ m x)))          ≡⟨ {!!} ⟩
--   sub (Kit.id/` 𝕂₃ m x)                         ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-`/id (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
-- _⊑ₖ_.ι-`/id' (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
-- _⊑ₖ_.ι-wk (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
