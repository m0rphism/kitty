open import Kitty.Term.Terms

module Kitty.Term.KitOrder (𝕋 : Terms) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Util.SubstProperties

open Terms 𝕋
open Kit ⦃ … ⦄

private variable
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : VarScoped
  ⦃ 𝕂 ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂  ⦄ : Kit _∋/⊢_

record _⊑ₖ_ (𝕂₁ : Kit _∋/⊢₁_) (𝕂₂ : Kit _∋/⊢₂_) : Set₁ where 
  private instance _ = 𝕂₁; _ = 𝕂₂
  field
    ι-∋/⊢  : ∀ {S} {m} → S ∋/⊢[ 𝕂₁ ] m → S ∋/⊢[ 𝕂₂ ] m
    ι-id/` : ∀ {S} {m} (x : S ∋ m)
             → ι-∋/⊢ (Kit.id/` 𝕂₁ x) ≡ Kit.id/` 𝕂₂ x
    ι-`/id : ∀ {S} {m} (x/t : S ∋/⊢[ 𝕂₁ ] m)
             → Kit.`/id 𝕂₁ x/t ≡ Kit.`/id 𝕂₂ (ι-∋/⊢ x/t)

    ι-wk : ∀ {m'} {m} {S} (x/t : S ∋/⊢[ 𝕂₁ ] m)
             → ι-∋/⊢ (Kit.wk 𝕂₁ m' x/t) ≡ Kit.wk 𝕂₂ m' (ι-∋/⊢ x/t)

  -- _,ₖ'_ : ∀ {S₁} {S₂} {m}
  --         → S₁ –[ 𝕂₂ ]→ S₂
  --         → S₂ ∋/⊢[ 𝕂₁ ] id/m→M m
  --         → (S₁ ▷ m) –[ 𝕂₂ ]→ S₂
  -- _,ₖ'_ {S₁} {S₂} {m} ϕ x/t =
  --   let sub = subst (S₂ ∋/⊢[ 𝕂₂ ]_) (ι-id/m→M m) in
  --   ϕ ,ₖ  sub (ι-∋/⊢ x/t)

⊑ₖ-refl : 𝕂 ⊑ₖ 𝕂
⊑ₖ-refl = record
  { ι-∋/⊢    = λ x → x
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
-- _⊑ₖ_.ι-id/` (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) {S} {m} x =
--   let sub = subst (S ∋/⊢[ 𝕂₃ ]_) (sym (ι-id/m→M (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) m)) in
--   let sub₁ = subst (S ∋/⊢[ 𝕂₂ ]_) (sym (ι-id/m→M 𝕂₁⊑𝕂₂ m)) in
--   let sub₂ = subst (S ∋/⊢[ 𝕂₃ ]_) (sym (ι-id/m→M 𝕂₂⊑𝕂₃ m)) in
--   let sub₂' = subst (S ∋/⊢[ 𝕂₃ ]_) (ι-id/m→M 𝕂₂⊑𝕂₃ m) in
--   ι-∋/⊢ 𝕂₂⊑𝕂₃ (ι-∋/⊢ 𝕂₁⊑𝕂₂ (Kit.id/` 𝕂₁ m x)) ≡⟨ cong (ι-∋/⊢ 𝕂₂⊑𝕂₃) (ι-id/` 𝕂₁⊑𝕂₂ x) ⟩
--   ι-∋/⊢ 𝕂₂⊑𝕂₃ (sub₁ (Kit.id/` 𝕂₂ m x))         ≡⟨ {!!} ⟩
--   sub (sub₂' (ι-∋/⊢ 𝕂₂⊑𝕂₃ (Kit.id/` 𝕂₂ m x)))  ≡⟨ cong sub (cong sub₂' (ι-id/` 𝕂₂⊑𝕂₃ x)) ⟩
--   sub (sub₂' (sub₂ (Kit.id/` 𝕂₃ m x)))          ≡⟨ {!!} ⟩
--   sub (Kit.id/` 𝕂₃ m x)                         ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-`/id (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
-- _⊑ₖ_.ι-`/id' (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
-- _⊑ₖ_.ι-wk (⊑ₖ-trans ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ 𝕂₁⊑𝕂₂ 𝕂₂⊑𝕂₃) = {!!}
