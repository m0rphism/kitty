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
  ⦃ K ⦄ ⦃ K₁ ⦄ ⦃ K₂  ⦄ : Kit _∋/⊢_

record _⊑ₖ_ (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) : Set₁ where 
  private instance _ = K₁; _ = K₂
  field
    ι-∋/⊢  : ∀ {S} {m} → S ∋/⊢[ K₁ ] m → S ∋/⊢[ K₂ ] m
    ι-id/` : ∀ {S} {m} (x : S ∋ m)
             → ι-∋/⊢ (Kit.id/` K₁ x) ≡ Kit.id/` K₂ x
    ι-`/id : ∀ {S} {m} (x/t : S ∋/⊢[ K₁ ] m)
             → Kit.`/id K₁ x/t ≡ Kit.`/id K₂ (ι-∋/⊢ x/t)

    ι-wk : ∀ {m'} {m} {S} (x/t : S ∋/⊢[ K₁ ] m)
             → ι-∋/⊢ (Kit.wk K₁ m' x/t) ≡ Kit.wk K₂ m' (ι-∋/⊢ x/t)

  -- _,ₖ'_ : ∀ {S₁} {S₂} {m}
  --         → S₁ –[ K₂ ]→ S₂
  --         → S₂ ∋/⊢[ K₁ ] id/m→M m
  --         → (S₁ ▷ m) –[ K₂ ]→ S₂
  -- _,ₖ'_ {S₁} {S₂} {m} ϕ x/t =
  --   let sub = subst (S₂ ∋/⊢[ K₂ ]_) (ι-id/m→M m) in
  --   ϕ ,ₖ  sub (ι-∋/⊢ x/t)

⊑ₖ-refl : K ⊑ₖ K
⊑ₖ-refl = record
  { ι-∋/⊢    = λ x → x
  ; ι-id/`   = λ x → refl
  ; ι-`/id   = λ x/t → refl
  ; ι-wk     = λ x/t → refl
  }

-- -- Probably not needed
-- ⊑ₖ-trans : ∀ ⦃ K₁ K₂ K₃ : Kit ⦄ → K₁ ⊑ₖ K₂ → K₂ ⊑ₖ K₃ → K₁ ⊑ₖ K₃
-- _⊑ₖ_.ι-Mode (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) m/M =
--   ι-Mode K₂⊑K₃ (ι-Mode K₁⊑K₂ m/M)
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-id/m→M (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) m =
--   ι-Mode K₂⊑K₃ (ι-Mode K₁⊑K₂ (Kit.id/m→M K₁ m)) ≡⟨ cong (ι-Mode K₂⊑K₃) (ι-id/m→M K₁⊑K₂ m) ⟩
--   ι-Mode K₂⊑K₃ (Kit.id/m→M K₂ m)                 ≡⟨ ι-id/m→M K₂⊑K₃ m ⟩
--   Kit.id/m→M K₃ m                                 ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-m→M/id (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) m/M =
--   Kit.m→M/id K₁ m/M                                 ≡⟨ ι-m→M/id K₁⊑K₂ m/M ⟩
--   Kit.m→M/id K₂ (ι-Mode K₁⊑K₂ m/M)                 ≡⟨ ι-m→M/id K₂⊑K₃ (ι-Mode K₁⊑K₂ m/M) ⟩
--   Kit.m→M/id K₃ (ι-Mode K₂⊑K₃ (ι-Mode K₁⊑K₂ m/M)) ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-∋/⊢ (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) x =
--   ι-∋/⊢ K₂⊑K₃ (ι-∋/⊢ K₁⊑K₂ x)
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-id/` (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) {S} {m} x =
--   let sub = subst (S ∋/⊢[ K₃ ]_) (sym (ι-id/m→M (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) m)) in
--   let sub₁ = subst (S ∋/⊢[ K₂ ]_) (sym (ι-id/m→M K₁⊑K₂ m)) in
--   let sub₂ = subst (S ∋/⊢[ K₃ ]_) (sym (ι-id/m→M K₂⊑K₃ m)) in
--   let sub₂' = subst (S ∋/⊢[ K₃ ]_) (ι-id/m→M K₂⊑K₃ m) in
--   ι-∋/⊢ K₂⊑K₃ (ι-∋/⊢ K₁⊑K₂ (Kit.id/` K₁ m x)) ≡⟨ cong (ι-∋/⊢ K₂⊑K₃) (ι-id/` K₁⊑K₂ x) ⟩
--   ι-∋/⊢ K₂⊑K₃ (sub₁ (Kit.id/` K₂ m x))         ≡⟨ {!!} ⟩
--   sub (sub₂' (ι-∋/⊢ K₂⊑K₃ (Kit.id/` K₂ m x)))  ≡⟨ cong sub (cong sub₂' (ι-id/` K₂⊑K₃ x)) ⟩
--   sub (sub₂' (sub₂ (Kit.id/` K₃ m x)))          ≡⟨ {!!} ⟩
--   sub (Kit.id/` K₃ m x)                         ∎
--   where open _⊑ₖ_
-- _⊑ₖ_.ι-`/id (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) = {!!}
-- _⊑ₖ_.ι-`/id' (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) = {!!}
-- _⊑ₖ_.ι-wk (⊑ₖ-trans ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ K₁⊑K₂ K₂⊑K₃) = {!!}
