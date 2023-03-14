open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)

module Kitty.Term.SubCompose {𝕄 : Modes} (𝕋 : Terms 𝕄) (𝕊 : SubWithLaws 𝕋) (T : Traversal 𝕋 𝕊) (H : KitHomotopy 𝕋 𝕊 T) where

open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.Prelude
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties
open ComposeKit ⦃ … ⦄
open Kit ⦃ … ⦄
open Kitty.Term.Sub.SubWithLaws 𝕊
open Modes 𝕄
open Sub ⦃ … ⦄
open Terms 𝕋
open Traversal T
open _⊑ₖ_ ⦃ … ⦄
open ~-Reasoning

record SubCompose : Set₁ where
  infixl  9  _·ₖ_
  infixr  9  _∘ₖ_

  field
    _·ₖ_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ µ₃}
          → µ₁ –[ 𝕂₁ ]→ µ₂
          → µ₂ –[ 𝕂₂ ]→ µ₃
          → µ₁ –[ 𝕂  ]→ µ₃

    &-·ₖ-&/⋯ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} {m}
                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
                (x : µ₁ ∋ m)
              → let sub = subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
                x & (ϕ₁ ·ₖ ϕ₂) ≡ sub ((x & ϕ₁) &/⋯ ϕ₂)

  ~-cong-· : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃}
                {ϕ₁ ϕ₁' : µ₁ –[ 𝕂₁ ]→ µ₂}
                {ϕ₂ ϕ₂' : µ₂ –[ 𝕂₂ ]→ µ₃}
              → ϕ₁ ~ ϕ₁'
              → ϕ₂ ~ ϕ₂'
              → (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁' ·ₖ ϕ₂')
  ~-cong-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' m x =
    let sub = subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
    `/id (x & (ϕ₁  ·ₖ ϕ₂ ))      ≡⟨ cong (`/id) (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x) ⟩
    `/id (sub (x & ϕ₁  &/⋯ ϕ₂ )) ≡⟨ cong (λ ■ → `/id (sub ■)) (~-cong-&/⋯ (~→~' ϕ₁~ϕ₁' _ x) ϕ₂~ϕ₂') ⟩
    `/id (sub (x & ϕ₁' &/⋯ ϕ₂')) ≡⟨ cong (`/id) (sym (&-·ₖ-&/⋯ ϕ₁' ϕ₂' x)) ⟩
    `/id (x & (ϕ₁' ·ₖ ϕ₂'))      ∎

  tm-⋯-· : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} {m}
              (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
              (x : µ₁ ∋ m)
            → `/id (x & ϕ₁) ⋯ ϕ₂ ≡ `/id (x & (ϕ₁ ·ₖ ϕ₂))
  tm-⋯-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} {m} ϕ₁ ϕ₂ x =
    let sub = subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
    let sub' = subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄  m) in
    `/id (x & ϕ₁) ⋯ ϕ₂         ≡⟨ sym (&/⋯-⋯' (x & ϕ₁) ϕ₂) ⟩
    `/id (sub (x & ϕ₁ &/⋯ ϕ₂)) ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x)) ⟩
    `/id (x & (ϕ₁ ·ₖ ϕ₂))      ∎

  dist-↑-· : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} m
                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
              → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  dist-↑-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(here refl) =
    let sub₁ = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
    let sub₂ = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ m) in
    `/id (x & ((ϕ₁ ·ₖ ϕ₂) ↑ m))                             ≡⟨ cong `/id (&-↑-here (ϕ₁ ·ₖ ϕ₂)) ⟩
    `/id (id/` (here refl))                                 ≡⟨ id/`/id (here refl) ⟩
    ` here refl                                             ≡⟨ sym (id/`/id (here refl)) ⟩
    `/id (id/` (here refl))                                 ≡⟨ sym (ι-∋/⊢-~ₜ (id/` (here refl))) ⟩
    `/id (sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (id/` (here refl))))     ≡⟨ cong (λ ■ → `/id (sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ ■)))
                                                                    (sym (&-↑-here ϕ₂)) ⟩
    `/id (sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (here refl & (ϕ₂ ↑ m)))) ≡⟨ cong `/id (sym (&/⋯-& (here refl) (ϕ₂ ↑ m))) ⟩
    `/id (sub₁ (id/` (here refl) &/⋯ (ϕ₂ ↑ m)))             ≡⟨ cong (λ ■ → `/id (sub₁ (■ &/⋯ ϕ₂ ↑ m))) (sym (&-↑-here ϕ₁)) ⟩
    `/id (sub₁ (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m)))                 ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ m) (ϕ₂ ↑ m) x)) ⟩
    `/id (x & ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)))                       ∎
  dist-↑-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(there y) =
    let sub₁ = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    let sub₁' = subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    `/id (x & ((ϕ₁ ·ₖ ϕ₂) ↑ m))                     ≡⟨ cong `/id (&-↑-there (ϕ₁ ·ₖ ϕ₂) y) ⟩
    `/id (wk _ (y & (ϕ₁ ·ₖ ϕ₂)))                    ≡⟨ cong (λ ■ → `/id (wk _ ■)) (&-·ₖ-&/⋯ ϕ₁ ϕ₂ y) ⟩
    `/id (wk _ (sub₁' (y & ϕ₁ &/⋯ ϕ₂)))             ≡⟨ cong `/id (dist-subst (wk _) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) (y & ϕ₁ &/⋯ ϕ₂)) ⟩
    `/id (sub₁ (wk _ (y & ϕ₁ &/⋯ ϕ₂)))              ≡⟨ cong (λ ■ → `/id (sub₁ ■)) (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
    `/id (sub₁ (wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ m)))        ≡⟨ cong (λ ■ → `/id (sub₁ (■ &/⋯ (ϕ₂ ↑ m)))) (sym (&-↑-there ϕ₁ y)) ⟩
    `/id (sub₁ (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m)))         ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ m) (ϕ₂ ↑ m) x)) ⟩
    `/id (x & ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))) ∎

  dist-↑*-· : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁ µ₂ µ₃}
                µ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃) →
    ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ~ ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ))
  dist-↑*-· []      ϕ₁ ϕ₂ =
    ((ϕ₁ ·ₖ ϕ₂) ↑* [])         ~⟨ ↑*-[] (ϕ₁ ·ₖ ϕ₂) ⟩
    ϕ₁ ·ₖ ϕ₂                   ~⟨ ~-sym (~-cong-· (↑*-[] ϕ₁) (↑*-[] ϕ₂)) ⟩
    ((ϕ₁ ↑* []) ·ₖ (ϕ₂ ↑* [])) ~∎
  dist-↑*-· (µ ▷ m) ϕ₁ ϕ₂ =
    (ϕ₁ ·ₖ ϕ₂) ↑* (µ ▷ m)               ~⟨ ↑*-▷ µ m (ϕ₁ ·ₖ ϕ₂) ⟩
    ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ↑ m               ~⟨ ~-cong-↑' (dist-↑*-· µ ϕ₁ ϕ₂) ⟩
    ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ)) ↑ m        ~⟨ dist-↑-· m (ϕ₁ ↑* µ) (ϕ₂ ↑* µ) ⟩
    ((ϕ₁ ↑* µ) ↑ m) ·ₖ ((ϕ₂ ↑* µ) ↑ m)  ~⟨ ~-sym (~-cong-· (↑*-▷ µ m ϕ₁) (↑*-▷ µ m ϕ₂)) ⟩
    (ϕ₁ ↑* (µ ▷ m)) ·ₖ (ϕ₂ ↑* (µ ▷ m))  ~∎

  -- dist-,ₖ-· : ∀ {m}
  --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --               (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
  --             → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --               ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t &/⋯ ϕ₂)) ~ (ϕ₁ ,ₖ x/t ·ₖ ϕ₂)

  _∘ₖ_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃}
        → µ₂ –[ 𝕂₂ ]→ µ₃
        → µ₁ –[ 𝕂₁ ]→ µ₂
        → µ₁ –[ 𝕂 ]→ µ₃
  ϕ₂ ∘ₖ ϕ₁ = ϕ₁ ·ₖ ϕ₂

  infixl  9  _·[_]_
  infixr  9  _∘[_]_

  _·[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {µ₃}
          → µ₁ –[ 𝕂₁ ]→ µ₂
          → ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂
          → µ₂ –[ 𝕂₂ ]→ µ₃
          → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃
  ϕ₁ ·[ C ] ϕ₂ = _·ₖ_ ⦃ C = C ⦄ ϕ₁ ϕ₂


  _∘[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {µ₃}
          → µ₂ –[ 𝕂₂ ]→ µ₃
          → ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂
          → µ₁ –[ 𝕂₁ ]→ µ₂
          → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃
  ϕ₂ ∘[ C ] ϕ₁ = _∘ₖ_ ⦃ C = C ⦄ ϕ₂ ϕ₁

  ·-idʳ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
          → (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄) ~ ϕ
  ·-idʳ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} ϕ mx x =
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    `/id (x & (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄))      ≡⟨ cong (`/id) (&-·ₖ-&/⋯ ϕ id x) ⟩
    `/id (sub (x & ϕ &/⋯ id ⦃ 𝕂 = 𝕂₂ ⦄)) ≡⟨ &/⋯-⋯' (x & ϕ) id ⟩
    `/id (x & ϕ) ⋯ id ⦃ 𝕂 = 𝕂₂ ⦄         ≡⟨ ⋯-id (`/id (x & ϕ)) ⟩
    `/id (x & ϕ)                         ∎

  ·-idˡ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
          → (id ⦃ 𝕂 = 𝕂₁ ⦄ ·ₖ ϕ) ~ ϕ
  ·-idˡ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} ϕ mx x =
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    let sub₂ = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    `/id (x & (id ⦃ 𝕂 = 𝕂₁ ⦄ ·ₖ ϕ))          ≡⟨ cong (`/id) (&-·ₖ-&/⋯ id ϕ x) ⟩
    `/id (sub (x & id ⦃ 𝕂 = 𝕂₁ ⦄ &/⋯ ϕ))     ≡⟨ cong (λ ■ → `/id (sub (■ &/⋯ ϕ))) (&-id ⦃ 𝕂 = 𝕂₁ ⦄ x) ⟩
    `/id (sub (id/` x &/⋯ ϕ))                ≡⟨ cong (`/id) (&/⋯-& x ϕ) ⟩
    `/id (sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (x & ϕ))) ≡⟨ ι-∋/⊢-~ₜ (x & ϕ) ⟩
    `/id (x & ϕ)                             ∎

  -- Alternative route:
    -- (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ (wkₖ _ (ϕ ,ₖ x/t)) ~ ϕ
  -- From which then follows:
    -- wkₖ _ ϕ · ⦅ x/t ⦆ ~
    -- wkₖ _ id · ϕ · ⦅ x/t ⦆ ~
    -- ϕ · wkₖ _ id · ⦅ x/t ⦆ ~
    -- ϕ · id ~
    -- ϕ
  wk-cancels-,ₖ-· :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {m}
      (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m)
    → (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ ϕ
  wk-cancels-,ₖ-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C ⦄ {µ₁} {µ₂} {m} ϕ x/t mx x =
    let sub₁ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    let sub₂ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    `/id (x & (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)))         ≡⟨ cong (`/id) (&-·ₖ-&/⋯ (wkₖ _ id) (ϕ ,ₖ x/t) x) ⟩
    `/id (sub₁ (x & wkₖ _ id &/⋯ (ϕ ,ₖ x/t)))   ≡⟨ cong (λ ■ → `/id (sub₁ (■ &/⋯[ C ] (ϕ ,ₖ x/t)))) (&-wkₖ-wk id x) ⟩
    `/id (sub₁ (wk _ (x & id) &/⋯ (ϕ ,ₖ x/t)))  ≡⟨ cong (λ ■ → `/id (sub₁ (wk ⦃ 𝕂₁ ⦄ _ ■ &/⋯ (ϕ ,ₖ x/t)))) (&-id x) ⟩
    `/id (sub₁ (wk _ (id/` x) &/⋯ (ϕ ,ₖ x/t)))  ≡⟨ cong (λ ■ → `/id (sub₁ (■ &/⋯[ C ] (ϕ ,ₖ x/t)))) (wk-id/` _ x) ⟩
    `/id (sub₁ (id/` (there x) &/⋯ (ϕ ,ₖ x/t))) ≡⟨ cong (`/id) (&/⋯-& (there x) (ϕ ,ₖ x/t)) ⟩
    `/id (sub₂ (ι-∋/⊢ (there x & (ϕ ,ₖ x/t))))  ≡⟨ cong (λ ■ → `/id (sub₂ (ι-∋/⊢ ■))) (&-,ₖ-there ϕ x/t x) ⟩
    `/id (sub₂ (ι-∋/⊢ (x & ϕ)))                 ≡⟨ cong (`/id) (sym (ι-ap-→ ϕ x)) ⟩
    `/id (x & (ι-→ ϕ))                          ≡⟨ ι-~-→ ϕ _ x ⟩
    `/id (x & ϕ)                                ∎

  wk-ϕ-id :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      {µ₁} {µ₂} {m}
      (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → wkₖ m ϕ ~ (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id)
  wk-ϕ-id ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C ⦄ ⦃ W ⦄ {µ₁} {µ₂} {m} ϕ mx x =
    let sub = subst ((µ₂ ▷ m) ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M mx) in
    `/id (x & wkₖ m ϕ)                         ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
    `/id (wk m (x & ϕ))                        ≡⟨ sym (ι-∋/⊢-~ₜ (wk m (x & ϕ))) ⟩
    `/id (sub (ι-∋/⊢ (wk m (x & ϕ))))          ≡⟨ cong (λ ■ → `/id (sub ■)) (sym (&/⋯-wk (x & ϕ))) ⟩
    `/id (sub (x & ϕ &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id)) ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id) x)) ⟩
    `/id (x & (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id))      ∎

  ↑-wk :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂₁⊔𝕂₂ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) m
    → (ϕ ·[ C₁ ] wkₖ m id) ~ (wkₖ m id ·[ C₂ ] (ϕ ↑ m))
  ↑-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} ϕ m =
      (ϕ ·[ C₁ ] wkₖ m id)                             ~⟨ ~-sym (wk-ϕ-id ϕ) ⟩
      wkₖ m ϕ                                          ~⟨ ~-sym (wk-cancels-,ₖ-· (wkₖ m ϕ) (id/` (here refl))) ⟩
      (wkₖ m id ·[ C₂ ] (wkₖ m ϕ ,ₖ id/` (here refl))) ~⟨ ~-cong-· ~-refl (~-sym (↑-,ₖ ϕ m)) ⟩
      (wkₖ m id ·[ C₂ ] (ϕ ↑ m))                       ~∎

  -- Specializations for Renamings ------------------------------------------------

  infixl  9  _ᵣ·_  _ᵣ·ᵣ_  _ᵣ·ₛ_
  infixr  9  _∘ᵣ_  _ᵣ∘ᵣ_  _ₛ∘ᵣ_

  private instance _ = kitᵣ; _ = kitₛ; _ = ckitᵣ

  _ᵣ·_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₃
  ρ ᵣ· ϕ = ρ ·ₖ ϕ

  _∘ᵣ_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₃
  ϕ₂ ∘ᵣ ϕ₁ = ϕ₁ ᵣ· ϕ₂

  _ᵣ·ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₃
  _ᵣ·ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  _ᵣ∘ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ kitᵣ ]→ µ₃
  _ₛ∘ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  _ᵣ·ᵣ_ = _ᵣ·_
  _ᵣ·ₛ_ = _ᵣ·_
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_

