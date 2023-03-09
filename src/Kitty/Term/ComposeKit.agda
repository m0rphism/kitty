open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal; KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.ComposeKit {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (H : KitHomotopy 𝕋 T) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

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
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open KitHomotopy H
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private instance _ = 𝕊

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

private instance
  _ = kitᵣ
  _ = kitₛ

record ComposeKit (𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit) : Set₁ where
  infixl  8  _&/⋯_

  private instance _ = 𝕂₁; _ = 𝕂₂; _ = 𝕂₁⊔𝕂₂

  field
    ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₁ ⊑ₖ 𝕂₁⊔𝕂₂
    ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₂ ⊑ₖ 𝕂₁⊔𝕂₂

    _&/⋯_ : ∀ {µ₁} {µ₂} {m/M}
             → µ₁ ∋/⊢[ 𝕂₁ ] m/M
             → µ₁ –[ 𝕂₂ ]→ µ₂
             → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode m/M)

    &/⋯-⋯ : ∀ {µ₁} {µ₂} {m/M} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
            → let sub = subst (µ₂ ⊢_) (ι-m→M/id m/M) in
              `/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ (x/t &/⋯ ϕ) ≡ sub (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ)

    &/⋯-& : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
             → let sub₁ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
               let sub₂ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ m) in
               sub₁ (id/` x &/⋯ ϕ) ≡ sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (x & ϕ))

    &/⋯-wk-↑ : ∀ {µ₁} {µ₂} {m} {mx}
                 (x/t : µ₁ ∋/⊢[ 𝕂₁ ] mx)
                 (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
               → wk _ (x/t &/⋯ ϕ) ≡ wk _ x/t &/⋯ (ϕ ↑ m)

    &/⋯-wk : ∀ {m'} {m/M : VarMode/TermMode ⦃ 𝕂₁ ⦄} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M)
                 → x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id ≡ ι-∋/⊢ (wk m' x/t)

    -- ⋯-x/t-wk : ∀ {m'} {m/M : VarMode/TermMode ⦃ 𝕂₁ ⦄} (x/t : µ₁ ∋/⊢ m/M)
    --             → (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id) ≡ `/id' (wk m' x/t)

    -- &/⋯-wk : ∀ {µ₁} {µ₂} {m} {mx}
    --             (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --             (x : µ₁ ∋ mx)
    --           → (x & ϕ &/⋯ wkₖ m id) ≡ ι-∋/⊢ (wk _ (x & ϕ))

    ~-cong-&/⋯ :
      ∀ {x/t₁ x/t₂ : µ₁ ∋/⊢[ 𝕂₁ ] (id/m→M m)}
        {ϕ₁ ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ &/⋯ ϕ₁ ≡ x/t₂ &/⋯ ϕ₂

  ⋯-x/t-wk' : ∀ {m'} {m/M : VarMode/TermMode ⦃ 𝕂₁ ⦄} (x/t : µ₁ ∋/⊢ m/M)
              → (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id) ≡ `/id' (wk m' x/t)
  ⋯-x/t-wk' {µ₁} {m'} {m/M} x/t =
    let sub = subst ((µ₁ ▷ m') ⊢_) (sym (ι-m→M/id m/M)) in
    `/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id           ≡⟨ sym (subst-sym' (ι-m→M/id m/M)
                                                                  (`/id' (x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id))
                                                                  (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id)
                                                                  (&/⋯-⋯ x/t (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m' id))) ⟩
    sub (`/id' (x/t &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id)) ≡⟨ cong (λ ■ → sub (`/id' ■)) (&/⋯-wk x/t) ⟩
    sub (`/id' (ι-∋/⊢ (wk m' x/t)))           ≡⟨ sym (ι-`/id' (wk m' x/t)) ⟩
    `/id' (wk m' x/t)                         ∎

  ⋯-x/t-wk : ∀ {m'} {m} (x/t : µ ∋/⊢[ 𝕂₁ ] id/m→M m)
              → (`/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id) ≡ `/id (wk m' x/t)
  ⋯-x/t-wk {µ} {m'} {m} x/t =
    let sub = subst (µ ⊢_) (id/m→M/id m) in
    let sub' = subst ((µ ▷ m') ⊢_) (id/m→M/id m) in
    `/id x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id         ≡⟨ cong (_⋯ _) (`/id≡`/id' x/t) ⟩
    sub (`/id' x/t) ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id  ≡⟨ dist-subst (_⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id) (id/m→M/id m) (`/id' x/t) ⟩
    sub' (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id) ≡⟨ cong sub' (⋯-x/t-wk' x/t) ⟩
    sub' (`/id' (wk m' x/t))               ≡⟨ sym (`/id≡`/id' (wk m' x/t)) ⟩
    `/id (wk m' x/t)                       ∎

  &/⋯-⋯' : ∀ {µ₁} {µ₂} {m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
          → let sub = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M m) in
            `/id ⦃ 𝕂₁⊔𝕂₂ ⦄ (sub (x/t &/⋯ ϕ)) ≡ `/id ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ
  &/⋯-⋯' {µ₁} {µ₂} {m} x/t ϕ =
    let sub = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M m) in
    let subx = subst (µ₂ ⊢_) (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m)) in
    let suby = subst (µ₂ ⊢_) (ι-m→M/id (id/m→M m)) in
    let subxy = subst (µ₂ ⊢_) (trans (ι-m→M/id (id/m→M m)) (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m))) in
    let subxyz = subst (µ₂ ⊢_) (trans (trans (ι-m→M/id (id/m→M m)) (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m))) (id/m→M/id m)) in
    let sub' = subst (µ₁ ⊢_) (id/m→M/id m) in
    let sub'' = subst (µ₂ ⊢_) (id/m→M/id m) in
    let sub''' = subst (µ₂ ⊢_) (id/m→M/id m) in
    `/id ⦃ 𝕂₁⊔𝕂₂ ⦄ (sub (x/t &/⋯ ϕ))           ≡⟨ `/id≡`/id' (sub (x/t &/⋯ ϕ)) ⟩
    sub'' (`/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ (sub (x/t &/⋯ ϕ)))  ≡⟨ cong sub'' (dist-subst' {F = µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_} m→M/id (`/id') (ι-id/m→M m) (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m)) (x/t &/⋯ ϕ)) ⟩
    sub'' (subx (`/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ (x/t &/⋯ ϕ))) ≡⟨ cong (λ ■ → sub'' (subx ■)) (&/⋯-⋯ x/t ϕ) ⟩
    sub'' (subx (suby (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ))) ≡⟨ cong sub'' (subst-merge (µ₂ ⊢_) _ (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m)) (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ)) ⟩
    sub'' (subxy (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ))       ≡⟨ subst-merge (µ₂ ⊢_) _ (id/m→M/id m) (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ) ⟩
    subxyz (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ)
      ≡⟨ subst-irrelevant {F = µ₂ ⊢_}
          (trans (trans (ι-m→M/id (id/m→M m)) (cong (m→M/id ⦃ 𝕂₁⊔𝕂₂ ⦄) (ι-id/m→M m))) (id/m→M/id m))
          (id/m→M/id m)
          (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ) ⟩
    sub''' (`/id' ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ)               ≡⟨ sym (dist-subst (_⋯ ϕ) (id/m→M/id m) (`/id' ⦃ 𝕂₁ ⦄ x/t)) ⟩
    sub' (`/id' ⦃ 𝕂₁ ⦄ x/t) ⋯ ϕ                ≡⟨ cong (_⋯ ϕ) (sym (`/id≡`/id' x/t)) ⟩
    `/id ⦃ 𝕂₁ ⦄ x/t ⋯ ϕ                        ∎

    -- &/⋯-⋯ : ∀ {µ₁} {µ₂} {m/M} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --         → let sub = subst (µ₂ ⊢_) (ι-m→M/id m/M) in
    --           `/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ _ (x/t &/⋯ ϕ) ≡ sub (`/id' ⦃ 𝕂₁ ⦄ _ x/t ⋯ ϕ)

    -- &/⋯-ap' : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --            → id/` ⦃ 𝕂₁ ⦄ _ x &/⋯ ϕ ~ₜ[ sym {!ι-m→M/id m!} ] & ϕ _ x

-- -- --       let sub  = subst (µ₂ ⊢_) (_⊑ₖ_.ι-m→M/id 𝕂₂⊑𝕂 m/M) in
-- -- --       sub (Kit.`/id' 𝕂₂ _ x/t ⋯ ϕ) ≡ Kit.`/id' 𝕂 _ (x/t ⋯ᶜ ϕ)

    -- tm-&/⋯-· : ∀ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --               (x/t : µ₁ ∋/⊢ m)
    --             → `/id' (& ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id (& (ϕ₁ ·ₖ ϕ₂) _ x)

    -- &/⋯-ap : ∀ {m/M} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --           → let sub = subst (µ₂ ⊢_) (ι-m→M/id m/M) in
    --             `/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ _ (x/t &/⋯ ϕ) ≡ sub (`/id' ⦃ 𝕂₁ ⦄ _ x/t ⋯ ϕ)

    -- dist-wk-· : ∀ m
    --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --             → wkₖ m (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁ ·ₖ wkₖ m ϕ₂)

    -- dist-,ₖ-·ˡ : ∀ {m}
    --                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --                (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
    --              → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
    --                ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t &/⋯ ϕ₂)) ~ ((ϕ₁ ,ₖ x/t) ·ₖ ϕ₂)

    -- dist-,ₖ-·ʳ : ∀ {m}
    --                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --                (x/t : µ₃ ∋/⊢[ 𝕂₂ ] id/m→M m)
    --              → ((ϕ₁ ·ₖ ϕ₂) ,ₖ' x/t) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ,ₖ x/t))

    -- -- dist-,ₖ-·ʳ : ∀ {m}
    -- --                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    -- --                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    -- --                (x/t : µ₃ ∋/⊢[ 𝕂₂ ] id/m→M m)
    -- --              → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
    -- --                (((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (ι-∋/⊢ x/t))) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ,ₖ x/t))

infixl  8  _&/⋯[_]_

_&/⋯[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {m/M}
            → µ₁ ∋/⊢[ 𝕂₁ ] m/M
            → (C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂)
            → µ₁ –[ 𝕂₂ ]→ µ₂
            → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode ⦃ ComposeKit.𝕂₁⊑𝕂₁⊔𝕂₂ C ⦄ m/M)
x/t &/⋯[ C ] ϕ = x/t &/⋯ ϕ where open ComposeKit C

open ComposeKit ⦃ … ⦄

~-cong-wk : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
              ⦃ Cx : ComposeKit 𝕂₁ kitᵣ 𝕂₁ ⦄
              ⦃ Cy : ComposeKit 𝕂₂ kitᵣ 𝕂₂ ⦄
              {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  wkₖ m ϕ ~ wkₖ m ϕ'
~-cong-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ C₁₂ ⦄ ⦃ C₂₁ ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
  `/id ⦃ 𝕂₁ ⦄ (x & wkₖ _ ϕ)                     ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
  `/id ⦃ 𝕂₁ ⦄ (wk _ (x & ϕ))                    ≡⟨ sym (⋯-x/t-wk (x & ϕ)) ⟩
  `/id ⦃ 𝕂₁ ⦄ (x & ϕ) ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id   ≡⟨ cong (_⋯ _) (ϕ~ϕ' mx x) ⟩
  `/id ⦃ 𝕂₂ ⦄ (x & ϕ') ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id  ≡⟨ ⋯-x/t-wk (x & ϕ') ⟩
  `/id ⦃ 𝕂₂ ⦄ (wk _ (x & ϕ'))                   ≡⟨ cong `/id (sym (&-wkₖ-wk ϕ' x)) ⟩
  `/id ⦃ 𝕂₂ ⦄ (x & wkₖ _ ϕ')                    ∎

~-cong-wk* : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
              ⦃ C₁₂ : ComposeKit 𝕂₁ kitᵣ 𝕂₁ ⦄
              ⦃ C₂₁ : ComposeKit 𝕂₂ kitᵣ 𝕂₂ ⦄
              {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  wkₖ* µ ϕ ~ wkₖ* µ ϕ'
~-cong-wk* {µ = []} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
  wkₖ* [] ϕ' ~∎
~-cong-wk* {µ = µ ▷ m} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* (µ ▷ m) ϕ    ~⟨ wkₖ*-▷ µ m ϕ ⟩
  wkₖ m (wkₖ* µ ϕ)  ~⟨ ~-cong-wk (~-cong-wk* ϕ~ϕ') ⟩
  wkₖ m (wkₖ* µ ϕ') ~⟨ ~-sym (wkₖ*-▷ µ m ϕ') ⟩
  wkₖ* (µ ▷ m) ϕ' ~∎

~-cong-↑ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
              ⦃ C₁₂ : ComposeKit 𝕂₁ kitᵣ 𝕂₁ ⦄
              ⦃ C₂₁ : ComposeKit 𝕂₂ kitᵣ 𝕂₂ ⦄
              {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑ m) ~ (ϕ' ↑ m)
~-cong-↑ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' =
  (ϕ ↑ m)                           ~⟨ ↑-,ₖ ϕ m ⟩
  (wkₖ _ ϕ  ,ₖ id/` (here refl))  ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') ~ₓ-refl ⟩
  (wkₖ _ ϕ' ,ₖ id/` (here refl))  ~⟨ ~-sym (↑-,ₖ ϕ' m) ⟩
  (ϕ' ↑ m)                          ~∎

~-cong-↑* : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
              ⦃ C₁₂ : ComposeKit 𝕂₁ kitᵣ 𝕂₁ ⦄
              ⦃ C₂₁ : ComposeKit 𝕂₂ kitᵣ 𝕂₂ ⦄
              {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑* µ) ~ (ϕ' ↑* µ)
~-cong-↑* {µ = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
  (ϕ' ↑* []) ~∎
~-cong-↑* {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* (µ ▷ m))  ~⟨ ↑*-▷ µ m ϕ ⟩
  (ϕ ↑* µ) ↑ m    ~⟨ ~-cong-↑ (~-cong-↑* ϕ~ϕ') ⟩
  (ϕ' ↑* µ) ↑ m   ~⟨ ~-sym (↑*-▷ µ m ϕ') ⟩
  (ϕ' ↑* (µ ▷ m)) ~∎

⊑ₖ-⊤ : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kit ⦄ ⦃ C : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ → 𝕂 ⊑ₖ kitₛ
⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ = record
  { ι-Mode   = m→M/id
  ; ι-id/m→M = id/m→M/id
  ; ι-m→M/id = λ m/M → refl
  ; ι-∋/⊢    = `/id'
  ; ι-id/`   = id/`/id'
  ; ι-`/id   = λ {µ} {m} x/t →
      let sub = subst (µ ⊢_) (Kit.id/m→M/id 𝕂 m) in
      `/id x/t        ≡⟨ `/id≡`/id' x/t ⟩
      sub (`/id' x/t) ∎
  ; ι-`/id'  = λ x/t → refl
  ; ι-wk     = λ {m'} {m} {µ} {m/M} x/t →
      `/id' (wk _ x/t)                  ≡⟨ sym (⋯-x/t-wk' x/t) ⟩
      `/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨⟩
      Kit.wk kitₛ _ (Kit.`/id' 𝕂 x/t)   ∎
  ; ι-∋/⊢-id = λ { refl x/t → refl }
  ; ι-∋/⊢-~ₜ = λ {µ} {m} x/t →
      let sub = subst (µ ⊢_) (id/m→M/id m) in
      sub (`/id' ⦃ 𝕂 ⦄ x/t) ≡⟨ sym (`/id≡`/id' x/t) ⟩
      `/id x/t              ∎
  ; ι-∋/⊢-~ₜ[] = λ x/t → refl
  }

-- ComposeKit for Renamings ----------------------------------------------------

-- &/⋯-wkᵣ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {mx}
--              (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
--              (x : µ₁ ∋ mx)
--            → (x & ϕ & (wkₖ ⦃ 𝕂 = 𝕂 ⦄ m id)) ≡ ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (x & ϕ))
-- &/⋯-wkᵣ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} ϕ x =
--   x & ϕ & (wkₖ _ id)                      ≡⟨ &-wkₖ-wk id (x & ϕ) ⟩
--   wk _ (x & ϕ & id)                       ≡⟨ cong (wk _) (&-id (x & ϕ)) ⟩
--   wk _ (id/` (x & ϕ))                     ≡⟨ sym (ι-wk ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ {m = m} (x & ϕ)) ⟩
--   ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (x & ϕ)) ∎

&/⋯-wkᵣ : ∀ ⦃ 𝕂 ⦄ {m'} {m} (x : µ₁ ∋ m)
          → x & wkₖ ⦃ 𝕂 = 𝕂 ⦄ m' id ≡ id/` (wk m' x)
&/⋯-wkᵣ {µ₁} ⦃ 𝕂 ⦄ {m'} {m} x =
  x & wkₖ ⦃ 𝕂 = 𝕂 ⦄ m' id ≡⟨ &-wkₖ-wk id x ⟩
  wk m' (x & id)          ≡⟨ cong (wk m') (&-id x) ⟩
  wk m' (id/` x )         ≡⟨ wk-id/` m' x ⟩
  id/` (wk m' x)          ∎

&/⋯-wkₛ : ∀ ⦃ 𝕂 ⦄
            ⦃ C : ComposeKit 𝕂 kitᵣ 𝕂 ⦄
            {m'} {M} (t : µ₁ ⊢ M)
          → t ⋯ wkₖ ⦃ 𝕂 = 𝕂 ⦄ m' id ≡ wk m' t
&/⋯-wkₛ {µ₁} ⦃ 𝕂 ⦄ {m'} {M} t =
  t ⋯ wkₖ ⦃ 𝕂 = 𝕂 ⦄ m' id    ≡⟨ ~-cong-⋯ t {!~-cong-wk!} ⟩
  t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m' id ≡⟨ {!!} ⟩
  wk m' t                    ∎

&/⋯-⋯ᵣ : ∀ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
        → let sub = subst (µ₂ ⊢_) (sym (id/m→M/id m)) in
          `/id' ⦃ 𝕂₂ ⦄ (x & ϕ) ≡ sub (` x ⋯ ϕ)
&/⋯-⋯ᵣ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} x ϕ =
  let sub = subst (µ₂ ⊢_) (id/m→M/id m) in
  let sub⁻¹ = subst (µ₂ ⊢_) (sym (id/m→M/id m)) in
  `/id' ⦃ 𝕂₂ ⦄ (x & ϕ)        ≡⟨ sym (cancel-subst (µ₂ ⊢_) (id/m→M/id m) (`/id' (x & ϕ))) ⟩
  sub⁻¹ (sub (`/id' (x & ϕ))) ≡⟨ cong sub⁻¹ (sym (`/id≡`/id' (x & ϕ))) ⟩
  sub⁻¹ (`/id ⦃ 𝕂₂ ⦄ (x & ϕ)) ≡⟨ cong sub⁻¹ (sym (⋯-var x ϕ)) ⟩
  sub⁻¹ (` x ⋯ ϕ)             ∎

&/⋯-wk-↑ᵣ : ∀ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {mx}
              (x : µ₁ ∋ mx)
              (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
            → wk _ (x & ϕ) ≡ there x & (ϕ ↑ m)
&/⋯-wk-↑ᵣ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {mx} x ϕ =
  wk _ (x & ϕ)     ≡⟨ sym (&-↑-there ϕ x) ⟩
  wk _ x & (ϕ ↑ m) ∎

ckitᵣ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitᵣ 𝕂 𝕂
ckitᵣ ⦃ 𝕂 ⦄ = record
  { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄
  ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ 𝕂 ⦄
  ; _&/⋯_      = _&_
  ; &/⋯-⋯      = &/⋯-⋯ᵣ
  ; &/⋯-&      = λ x ϕ → refl
  ; &/⋯-wk-↑   = &/⋯-wk-↑ᵣ
  ; &/⋯-wk     = &/⋯-wkᵣ
  ; ~-cong-&/⋯ = λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }
  }

-- &/⋯-wk-↑ₛ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx}
--               (t : µ₁ ⊢ mx)
--               (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
--             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
-- &/⋯-wk-↑ₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} t ϕ =
--   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
--   t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
--   t ⋯ (ϕ ↑* []) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* [])       ≡⟨⟩
--   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ []) ↑** []        ≡⟨
--     ⋯-↑ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ [])
--         ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ [])
--         (λ {µ'} x →
--           ` x ⋯ (ϕ ↑* µ') ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')           ≡⟨ cong (_⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) (⋯-var x (ϕ ↑* µ')) ⟩
--           `/id (x & (ϕ ↑* µ')) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')       ≡⟨ {!!} ⟩
--           `/id (x & (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) ⋯ ((ϕ ↑ m) ↑* µ') ≡⟨ cong (_⋯ ϕ ↑ m ↑* µ') (sym (⋯-var x (wkₖ _ id ↑* µ'))) ⟩
--           ` x ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ') ⋯ ((ϕ ↑ m) ↑* µ')      ∎
--         )
--         t ⟩
--   t ⋯* ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ []) ↑** []  ≡⟨⟩
--   t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* []) ⋯ ((ϕ ↑ m) ↑* []) ≡⟨ {!!} ⟩
--   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)                 ≡⟨ {!!} ⟩
--   wk _ t ⋯ (ϕ ↑ m)                                    ∎

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
