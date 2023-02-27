open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal; KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.ComposeKit {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (H : KitHomotopy 𝕋 T) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

open import Data.List using (List; []; _∷_)
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

    &/⋯-ap : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
              → let sub₁ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
                let sub₂ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ m) in
                sub₁ (id/` x &/⋯ ϕ) ≡ sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (x & ϕ))

    &/⋯-wk-↑ : ∀ {µ₁} {µ₂} {m} {mx}
                 (x/t : µ₁ ∋/⊢[ 𝕂₁ ] mx)
                 (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
               → wk _ (x/t &/⋯ ϕ) ≡ wk _ x/t &/⋯ (ϕ ↑ m)

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

  -- dist-↑-· : ∀ {µ₁} {µ₂} {µ₃} m
  --              (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --            → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(here refl) =
  --   let sub = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --   let sub' = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in -- different ⊑-instance
  --   & ((ϕ₁ ·ₖ ϕ₂) ↑ m) _ x                  ≡⟨ &-↑-here (ϕ₁ ·ₖ ϕ₂) ⟩
  --   id/` (here refl)                        ≡⟨ {!ι-`/id!} ⟩
  --   sub' (ι-∋/⊢ (id/` (here refl)))         ≡⟨ cong (λ ■ → sub' (ι-∋/⊢ ■)) (sym (&-↑-here ϕ₂)) ⟩
  --   sub' (ι-∋/⊢ (& (ϕ₂ ↑ m) _ (here refl))) ≡⟨ sym (ι-ap-→ (ϕ₂ ↑ m) (here refl)) ⟩ -- requires 𝕂₂⊑⊔
  --   & (ι-→ (ϕ₂ ↑ m)) _(here refl)           ≡⟨ {!!} ⟩
  --   sub (id/` (here refl) &/⋯ (ϕ₂ ↑ m))    ≡⟨ {!!} ⟩
  --   sub (& (ϕ₁ ↑ m) _ x &/⋯ (ϕ₂ ↑ m))      ≡⟨ {!!} ⟩
  --   & ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)) _ x            ∎
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(there y) = {!!}

  -- dist-↑-· : ∀ {µ₁} {µ₂} {µ₃} m
  --              (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --            → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ =
  --   ((ϕ₁ ·ₖ ϕ₂) ↑ m)                                                       ~⟨ ↑-,ₖ (ϕ₁ ·ₖ ϕ₂) m ⟩
  --   (wkₖ m (ϕ₁ ·ₖ ϕ₂) ,ₖ id/` (here refl))                               ~⟨ ~-cong-,ₖ (dist-wk-· m ϕ₁ ϕ₂) refl ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ id/` (here refl))                               ~⟨ {!!} ⟩
  --   ((wkₖ m ϕ₁ ,ₖ id/` (here refl)) ·ₖ (wkₖ m ϕ₂ ,ₖ id/` (here refl))) ~⟨ ~-sym (~-cong-· (↑-,ₖ ϕ₁ m) (↑-,ₖ ϕ₂ m)) ⟩
  --   ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))                                                 ~∎
    
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ =
  --   let sub = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --   ((ϕ₁ ·ₖ ϕ₂) ↑ m)                         ~⟨ ↑-,ₖ (ϕ₁ ·ₖ ϕ₂) m ⟩
  --   (wkₖ m (ϕ₁ ·ₖ ϕ₂) ,ₖ id/` (here refl)) ~⟨ {!!} ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ id/` (here refl)) ~⟨ {!!} ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ sub ({!id/` (here refl)!} &/⋯ wkₖ m ϕ₂)) ~⟨ {!!} ⟩
  --   ((wkₖ m ϕ₁ ,ₖ id/` (here refl)) ·ₖ (wkₖ m ϕ₂ ,ₖ id/` (here refl))) ~⟨ ~-sym (~-cong-· (↑-,ₖ ϕ₁ m) (↑-,ₖ ϕ₂ m)) ⟩
  --   ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)) ~∎

  -- dist-,ₖ-· : ∀ {m}
  --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --               (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
  --             → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --               ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t &/⋯ ϕ₂)) ~ (ϕ₁ ,ₖ x/t ·ₖ ϕ₂)

-- ComposeKit for Renamings ----------------------------------------------------

&/⋯-wkᵣ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {mx}
             (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
             (x : µ₁ ∋ mx)
           → (x & ϕ & (wkₖ ⦃ 𝕂 = 𝕂 ⦄ m id)) ≡ ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (x & ϕ))
&/⋯-wkᵣ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} ϕ x =
  x & ϕ & (wkₖ _ id)                      ≡⟨ &-wkₖ-wk id (x & ϕ) ⟩
  wk _ (x & ϕ & id)                       ≡⟨ cong (wk _) (&-id (x & ϕ)) ⟩
  wk _ (id/` (x & ϕ))                     ≡⟨ sym (ι-wk ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ {m = m} (x & ϕ)) ⟩
  ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (x & ϕ)) ∎

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
  ; &/⋯-ap     = λ x ϕ → refl
  ; &/⋯-wk-↑   = &/⋯-wk-↑ᵣ
  ; ~-cong-&/⋯ = λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }
  }

open import Kitty.Util.Star
open import Kitty.Term.MultiSub 𝕋

↑**-[] : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) (x : µ₁ ∋ m)
       → (` x) ⋯* fs ↑** [] ≡ (` x) ⋯* fs
↑**-[] [] x =
  (` x) ⋯* [] ↑** [] ≡⟨⟩
  (` x) ⋯* []        ∎
↑**-[] {𝕂s = 𝕂 ∷ 𝕂s} (f ∷ fs) x =
  let instance _ = 𝕂 in
  (` x) ⋯* (f ∷ fs) ↑** []       ≡⟨⟩
  ((` x) ⋯* fs ↑** []) ⋯ f ↑* [] ≡⟨ cong (_⋯ f ↑* []) (↑**-[] fs x) ⟩
  ((` x) ⋯* fs) ⋯ f ↑* []        ≡⟨ ~-cong-⋯ _ (↑*-[] f) ⟩
  ((` x) ⋯* fs) ⋯ f              ≡⟨⟩
  (` x) ⋯* (f ∷ fs)              ∎

↑**-▷ : ∀ {𝕂s : List Kit} {µ₁} {µ₂} {µ} {m} (fs : µ₁ –[ 𝕂s ]→* µ₂) {mx} (x : µ₁ ▷▷ (µ ▷ m) ∋ mx)
      → (` x) ⋯* fs ↑** (µ ▷ m) ≡ (` x) ⋯* fs ↑** µ ↑** ([] ▷ m)
↑**-▷ {[]}     {µ₁} {µ₂} {µ} {m} []       x = refl
↑**-▷ {𝕂 ∷ 𝕂s} {µ₁} {µ₂} {µ} {m} (f ∷ fs) x =
  let instance _ = 𝕂 in
  (` x) ⋯* (f ∷ fs) ↑** (µ ▷ m)                             ≡⟨⟩
  (` x) ⋯* ((f ↑* (µ ▷ m)) ∷ (fs ↑** (µ ▷ m)))              ≡⟨⟩
  ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* (µ ▷ m))       ≡⟨ ~-cong-⋯ ((` x) ⋯* (fs ↑** (µ ▷ m))) (↑*-▷ µ m f) ⟩
  ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑ m)         ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (µ ▷ m)) (~-cong-↑ (~-sym (↑*-[] (f ↑* µ)))) ⟩
  ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑* [] ↑ m)   ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (µ ▷ m)) (~-sym (↑*-▷ [] m (f ↑* µ))) ⟩
  ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑* ([] ▷ m)) ≡⟨ cong (_⋯ f ↑* µ ↑* ([] ▷ m)) (↑**-▷ fs x) ⟩
  ((` x) ⋯* (fs ↑** µ ↑** ([] ▷ m))) ⋯ (f ↑* µ ↑* ([] ▷ m)) ≡⟨⟩
  (` x) ⋯* ((f ↑* µ ↑* ([] ▷ m)) ∷ (fs ↑** µ ↑** ([] ▷ m))) ≡⟨⟩
  (` x) ⋯* (f ∷ fs) ↑** µ ↑** ([] ▷ m)                      ∎

↑**-here : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) {µ₁'} {m} →
  (` here refl) ⋯* fs ↑** (µ₁' ▷ m) ≡ ` here refl
↑**-here {[]} {µ₁} {.µ₁} [] {µ₁'} {m} = refl
↑**-here {𝕂s ▷ 𝕂} {µ₁} {µ₂} (f ∷ fs) {µ₁'} {m} =
  let instance _ = 𝕂 in
  ` here refl ⋯* (f ∷ fs) ↑** (µ₁' ▷ m)              ≡⟨⟩
  ` here refl ⋯* (fs ↑** (µ₁' ▷ m)) ⋯ f ↑* (µ₁' ▷ m) ≡⟨ cong (_⋯ f ↑* (µ₁' ▷ m)) (↑**-here fs) ⟩
  ` here refl ⋯ f ↑* (µ₁' ▷ m)                       ≡⟨ ~-cong-⋯ (` here refl) (↑*-▷ µ₁' m f) ⟩
  ` here refl ⋯ f ↑* µ₁' ↑ m                         ≡⟨ ⋯-var (here refl) (f ↑* µ₁' ↑ m) ⟩
  `/id (here refl & f ↑* µ₁' ↑ m)                    ≡⟨ cong `/id (&-↑-here (f ↑* µ₁')) ⟩
  `/id (id/` ⦃ 𝕂 ⦄ (here refl))                      ≡⟨ id/`/id (here refl) ⟩
  ` here refl                                        ∎

↑**-there : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) {µ₁'} {m} {mx} (x : (µ₁ ▷▷ µ₁') ∋ mx) →
  ` there x ⋯* fs ↑** (µ₁' ▷ m) ≡ wkₛ m (` x ⋯* fs ↑** µ₁')
↑**-there {[]} {µ₁} {.µ₁} [] {µ₁'} {m} {mx} x =
  (` there x) ≡⟨ sym (⋯-x/t-wk'' x) ⟩
  wkₛ m (` x) ∎
↑**-there {𝕂s ▷ 𝕂} {µ₁} {µ₂} (f ∷ fs) {µ₁'} {m} {mx} x =
  let instance _ = 𝕂 in
  (` there x) ⋯* (f ∷ fs) ↑** (µ₁' ▷ m)              ≡⟨⟩
  (` there x) ⋯* (fs ↑** (µ₁' ▷ m)) ⋯ f ↑* (µ₁' ▷ m) ≡⟨ cong (_⋯ f ↑* (µ₁' ▷ m)) (↑**-there fs x) ⟩
  wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* (µ₁' ▷ m)       ≡⟨ {!!} ⟩
  wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* µ₁' ↑ m         ≡⟨ {!!} ⟩
  wkₛ m ((` x) ⋯* fs ↑** µ₁' ⋯ f ↑* µ₁')             ≡⟨⟩
  wkₛ m ((` x) ⋯* (f ∷ fs) ↑** µ₁')                  ∎

⋯-↑' : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
       → (∀ {m} (x : µ₁ ∋ m) → (` x) ⋯* f ≡ (` x) ⋯* g)
       → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁'))
⋯-↑' fs gs fs~gs {[]} x =
  (` x) ⋯* fs ↑** [] ≡⟨ ↑**-[] fs x ⟩
  (` x) ⋯* fs        ≡⟨ fs~gs x ⟩
  (` x) ⋯* gs        ≡⟨ sym (↑**-[] gs x) ⟩
  (` x) ⋯* gs ↑** [] ∎
⋯-↑' fs gs fs~gs {µ₁' ▷ m'} x@(here refl) =
  (` x) ⋯* fs ↑** (µ₁' ▷ m') ≡⟨ ↑**-here fs ⟩
  ` here refl                ≡⟨ sym (↑**-here gs) ⟩
  (` x) ⋯* gs ↑** (µ₁' ▷ m') ∎
⋯-↑' fs gs fs~gs {µ₁' ▷ m'} {m} x@(there y) =
  (` x) ⋯* fs ↑** (µ₁' ▷ m')  ≡⟨ ↑**-there fs y ⟩
  wk m' ((` y) ⋯* fs ↑** µ₁') ≡⟨ cong (wk m') (⋯-↑' fs gs fs~gs y) ⟩
  wk m' ((` y) ⋯* gs ↑** µ₁') ≡⟨ sym (↑**-there gs y) ⟩
  (` x) ⋯* gs ↑** (µ₁' ▷ m')  ∎

-- -- ⋯-↑'' : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
-- --        → (∀ {m} (x : µ₁ ∋ m) → (` x) ⋯*' f ≡ (` x) ⋯*' g)
-- --        → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯*' (f ↑** µ₁') ≡ (` x) ⋯*' (g ↑** µ₁'))
-- -- ⋯-↑'' fs gs fs~gs {[]} x =
-- --   (` x) ⋯*' fs ↑** [] ≡⟨ {!↑**-[] fs x!} ⟩
-- --   (` x) ⋯*' fs        ≡⟨ fs~gs x ⟩
-- --   (` x) ⋯*' gs        ≡⟨ {!sym (↑**-[] gs x)!} ⟩
-- --   (` x) ⋯*' gs ↑** [] ∎
-- -- ⋯-↑'' fs gs fs~gs {µ₁' ▷ m'} x@(here refl) =
-- --   (` x) ⋯*' fs ↑** (µ₁' ▷ m')        ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' fs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
-- --   ` here refl                       ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' gs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' gs ↑** (µ₁' ▷ m') ∎
-- -- ⋯-↑'' fs gs fs~gs {µ₁' ▷ m'} {m} x@(there y) =
-- --   (` x) ⋯*' fs ↑** (µ₁' ▷ m')        ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' fs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
-- --   wk m' ((` y) ⋯*' fs ↑** µ₁')       ≡⟨ cong (wk m') (⋯-↑'' fs gs fs~gs y) ⟩
-- --   wk m' ((` y) ⋯*' gs ↑** µ₁')       ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' gs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
-- --   (` x) ⋯*' gs ↑** (µ₁' ▷ m') ∎

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
--   }
