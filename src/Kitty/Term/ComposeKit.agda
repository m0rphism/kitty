open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal; KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.ComposeKit {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (H : KitHomotopy 𝕋 T) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
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

record ComposeKit (𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit ) : Set₁ where
  infixl  8  _ap/⋯_

  private instance _ = 𝕂₁; _ = 𝕂₂; _ = 𝕂₁⊔𝕂₂

  field
    ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₁ ⊑ₖ 𝕂₁⊔𝕂₂
    ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₂ ⊑ₖ 𝕂₁⊔𝕂₂

    _ap/⋯_ : ∀ {µ₁} {µ₂} {m/M}
             → µ₁ ∋/⊢[ 𝕂₁ ] m/M
             → µ₁ –[ 𝕂₂ ]→ µ₂
             → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode m/M)

    ap/⋯-⋯ : ∀ {µ₁} {µ₂} {m/M} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
            → let sub = subst (µ₂ ⊢_) (ι-m→M/id m/M) in
              `/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ _ (x/t ap/⋯ ϕ) ≡ sub (`/id' ⦃ 𝕂₁ ⦄ _ x/t ⋯ ϕ)

    ap/⋯-ap : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
              → let sub₁ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ m) in
                let sub₂ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ m) in
                sub₁ (id/` _ x ap/⋯ ϕ) ≡ sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (apₖ ϕ _ x))

    ~-cong-ap/⋯ :
      ∀ {x/t₁ x/t₂ : µ₁ ∋/⊢[ 𝕂₁ ] (id/m→M m)}
        {ϕ₁ ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ ap/⋯ ϕ₁ ≡ x/t₂ ap/⋯ ϕ₂

    -- ap/⋯-ap' : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --            → id/` ⦃ 𝕂₁ ⦄ _ x ap/⋯ ϕ ~ₜ[ sym {!ι-m→M/id m!} ] apₖ ϕ _ x

    -- ap/⋯-wk : ∀ {µ₁} {µ₂} {m} {mx}
    --             (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --             (x : µ₁ ∋ mx)
    --           → (apₖ ϕ _ x ap/⋯ wkₖ m id) ≡ ι-∋/⊢ (wk _ (apₖ ϕ _ x))

-- -- --       let sub  = subst (µ₂ ⊢_) (_⊑ₖ_.ι-m→M/id 𝕂₂⊑𝕂 m/M) in
-- -- --       sub (Kit.`/id' 𝕂₂ _ x/t ⋯ ϕ) ≡ Kit.`/id' 𝕂 _ (x/t ⋯ᶜ ϕ)

    -- tm-ap/⋯-· : ∀ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --               (x/t : µ₁ ∋/⊢ m)
    --             → `/id' _ (apₖ ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id _ (apₖ (ϕ₁ ·ₖ ϕ₂) _ x)

    -- ap/⋯-ap : ∀ {m/M} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] m/M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --           → let sub = subst (µ₂ ⊢_) (ι-m→M/id m/M) in
    --             `/id' ⦃ 𝕂₁⊔𝕂₂ ⦄ _ (x/t ap/⋯ ϕ) ≡ sub (`/id' ⦃ 𝕂₁ ⦄ _ x/t ⋯ ϕ)

    -- dist-wk-· : ∀ m
    --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --             → wkₖ m (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁ ·ₖ wkₖ m ϕ₂)

    -- dist-,ₖ-·ˡ : ∀ {m}
    --                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
    --                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    --                (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
    --              → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
    --                ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t ap/⋯ ϕ₂)) ~ ((ϕ₁ ,ₖ x/t) ·ₖ ϕ₂)

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

infixl  8  _ap/⋯[_]_

_ap/⋯[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {m/M}
            → µ₁ ∋/⊢[ 𝕂₁ ] m/M
            → (C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂)
            → µ₁ –[ 𝕂₂ ]→ µ₂
            → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode ⦃ ComposeKit.𝕂₁⊑𝕂₁⊔𝕂₂ C ⦄ m/M)
x/t ap/⋯[ C ] ϕ = x/t ap/⋯ ϕ where open ComposeKit C

  -- dist-↑-· : ∀ {µ₁} {µ₂} {µ₃} m
  --              (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --            → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(here refl) =
  --   let sub = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --   let sub' = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in -- different ⊑-instance
  --   apₖ ((ϕ₁ ·ₖ ϕ₂) ↑ m) _ x                  ≡⟨ apₖ-↑-here (ϕ₁ ·ₖ ϕ₂) ⟩
  --   id/` _ (here refl)                        ≡⟨ {!ι-`/id!} ⟩
  --   sub' (ι-∋/⊢ (id/` _ (here refl)))         ≡⟨ cong (λ ■ → sub' (ι-∋/⊢ ■)) (sym (apₖ-↑-here ϕ₂)) ⟩
  --   sub' (ι-∋/⊢ (apₖ (ϕ₂ ↑ m) _ (here refl))) ≡⟨ sym (ι-ap-→ (ϕ₂ ↑ m) (here refl)) ⟩ -- requires 𝕂₂⊑⊔
  --   apₖ (ι-→ (ϕ₂ ↑ m)) _(here refl)           ≡⟨ {!!} ⟩
  --   sub (id/` _ (here refl) ap/⋯ (ϕ₂ ↑ m))    ≡⟨ {!!} ⟩
  --   sub (apₖ (ϕ₁ ↑ m) _ x ap/⋯ (ϕ₂ ↑ m))      ≡⟨ {!!} ⟩
  --   apₖ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)) _ x            ∎
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(there y) = {!!}

  -- dist-↑-· : ∀ {µ₁} {µ₂} {µ₃} m
  --              (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --            → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ =
  --   ((ϕ₁ ·ₖ ϕ₂) ↑ m)                                                       ~⟨ ↑-,ₖ (ϕ₁ ·ₖ ϕ₂) m ⟩
  --   (wkₖ m (ϕ₁ ·ₖ ϕ₂) ,ₖ id/` _ (here refl))                               ~⟨ ~-cong-,ₖ (dist-wk-· m ϕ₁ ϕ₂) refl ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ id/` _ (here refl))                               ~⟨ {!!} ⟩
  --   ((wkₖ m ϕ₁ ,ₖ id/` _ (here refl)) ·ₖ (wkₖ m ϕ₂ ,ₖ id/` _ (here refl))) ~⟨ ~-sym (~-cong-· (↑-,ₖ ϕ₁ m) (↑-,ₖ ϕ₂ m)) ⟩
  --   ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))                                                 ~∎
    
  -- dist-↑-· {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ =
  --   let sub = subst ((µ₃ ▷ m) ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --   ((ϕ₁ ·ₖ ϕ₂) ↑ m)                         ~⟨ ↑-,ₖ (ϕ₁ ·ₖ ϕ₂) m ⟩
  --   (wkₖ m (ϕ₁ ·ₖ ϕ₂) ,ₖ id/` _ (here refl)) ~⟨ {!!} ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ id/` _ (here refl)) ~⟨ {!!} ⟩
  --   ((ϕ₁ ·ₖ wkₖ m ϕ₂) ,ₖ sub ({!id/` _ (here refl)!} ap/⋯ wkₖ m ϕ₂)) ~⟨ {!!} ⟩
  --   ((wkₖ m ϕ₁ ,ₖ id/` _ (here refl)) ·ₖ (wkₖ m ϕ₂ ,ₖ id/` _ (here refl))) ~⟨ ~-sym (~-cong-· (↑-,ₖ ϕ₁ m) (↑-,ₖ ϕ₂ m)) ⟩
  --   ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)) ~∎

  -- dist-,ₖ-· : ∀ {m}
  --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --               (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
  --             → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --               ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t ap/⋯ ϕ₂)) ~ (ϕ₁ ,ₖ x/t ·ₖ ϕ₂)

-- ComposeKit for Renamings ----------------------------------------------------

ap/⋯-wkᵣ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {mx}
             (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
             (x : µ₁ ∋ mx)
           → (apₖ (wkₖ ⦃ 𝕂 = 𝕂 ⦄ m id) _ (apₖ ϕ _ x)) ≡ ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (apₖ ϕ _ x))
ap/⋯-wkᵣ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} ϕ x =
  apₖ (wkₖ _ id) _ (apₖ ϕ _ x)            ≡⟨ apₖ-wkₖ-wk id (apₖ ϕ _ x) ⟩
  wk _ (apₖ id _ (apₖ ϕ _ x))             ≡⟨ cong (wk _) (apₖ-id (apₖ ϕ _ x)) ⟩
  wk _ (id/` _ (apₖ ϕ _ x))               ≡⟨ sym (ι-wk ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ {m = m} (apₖ ϕ _ x)) ⟩
  ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (wk _ (apₖ ϕ _ x)) ∎

ap/⋯-⋯ᵣ : ∀ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
        → let sub = subst (µ₂ ⊢_) (sym (id/m→M/id m)) in
          `/id' ⦃ 𝕂₂ ⦄ _ (apₖ ϕ _ x) ≡ sub (` x ⋯ ϕ)
ap/⋯-⋯ᵣ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} x ϕ =
  let sub = subst (µ₂ ⊢_) (id/m→M/id m) in
  let sub⁻¹ = subst (µ₂ ⊢_) (sym (id/m→M/id m)) in
  `/id' ⦃ 𝕂₂ ⦄ _ (apₖ ϕ _ x)         ≡⟨ sym (cancel-subst (µ₂ ⊢_) (id/m→M/id m) (`/id' _ (apₖ ϕ _ x))) ⟩
  sub⁻¹ (sub (`/id' _ (apₖ ϕ _ x)))  ≡⟨ cong sub⁻¹ (sym (`/id≡`/id' (apₖ ϕ _ x))) ⟩
  sub⁻¹ (`/id ⦃ 𝕂₂ ⦄ _ (apₖ ϕ _ x))  ≡⟨ cong sub⁻¹ (sym (⋯-var x ϕ)) ⟩
  sub⁻¹ (` x ⋯ ϕ)                    ∎

ckitᵣ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitᵣ 𝕂 𝕂
ckitᵣ ⦃ 𝕂 ⦄ = record
  { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊥ ⦃ 𝕂 = 𝕂 ⦄
  ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ 𝕂 ⦄
  ; _ap/⋯_      = λ x ϕ → apₖ ϕ _ x
  ; ap/⋯-⋯      = ap/⋯-⋯ᵣ
  ; ap/⋯-ap     = λ x ϕ → refl
  -- ; _·ₖ_        = _ᵣ·_
  -- ; ap/⋯-·ₖ     = ap-ᵣ·
  -- ; ap/⋯-wk     = ap/⋯-wkᵣ
  -- ; tm-⋯-·      = tm-⋯-ᵣ·
  -- ; dist-↑-·    = dist-↑-ᵣ·
  -- ; ~-cong-·    = ~-cong-ᵣ·
  ; ~-cong-ap/⋯ = λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }
  }
