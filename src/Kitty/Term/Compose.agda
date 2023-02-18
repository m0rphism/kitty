open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal; KitHomotopy)
import Kitty.Term.Sub

module Kitty.Term.Compose {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (H : KitHomotopy 𝕋 T) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

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

-- If the client provides a `ComposeTraversal` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

private instance
  _ = kitᵣ
  _ = kitₛ

record ComposeKit (𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit ) : Set₁ where
  infixl  8  _ap/⋯_
  infixl  9  _·ₖ_
  infixr  9  _∘ₖ_

  private instance _ = 𝕂₁; _ = 𝕂₂; _ = 𝕂₁⊔𝕂₂

  field
    ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₁ ⊑ₖ 𝕂₁⊔𝕂₂
    ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ : 𝕂₂ ⊑ₖ 𝕂₁⊔𝕂₂

    _ap/⋯_ : ∀ {m/M}
             → µ₁ ∋/⊢[ 𝕂₁ ] m/M
             → µ₁ –[ 𝕂₂ ]→ µ₂
             → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode m/M)

    _·ₖ_ : ∀ {µ₁} {µ₂} {µ₃}
          → µ₁ –[ 𝕂₁ ]→ µ₂
          → µ₂ –[ 𝕂₂ ]→ µ₃
          → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃

    ap/⋯-·ₖ : ∀ {µ₁} {µ₂} {µ₃} {m}
                (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
                (x : µ₁ ∋ m)
              → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M m) in
                apₖ (ϕ₁ ·ₖ ϕ₂) _ x ≡ sub (apₖ ϕ₁ _ x ap/⋯ ϕ₂)

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

    -- TODO: can be derived maybe
    tm-⋯-· : ∀ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
               (x : µ₁ ∋ m)
             → `/id _ (apₖ ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id _ (apₖ (ϕ₁ ·ₖ ϕ₂) _ x)

    dist-↑-· : ∀ m
                 (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
                 (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
               → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))

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

    ~-cong-· : ∀ {ϕ₁ ϕ₁' : µ₁ –[ 𝕂₁ ]→ µ₂}
                 {ϕ₂ ϕ₂' : µ₂ –[ 𝕂₂ ]→ µ₃}
               → ϕ₁ ~ ϕ₁'
               → ϕ₂ ~ ϕ₂'
               → (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁' ·ₖ ϕ₂')

    ~-cong-ap/⋯ :
      ∀ {x/t₁ x/t₂ : µ₁ ∋/⊢[ 𝕂₁ ] (id/m→M m)}
        {ϕ₁ ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂}
      → x/t₁ ≡ x/t₂
      → ϕ₁ ~ ϕ₂
      → x/t₁ ap/⋯ ϕ₁ ≡ x/t₂ ap/⋯ ϕ₂

  _∘ₖ_ : ∀ {µ₁} {µ₂} {µ₃}
        → µ₂ –[ 𝕂₂ ]→ µ₃
        → µ₁ –[ 𝕂₁ ]→ µ₂
        → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃
  ϕ₂ ∘ₖ ϕ₁ = ϕ₁ ·ₖ ϕ₂

  -- tm-⋯-· : ∀ {µ₁} {µ₂} {µ₃} {m}
  --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --               (x : µ₁ ∋ m)
  --             → `/id _ (apₖ ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id _ (apₖ (ϕ₁ ·ₖ ϕ₂) _ x)
  -- tm-⋯-· {µ₁} {µ₂} {µ₃} {m} ϕ₁ ϕ₂ x =
  --   let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M m) in
  --   `/id _ (apₖ ϕ₁ _ x) ⋯ ϕ₂          ≡⟨ {!!} ⟩
  --   `/id _ (sub (apₖ ϕ₁ _ x ap/⋯ ϕ₂)) ≡⟨ cong (`/id _) (sym (ap/⋯-·ₖ ϕ₁ ϕ₂ x)) ⟩
  --   `/id _ (apₖ (ϕ₁ ·ₖ ϕ₂) _ x)       ∎

  dist-↑*-· : ∀ µ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃) →
    ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ~ ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ))
  dist-↑*-· []      ϕ₁ ϕ₂ =
    ((ϕ₁ ·ₖ ϕ₂) ↑* [])         ~⟨ ↑*-[] (ϕ₁ ·ₖ ϕ₂) ⟩
    ϕ₁ ·ₖ ϕ₂                   ~⟨ ~-sym (~-cong-· (↑*-[] ϕ₁) (↑*-[] ϕ₂)) ⟩
    ((ϕ₁ ↑* []) ·ₖ (ϕ₂ ↑* [])) ~∎
  dist-↑*-· (µ ▷ m) ϕ₁ ϕ₂ =
    (ϕ₁ ·ₖ ϕ₂) ↑* (µ ▷ m)               ~⟨ ↑*-▷ µ m (ϕ₁ ·ₖ ϕ₂) ⟩
    ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ↑ m               ~⟨ ~-cong-↑ (dist-↑*-· µ ϕ₁ ϕ₂) ⟩
    ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ)) ↑ m        ~⟨ dist-↑-· m (ϕ₁ ↑* µ) (ϕ₂ ↑* µ) ⟩
    ((ϕ₁ ↑* µ) ↑ m) ·ₖ ((ϕ₂ ↑* µ) ↑ m)  ~⟨ ~-sym (~-cong-· (↑*-▷ µ m ϕ₁) (↑*-▷ µ m ϕ₂)) ⟩
    (ϕ₁ ↑* (µ ▷ m)) ·ₖ (ϕ₂ ↑* (µ ▷ m))  ~∎

infixl  8  _ap/⋯[_]_
infixl  9  _·[_]_
infixr  9  _∘[_]_

_ap/⋯[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {m/M}
            → µ₁ ∋/⊢[ 𝕂₁ ] m/M
            → (C : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂)
            → µ₁ –[ 𝕂₂ ]→ µ₂
            → µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ] (ι-Mode ⦃ ComposeKit.𝕂₁⊑𝕂₁⊔𝕂₂ C ⦄ m/M)
x/t ap/⋯[ C ] ϕ = x/t ap/⋯ ϕ where open ComposeKit C

_·[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {µ₃}
         → µ₁ –[ 𝕂₁ ]→ µ₂
         → ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂
         → µ₂ –[ 𝕂₂ ]→ µ₃
         → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃
ϕ₁ ·[ C ] ϕ₂ = ϕ₁ ·ₖ ϕ₂ where open ComposeKit C


_∘[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄ {µ₁} {µ₂} {µ₃}
         → µ₂ –[ 𝕂₂ ]→ µ₃
         → ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂
         → µ₁ –[ 𝕂₁ ]→ µ₂
         → µ₁ –[ 𝕂₁⊔𝕂₂ ]→ µ₃
ϕ₂ ∘[ C ] ϕ₁ = ϕ₂ ∘ₖ ϕ₁ where open ComposeKit C

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

infixl  9  _ᵣ·_  _ᵣ·ᵣ_  _ᵣ·ₛ_
infixr  9  _∘ᵣ_  _ᵣ∘ᵣ_  _ₛ∘ᵣ_

_ᵣ·_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₃
ρ ᵣ· ϕ = pre ϕ (apₖ ⦃ 𝕂 = kitᵣ ⦄ ρ)

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

ap-ᵣ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} {m}
          (ρ : µ₁ –[ kitᵣ ]→ µ₂)
          (ϕ : µ₂ –[ 𝕂₂ ]→ µ₃)
          (x : µ₁ ∋ m)
        → apₖ (ρ ᵣ· ϕ) _ x ≡ apₖ ϕ _ (apₖ ρ _ x)
ap-ᵣ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} {m} ρ ϕ x =
  apₖ (ρ ᵣ· ϕ) _ x        ≡⟨⟩
  apₖ (pre ϕ (apₖ ρ)) _ x ≡⟨ apₖ-pre ϕ (apₖ ρ) x ⟩
  apₖ ϕ _ (apₖ ρ _ x)     ∎

~-cong-ᵣ· : ∀ ⦃ 𝕂₂ : Kit ⦄
               {ϕ₁ ϕ₁' : µ₁ –[ kitᵣ ]→ µ₂}
               {ϕ₂ ϕ₂' : µ₂ –[ 𝕂₂ ]→ µ₃}
             → ϕ₁ ~ ϕ₁'
             → ϕ₂ ~ ϕ₂'
             → (ϕ₁ ᵣ· ϕ₂) ~ (ϕ₁' ᵣ· ϕ₂')
~-cong-ᵣ· ⦃ 𝕂₂ ⦄ {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' m x =
  apₖ (ϕ₁  ᵣ· ϕ₂ ) m x        ≡⟨⟩
  apₖ (pre ϕ₂  (apₖ ϕ₁ )) m x ≡⟨ apₖ-pre ϕ₂ (apₖ ϕ₁) x ⟩
  apₖ ϕ₂  _ (apₖ ϕ₁  m x)     ≡⟨ cong (apₖ ϕ₂ _) (ϕ₁~ϕ₁' m x) ⟩
  apₖ ϕ₂  _ (apₖ ϕ₁' m x)     ≡⟨ ϕ₂~ϕ₂' _ (apₖ ϕ₁' m x) ⟩
  apₖ ϕ₂' _ (apₖ ϕ₁' m x)     ≡⟨ sym (apₖ-pre ϕ₂' (apₖ ϕ₁') x) ⟩
  apₖ (pre ϕ₂' (apₖ ϕ₁')) m x ≡⟨⟩
  apₖ (ϕ₁' ᵣ· ϕ₂') m x        ∎

dist-↑-ᵣ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} m
               (ϕ₁ : µ₁ –[ kitᵣ ]→ µ₂)
               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
             → ((ϕ₁ ᵣ· ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ᵣ· (ϕ₂ ↑ m))
dist-↑-ᵣ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(here refl) =
  apₖ ((ϕ₁ ᵣ· ϕ₂) ↑ m) _ x            ≡⟨ apₖ-↑-here (ϕ₁ ᵣ· ϕ₂) ⟩
  id/` _ (here refl)                  ≡⟨ sym (apₖ-↑-here ϕ₂) ⟩
  apₖ (ϕ₂ ↑ m) _ (here refl)          ≡⟨⟩
  apₖ (ϕ₂ ↑ m) _ (id/` _ (here refl)) ≡⟨ cong (apₖ (ϕ₂ ↑ m) _) (sym (apₖ-↑-here ϕ₁)) ⟩
  apₖ (ϕ₂ ↑ m) _ (apₖ (ϕ₁ ↑ m) _ x)   ≡⟨ sym (apₖ-pre (ϕ₂ ↑ m) (apₖ (ϕ₁ ↑ m)) x) ⟩
  apₖ ((ϕ₁ ↑ m) ᵣ· (ϕ₂ ↑ m)) _ x      ∎
dist-↑-ᵣ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(there y) =
  apₖ ((ϕ₁ ᵣ· ϕ₂) ↑ m) _ x            ≡⟨ apₖ-↑-there (ϕ₁ ᵣ· ϕ₂) y ⟩
  wk _ (apₖ (ϕ₁ ᵣ· ϕ₂) _ y)           ≡⟨ cong (wk _) (apₖ-pre ϕ₂ (apₖ ϕ₁) y) ⟩
  wk _ (apₖ ϕ₂ _ (apₖ ϕ₁ _ y))        ≡⟨ sym (apₖ-↑-there ϕ₂ (apₖ ϕ₁ _ y)) ⟩
  apₖ (ϕ₂ ↑ m) _ (there (apₖ ϕ₁ _ y)) ≡⟨⟩
  apₖ (ϕ₂ ↑ m) _ (wk _ (apₖ ϕ₁ _ y))  ≡⟨ cong (apₖ (ϕ₂ ↑ m) _) (sym (apₖ-↑-there ϕ₁ y)) ⟩
  apₖ (ϕ₂ ↑ m) _ (apₖ (ϕ₁ ↑ m) _ x)   ≡⟨ sym (apₖ-pre (ϕ₂ ↑ m) (apₖ (ϕ₁ ↑ m)) x) ⟩
  apₖ ((ϕ₁ ↑ m) ᵣ· (ϕ₂ ↑ m)) _ x      ∎

tm-⋯-ᵣ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃}
             (ϕ₁ : µ₁ –[ kitᵣ ]→ µ₂)
             (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
             (x : µ₁ ∋ m)
           → `/id _ (apₖ ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id _ (apₖ (ϕ₁ ᵣ· ϕ₂) _ x)
tm-⋯-ᵣ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} ϕ₁ ϕ₂ x =
  `/id _ (apₖ ϕ₁ _ x) ⋯ ϕ₂       ≡⟨⟩
  ` (apₖ ϕ₁ _ x) ⋯ ϕ₂            ≡⟨ ⋯-var (apₖ ϕ₁ _ x) ϕ₂ ⟩
  `/id _ (apₖ ϕ₂ _ (apₖ ϕ₁ _ x)) ≡⟨ cong (`/id _) (sym (apₖ-pre ϕ₂ (apₖ ϕ₁) x)) ⟩
  `/id _ (apₖ (ϕ₁ ᵣ· ϕ₂) _ x)    ∎

ap/⋯-wkᵣ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {mx}
             (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
             (x : µ₁ ∋ mx)
           → (apₖ (wkₖ ⦃ 𝕂 = 𝕂 ⦄ m id) _ (apₖ ϕ _ x)) ≡ ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 ⦄ ⦄ (wk _ (apₖ ϕ _ x))
ap/⋯-wkᵣ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} ϕ x =
  apₖ (wkₖ _ id) _ (apₖ ϕ _ x)            ≡⟨ apₖ-wkₖ-wk id (apₖ ϕ _ x) ⟩
  wk _ (apₖ id _ (apₖ ϕ _ x))             ≡⟨ cong (wk _) (apₖ-id (apₖ ϕ _ x)) ⟩
  wk _ (id/` _ (apₖ ϕ _ x))               ≡⟨ sym (ι-wk ⦃ ⊑ₖ-⊥ ⦃ 𝕂 ⦄ ⦄ {m = m} (apₖ ϕ _ x)) ⟩
  ι-∋/⊢ ⦃ ⊑ₖ-⊥ ⦃ 𝕂 ⦄ ⦄ (wk _ (apₖ ϕ _ x)) ∎

ckitᵣ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitᵣ 𝕂 𝕂
ckitᵣ ⦃ 𝕂 ⦄ = record
  { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊥ ⦃ 𝕂 ⦄
  ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ 𝕂 ⦄
  ; _ap/⋯_      = λ x ϕ → apₖ ϕ _ x
  ; _·ₖ_        = _ᵣ·_
  ; ap/⋯-·ₖ     = ap-ᵣ·
  -- ; ap/⋯-wk     = ap/⋯-wkᵣ
  ; tm-⋯-·      = tm-⋯-ᵣ·
  ; dist-↑-·    = dist-↑-ᵣ·
  ; ~-cong-·    = ~-cong-ᵣ·
  ; ~-cong-ap/⋯ = λ { refl ϕ₁~ϕ₂ → ϕ₁~ϕ₂ _ _ }
  }

private instance _ = ckitᵣ

-- ComposeTraversal ------------------------------------------------------------

record ComposeTraversal : Set₁ where
  open ComposeKit ⦃ … ⦄

  field
    ⋯-assoc : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit ⦄ ⦃ 𝔸 : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
                (t : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃) →
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)

  -- Example:
  --
  --   instance kit-assoc : ComposeTraversal {{traversal}}
  --   ComposeTraversal.⋯-assoc kit-assoc (` x) f g =
  --     tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  --     tm' ((g ∘ₖ f) _ x) ∎
  --   ComposeTraversal.⋯-assoc kit-assoc (λ→ e) f g = cong λ→_
  --     (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  --      e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  --      e ⋯ (g ∘ₖ f) ↑ _         ∎)
  --   ComposeTraversal.⋯-assoc kit-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

  -- ComposeKit for Substitutions ------------------------------------------------

  infixl  9  _ₛ·_  _ₛ·ᵣ_  _ₛ·ₛ_
  infixr  9  _∘ₛ_  _ᵣ∘ₛ_  _ₛ∘ₛ_

  _ₛ·_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃}
        → µ₁ –[ kitₛ ]→ µ₂
        → µ₂ –[ 𝕂₂ ]→ µ₃
        → µ₁ –[ kitₛ ]→ µ₃
  σ ₛ· ϕ = post ⦃ 𝕂 = kitₛ ⦄ σ (λ _ t → t ⋯ ϕ)

  _∘ₛ_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  ϕ₂ ∘ₛ ϕ₁ = ϕ₁ ₛ· ϕ₂

  _ₛ·ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitₛ ]→ µ₂ → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ·ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitₛ ]→ µ₂ → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  _ᵣ∘ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ∘ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ·ᵣ_ = _ₛ·_
  _ₛ·ₛ_ = _ₛ·_
  _ᵣ∘ₛ_ = _∘ₛ_
  _ₛ∘ₛ_ = _∘ₛ_

  ⋯-ₛ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} {m}
           (σ : µ₁ –[ kitₛ  ]→ µ₂)
           (ϕ : µ₂ –[ 𝕂₂ ]→ µ₃)
           (x : µ₁ ∋ m)
         → apₖ (σ ₛ· ϕ) _ x ≡ apₖ σ _ x ⋯ ϕ
  ⋯-ₛ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} {m} σ ϕ x =
    apₖ (σ ₛ· ϕ) _ x ≡⟨⟩
    apₖ (post σ (λ _ t → t ⋯ ϕ)) _ x ≡⟨ apₖ-post σ (λ _ t → t ⋯ ϕ) x ⟩
    apₖ σ _ x ⋯ ϕ    ∎

  ~-cong-ₛ· : ∀ ⦃ 𝕂₂ : Kit ⦄
                {ϕ₁ ϕ₁' : µ₁ –[ kitₛ ]→ µ₂}
                {ϕ₂ ϕ₂' : µ₂ –[ 𝕂₂ ]→ µ₃}
              → ϕ₁ ~ ϕ₁'
              → ϕ₂ ~ ϕ₂'
              → (ϕ₁ ₛ· ϕ₂) ~ (ϕ₁' ₛ· ϕ₂')
  ~-cong-ₛ· ⦃ 𝕂₂ ⦄ {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' m x =
    apₖ (ϕ₁  ₛ· ϕ₂ ) m x                 ≡⟨⟩
    apₖ (post ϕ₁ (λ _ t → t ⋯ ϕ₂)) m x   ≡⟨ apₖ-post ϕ₁ (λ _ t → t ⋯ ϕ₂) x ⟩
    apₖ ϕ₁  m x ⋯ ϕ₂                     ≡⟨ ~-cong-⋯ (apₖ ϕ₁  m x) ϕ₂~ϕ₂' ⟩
    apₖ ϕ₁  m x ⋯ ϕ₂'                    ≡⟨ cong (_⋯ ϕ₂') (ϕ₁~ϕ₁' m x) ⟩
    apₖ ϕ₁' m x ⋯ ϕ₂'                    ≡⟨ sym (apₖ-post ϕ₁' (λ _ t → t ⋯ ϕ₂') x) ⟩
    apₖ (post ϕ₁' (λ _ t → t ⋯ ϕ₂')) m x ≡⟨⟩
    apₖ (ϕ₁' ₛ· ϕ₂') m x                 ∎

  tm-⋯-ₛ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃}
              (ϕ₁ : µ₁ –[ kitₛ ]→ µ₂)
              (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
              (x : µ₁ ∋ m)
            → `/id ⦃ kitₛ ⦄ _ (apₖ ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id ⦃ kitₛ ⦄ _ (apₖ (ϕ₁ ₛ· ϕ₂) _ x)
  tm-⋯-ₛ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} ϕ₁ ϕ₂ x =
    `/id ⦃ kitₛ ⦄ _ (apₖ ϕ₁ _ x) ⋯ ϕ₂    ≡⟨⟩
    (apₖ ϕ₁ _ x) ⋯ ϕ₂                          ≡⟨ sym (apₖ-post ϕ₁ (λ _ t → t ⋯ ϕ₂) x) ⟩
    apₖ (ϕ₁ ₛ· ϕ₂) _ x                         ≡⟨⟩
    `/id ⦃ kitₛ ⦄ _ (apₖ (ϕ₁ ₛ· ϕ₂) _ x) ∎

  -- ap/⋯-wkₛ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {mx}
  --             (ϕ : µ₁ –[ kitₛ ]→ µ₂)
  --             (x : µ₁ ∋ mx)
  --           → ((apₖ ϕ _ x) ⋯ (wkₖ ⦃ 𝕂 = 𝕂 ⦄ m id)) ≡ ι-∋/⊢ ⦃ ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ kitₛ ⦄ ⦄ (wk _ (apₖ ϕ _ x))
  -- ap/⋯-wkₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} ϕ x =
  --   apₖ ϕ _ x ⋯ wkₖ ⦃ 𝕂 = 𝕂 ⦄ _ id                  ≡⟨ {!refl!} ⟩
  --   apₖ ϕ _ x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id               ≡⟨⟩
  --   wk _ (apₖ ϕ _ x)                                ≡⟨ sym (ι-wk ⦃ ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ kitₛ ⦄ ⦄ {m = m} (apₖ ϕ _ x)) ⟩
  --   ι-∋/⊢ ⦃ ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ kitₛ ⦄ ⦄ (wk _ (apₖ ϕ _ x)) ∎

  open ComposeKit ⦃ … ⦄

  record WkDistKit {𝕂₁ 𝕂₂ 𝕂 : Kit} (C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂) (C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂) : Set₁ where
    private instance _ = 𝕂₁; _ = 𝕂₂; _ = 𝕂
    field
      ↑-wk : ∀ {µ₁} {µ₂} m
              (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
            → (ϕ ·[ C₁ ] wkₖ _ id) ~ (wkₖ _ id ·[ C₂ ] (ϕ ↑ m))

  open WkDistKit ⦃ … ⦄

  apₖ-wk-↑ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {mx}
          (ϕ : µ₁ –[ 𝕂 ]→ µ₂) m
          (x : µ₁ ∋ mx)
        → apₖ (wkₖ _ id ᵣ· (ϕ ↑ m)) _ x ≡ wk _ (apₖ ϕ _ x)
  apₖ-wk-↑ {µ₁} {µ₂} ϕ m x =
    apₖ (wkₖ _ id ᵣ· (ϕ ↑ m)) _ x      ≡⟨ apₖ-pre (ϕ ↑ m) (apₖ (wkₖ _ id)) x ⟩
    apₖ (ϕ ↑ m) _ (apₖ (wkₖ _ id) _ x) ≡⟨ cong (apₖ (ϕ ↑ m) _) (apₖ-wkₖ-wk id x) ⟩
    apₖ (ϕ ↑ m) _ (there (apₖ id _ x)) ≡⟨ cong (λ ■ → apₖ (ϕ ↑ m) _ (there ■)) (apₖ-id x) ⟩
    apₖ (ϕ ↑ m) _ (there x)            ≡⟨ apₖ-↑-there ϕ x ⟩
    wk _ (apₖ ϕ _ x)                   ∎

  apₖ-wk-↑' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {mx}
          (ϕ : µ₁ –[ 𝕂 ]→ µ₂) m
          (x : µ₁ ∋ mx)
        → apₖ (wkₖ _ id ₛ· (ϕ ↑ m)) _ x ≡ `/id _ (wk _ (apₖ ϕ _ x))
  apₖ-wk-↑' {µ₁} {µ₂} ϕ m x =
    apₖ (wkₖ _ id ₛ· (ϕ ↑ m)) _ x                ≡⟨ apₖ-post (wkₖ _ id) (λ _ t → t ⋯ (ϕ ↑ m)) x ⟩
    (apₖ (wkₖ _ id) _ x) ⋯ (ϕ ↑ m)               ≡⟨ cong (_⋯ (ϕ ↑ m)) (apₖ-wkₖ-wk id x) ⟩
    wk _ (apₖ id _ x) ⋯ (ϕ ↑ m)                  ≡⟨ cong (λ ■ → wk ⦃ kitₛ ⦄ _ ■ ⋯ (ϕ ↑ m)) (apₖ-id x) ⟩
    wk _ (` x) ⋯ (ϕ ↑ m)                         ≡⟨ cong (_⋯ ϕ ↑ m) (sym (ι-wk ⦃ ⊑-ᵣₛ ⦄ {m = m} x)) ⟩
    ` there x ⋯ (ϕ ↑ m)                          ≡⟨ ⋯-var (there x) (ϕ ↑ m) ⟩
    `/id _ (apₖ (ϕ ↑ m) _ (there x))             ≡⟨ cong (`/id _) (apₖ-↑-there ϕ x) ⟩
    `/id _ (wk _ (apₖ ϕ _ x))                    ∎

  ↑-wkᵣ : ∀ {µ₁} {µ₂} m
            (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
          → (ϕ ᵣ· wkₖ _ id) ~ (wkₖ _ id ᵣ· (ϕ ↑ m))
  ↑-wkᵣ {µ₁} {µ₂} m ϕ mx x =
    apₖ (ϕ ᵣ· wkₖ _ id) _ x            ≡⟨ apₖ-pre (wkₖ _ id) (apₖ ϕ) x ⟩
    apₖ (wkₖ _ id) _ (apₖ ϕ _ x)       ≡⟨ apₖ-wkₖ-wk id (apₖ ϕ _ x) ⟩
    wk _ (apₖ id _ (apₖ ϕ _ x))        ≡⟨ cong (wk _) (apₖ-id (apₖ ϕ _ x)) ⟩
    wk _ (apₖ ϕ _ x)                   ≡⟨ sym (apₖ-wk-↑ ϕ m x) ⟩
    apₖ (wkₖ _ id ᵣ· (ϕ ↑ m)) _ x      ∎

  wkkitᵣ : WkDistKit ckitᵣ ckitᵣ
  wkkitᵣ = record { ↑-wk = ↑-wkᵣ }

  private instance _ = wkkitᵣ

  ↑-wkₛ : ∀ {µ₁} {µ₂} m
            (ϕ : µ₁ –[ kitₛ ]→ µ₂)
          → (ϕ ₛ·ᵣ wkₖ _ id) ~ (wkₖ _ id ᵣ· (ϕ ↑ m))
  ↑-wkₛ {µ₁} {µ₂} m ϕ mx x =
    apₖ (ϕ ₛ· wkₖ _ id) _ x            ≡⟨ apₖ-post ϕ (λ _ t → t ⋯ wkₖ _ id) x ⟩
    apₖ ϕ _ x ⋯ᵣ wkₖ _ id              ≡⟨⟩
    wk _ (apₖ ϕ _ x)                   ≡⟨ sym (apₖ-wk-↑ ϕ m x) ⟩
    apₖ (wkₖ _ id ᵣ· (ϕ ↑ m)) _ x      ∎

  dist-↑-·' : ∀ ⦃ 𝕂₂ : Kit ⦄ ⦃ C : ComposeKit 𝕂₂ kitᵣ 𝕂₂ ⦄ ⦃ W : WkDistKit C ckitᵣ ⦄ {µ₁} {µ₂} {µ₃} m
                (ϕ₁ : µ₁ –[ kitₛ ]→ µ₂)
                (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
              → ((ϕ₁ ₛ· ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ₛ· (ϕ₂ ↑ m))
  dist-↑-·' ⦃ 𝕂₂ ⦄ ⦃ C ⦄ ⦃ W ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(here refl) =
    apₖ ((ϕ₁ ₛ· ϕ₂) ↑ m) _ x                             ≡⟨ apₖ-↑-here (ϕ₁ ₛ· ϕ₂) ⟩
    ` here refl                                          ≡⟨ sym (id/`/id _) ⟩
    `/id ⦃ 𝕂₂ ⦄ _ (id/` _ (here refl))                   ≡⟨ cong (`/id _) (sym (apₖ-↑-here ϕ₂)) ⟩
    `/id _ (apₖ (ϕ₂ ↑ m) _ (here refl))  ≡⟨ sym (⋯-var (here refl) (ϕ₂ ↑ m)) ⟩
    (` here refl) ⋯ (ϕ₂ ↑ m)                             ≡⟨ cong (_⋯ ϕ₂ ↑ m) (sym (apₖ-↑-here ϕ₁)) ⟩
    _⋯_ ⦃ 𝕂₂ ⦄ (apₖ (ϕ₁ ↑ m) _ x) (ϕ₂ ↑ m) ≡⟨ sym (apₖ-post (ϕ₁ ↑ m) (λ _ t → t ⋯ (ϕ₂ ↑ m)) x) ⟩
    apₖ ((ϕ₁ ↑ m) ₛ· (ϕ₂ ↑ m)) _ x                       ∎
  dist-↑-·' ⦃ 𝕂₂ ⦄ ⦃ C ⦄ ⦃ W ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ mx x@(there y) =
    apₖ ((ϕ₁ ₛ· ϕ₂) ↑ m) _ x                             ≡⟨ apₖ-↑-there (ϕ₁ ₛ· ϕ₂) y ⟩
    wk _ (apₖ (ϕ₁ ₛ· ϕ₂) _ y)                            ≡⟨ cong (wk _) (apₖ-post ϕ₁ (λ _ t → t ⋯ ϕ₂) y) ⟩
    wk _ (apₖ ϕ₁ _ y ⋯ ϕ₂)                               ≡⟨⟩
    apₖ ϕ₁ _ y ⋯ ϕ₂ ⋯ᵣ wkₖ _ id                          ≡⟨ ⋯-assoc ⦃ 𝔸 = C ⦄ (apₖ ϕ₁ _ y) ϕ₂ (wkₖ _ id) ⟩
    apₖ ϕ₁ _ y ⋯ (ComposeKit._·ₖ_ C ϕ₂ (wkₖ _ id))       ≡⟨ ~-cong-⋯ (apₖ ϕ₁ _ y) (WkDistKit.↑-wk W m ϕ₂) ⟩
    apₖ ϕ₁ _ y ⋯ (_ᵣ·_ ⦃ 𝕂₂ ⦄ (wkₖ _ id) (ϕ₂ ↑ m))       ≡⟨ sym (⋯-assoc (apₖ ϕ₁ _ y) (wkₖ _ id) (ϕ₂ ↑ m)) ⟩
    apₖ ϕ₁ _ y ⋯ᵣ wkₖ _ id ⋯ (ϕ₂ ↑ m)                    ≡⟨⟩
    wk _ (apₖ ϕ₁ _ y) ⋯ (ϕ₂ ↑ m)                         ≡⟨ cong (_⋯ ϕ₂ ↑ m) (sym (apₖ-↑-there ϕ₁ y)) ⟩
    _⋯_ ⦃ 𝕂₂ ⦄ (apₖ (ϕ₁ ↑ m) _ x) (ϕ₂ ↑ m) ≡⟨ sym (apₖ-post (ϕ₁ ↑ m) (λ _ t → t ⋯ (ϕ₂ ↑ m)) x) ⟩
    apₖ ((ϕ₁ ↑ m) ₛ· (ϕ₂ ↑ m)) _ x                       ∎

  ckitₛᵣ : ComposeKit kitₛ kitᵣ kitₛ
  ckitₛᵣ = record
    { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ kitₛ ⦄ 
    ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ kitᵣ ⦄
    ; _ap/⋯_      = λ t ϕ → t ⋯ ϕ
    ; _·ₖ_        = _ₛ·_
    ; ap/⋯-·ₖ     = ⋯-ₛ·
    -- ; ap/⋯-wk     = ap/⋯-wkₛ
    ; tm-⋯-·      = tm-⋯-ₛ·
    ; dist-↑-·    = dist-↑-·' ⦃ W = wkkitᵣ ⦄
    ; ~-cong-·    = ~-cong-ₛ·
    ; ~-cong-ap/⋯ = λ { refl ϕ₁~ϕ₂ → ~-cong-⋯ _ ϕ₁~ϕ₂ }
    }

  private instance _ = ckitₛᵣ

  wkkitₛ : WkDistKit ckitₛᵣ ckitᵣ
  wkkitₛ = record { ↑-wk = ↑-wkₛ }

  private instance _ = wkkitₛ

  ckitₛₛ : ComposeKit kitₛ kitₛ kitₛ
  ckitₛₛ = record
    { 𝕂₁⊑𝕂₁⊔𝕂₂   = ⊑ₖ-refl ⦃ kitₛ ⦄ 
    ; 𝕂₂⊑𝕂₁⊔𝕂₂   = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ kitₛ ⦄
    ; _ap/⋯_      = λ t ϕ → t ⋯ ϕ
    ; _·ₖ_        = _ₛ·_
    ; ap/⋯-·ₖ     = ⋯-ₛ·
    ; tm-⋯-·      = tm-⋯-ₛ·
    ; dist-↑-·    = dist-↑-·' ⦃ W = wkkitₛ ⦄
    ; ~-cong-·    = ~-cong-ₛ·
    ; ~-cong-ap/⋯ = λ { refl ϕ₁~ϕ₂ → ~-cong-⋯ _ ϕ₁~ϕ₂ }
    }

  private instance _ = ckitₛₛ

  --------------------------------------------------------------------------------

  ↑-wkᵣₛ : ∀ {µ₁} {µ₂} m
            (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
          → (ϕ ᵣ·ₛ wkₖ _ id) ~ (wkₖ _ id ₛ·ᵣ (ϕ ↑ m))
  ↑-wkᵣₛ {µ₁} {µ₂} m ϕ mx x =
    apₖ (ϕ ᵣ· wkₖ _ id) _ x            ≡⟨ apₖ-pre (wkₖ _ id) (apₖ ϕ) x ⟩
    apₖ (wkₖ _ id) _ (apₖ ϕ _ x)       ≡⟨ apₖ-wkₖ-wk id (apₖ ϕ _ x) ⟩
    wk _ (apₖ id _ (apₖ ϕ _ x))        ≡⟨ cong (wk _) (apₖ-id (apₖ ϕ _ x)) ⟩
    wk _ (` apₖ ϕ _ x)                 ≡⟨ sym (ι-wk ⦃ ⊑-ᵣₛ ⦄ {m = m} (apₖ ϕ _ x)) ⟩
    ` there (apₖ ϕ _ x)                ≡⟨⟩
    `/id _ (wk _ (apₖ ϕ _ x))          ≡⟨ sym (apₖ-wk-↑' ϕ _ x)  ⟩
    apₖ (wkₖ _ id ₛ·ᵣ (ϕ ↑ m)) _ x      ∎

  wkkitᵣₛ : WkDistKit ckitᵣ ckitₛᵣ 
  wkkitᵣₛ = record { ↑-wk = ↑-wkᵣₛ }

  private instance _ = wkkitᵣₛ

  --------------------------------------------------------------------------------

  ↑-wkₛₛ : ∀ {µ₁} {µ₂} m
            (ϕ : µ₁ –[ kitₛ ]→ µ₂)
          → (ϕ ₛ·ₛ wkₖ _ id) ~ (wkₖ _ id ₛ·ₛ (ϕ ↑ m))
  ↑-wkₛₛ {µ₁} {µ₂} m ϕ mx x =
    apₖ (ϕ ₛ· wkₖ _ id) _ x            ≡⟨ apₖ-post ϕ (λ _ t → t ⋯ wkₖ _ id) x ⟩
    apₖ ϕ _ x ⋯ₛ wkₖ _ id              ≡⟨ ⋯-x/t-wk' ⦃ kitₛ ⦄ (apₖ ϕ _ x) ⟩
    apₖ ϕ _ x ⋯ᵣ wkₖ _ id              ≡⟨⟩
    wk _ (apₖ ϕ _ x)                   ≡⟨⟩
    `/id _ (wk _ (apₖ ϕ _ x))          ≡⟨ sym (apₖ-wk-↑' ⦃ kitₛ ⦄ ϕ _ x)  ⟩
    apₖ (wkₖ _ id ₛ·ₛ (ϕ ↑ m)) _ x     ∎

  wkkitₛₛ : WkDistKit ckitₛₛ ckitₛₛ 
  wkkitₛₛ = record { ↑-wk = ↑-wkₛₛ }

  private instance _ = wkkitᵣₛ

  --------------------------------------------------------------------------------

  ∘~∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit 𝕂₁  𝕂₂  𝕂}}
              {{𝔸' : ComposeKit 𝕂₁' 𝕂₂' 𝕂}}
              {ϕ₁  : µ₁ –[ 𝕂₁  ]→ µ₂ } {ϕ₂  : µ₂  –[ 𝕂₂  ]→ µ₃}
              {ϕ₁' : µ₁ –[ 𝕂₁' ]→ µ₂'} {ϕ₂' : µ₂' –[ 𝕂₂' ]→ µ₃} →
    (ϕ₁ ·[ 𝔸 ] ϕ₂) ~ (ϕ₁' ·[ 𝔸' ] ϕ₂') →
    ∀ {M} (t : µ₁ ⊢ M) →
    t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
  ∘~∘→⋯≡⋯ ⦃ 𝔸 = 𝔸 ⦄ ⦃ 𝔸' ⦄ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
    t ⋯ ϕ₁ ⋯ ϕ₂         ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
    t ⋯ ϕ₁  ·[ 𝔸  ] ϕ₂  ≡⟨ ~-cong-⋯ t eq ⟩
    t ⋯ ϕ₁' ·[ 𝔸' ] ϕ₂' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
    t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

-- -- record ComposeTraversal : Set₁ where

-- --   record WkDistKit
-- --       {{𝕂 : Kit}}
-- --       {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
-- --       {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
-- --       : Set₁ where
-- --     field
-- --       comm-↑-wk : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
-- --         (ϕ ↑ m) ∘ₖ wkᵣ ~ wkᵣ ∘ₖ ϕ
-- --       wk-cancels-,ₖ-∘ : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
-- --         (ϕ ,ₖ v) ∘ₖ wkᵣ ~ ϕ

-- --     -- TODO: generalize kitᵣ to arbitrary kits and include ⦅⦆ lemmas.

-- --     -- This isn't limited to renamings i.e. wkᵣ ...
-- --     dist-↑-f : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
-- --       v ⋯ᵣ wkᵣ ⋯ (ϕ ↑ m) ≡ v ⋯ ϕ ⋯ᵣ wkᵣ
-- --     dist-↑-f v ϕ =
-- --       v ⋯ wkᵣ ⋯ (ϕ ↑ _)  ≡⟨ ⋯-assoc v wk (ϕ ↑ _)  ⟩
-- --       v ⋯ (ϕ ↑ _) ∘ₖ wkᵣ ≡⟨ ~-cong-⋯ v (comm-↑-wk ϕ) ⟩
-- --       v ⋯ wkᵣ ∘ₖ ϕ       ≡⟨ sym (⋯-assoc v ϕ wk) ⟩
-- --       v ⋯ ϕ ⋯ wkᵣ        ∎

-- --     wk-cancels-,ₖ : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v' : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
-- --       v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v') ≡ v ⋯ ϕ
-- --     wk-cancels-,ₖ v ϕ v' =
-- --       v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v')   ≡⟨ ⋯-assoc v wkᵣ (ϕ ,ₖ v') ⟩
-- --       v ⋯ ((ϕ ,ₖ v') ∘ₖ wkᵣ) ≡⟨ ~-cong-⋯ _ (wk-cancels-,ₖ-∘ ϕ v') ⟩
-- --       v ⋯ ϕ                  ∎

-- --   wk-kitᵣ : WkDistKit {{kitᵣ}} {{kitᵣᵣ}} {{kitᵣᵣ}}
-- --   wk-kitᵣ = record
-- --     { comm-↑-wk = λ ϕ → ~-refl
-- --     ; wk-cancels-,ₖ-∘ = λ ϕ v → ~-refl
-- --     }

-- --   wk-kitₛ : WkDistKit {{kitₛ}} {{kitₛᵣ}} {{kitᵣₛ}}
-- --   wk-kitₛ = record
-- --     { comm-↑-wk = λ ϕ → ~-refl
-- --     ; wk-cancels-,ₖ-∘ = λ ϕ v → ~-refl
-- --     }

-- --   private instance _ = wk-kitᵣ
-- --   private instance _ = wk-kitₛ

-- --   open WkDistKit {{...}}

-- --   open WkDistKit wk-kitᵣ public renaming (dist-↑-f to dist-↑-ren; wk-cancels-,ₖ to wk-cancels-,ᵣ) using ()
-- --   open WkDistKit wk-kitₛ public renaming (dist-↑-f to dist-↑-sub; wk-cancels-,ₖ to wk-cancels-,ₛ) using ()

-- --   record ComposeTraversalLemmas : Set₁ where
-- --     open ComposeKit {{...}}

-- --     field
-- --       ⋯-id : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

-- --     ⋯-idₛ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitₛ}} ≡ v
-- --     ⋯-idₛ = ⋯-id

-- --     ⋯-idᵣ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitᵣ}} ≡ v
-- --     ⋯-idᵣ = ⋯-id

-- --     record ComposeTraversalLemmas'' : Set₁ where
-- --       field
-- --         ⋯ᶜ-id : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
-- --                   ⦃ C : ComposeKit ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                   {µ M} (v : µ ∋/⊢[ 𝕂₂ ] M)
-- --                 → v ⋯[ C ] idₖ ≡ v

-- --     ren→sub : ∀ (e : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
-- --               e ⋯ᵣ ρ ≡ e ⋯ₛ (idₛ ₛ∘ᵣ ρ)
-- --     ren→sub e ρ =
-- --       e ⋯ᵣ ρ           ≡⟨ sym (⋯-idₛ (e ⋯ᵣ ρ)) ⟩
-- --       e ⋯ᵣ ρ ⋯ₛ idₛ    ≡⟨ ⋯-assoc e ρ id/` ⟩
-- --       e ⋯ₛ (idₛ ₛ∘ᵣ ρ) ∎

-- --     ren→sub' : ∀ ⦃ 𝕂₂ 𝕂 : Kit ⦄
-- --                  ⦃ Cᵣ : ComposeKit ⦃ kitᵣ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                  ⦃ Cₛ : ComposeKit ⦃ kitₛ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                  (e : µ₁ ∋/⊢[ 𝕂₂ ] id/m→M m) (ρ : µ₁ →ᵣ µ₂) →
-- --                e ⋯[ Cᵣ ] ρ ≡ e ⋯[ Cₛ ] (idₛ ₛ∘ᵣ ρ)
-- --     ren→sub' e ρ = {!!}
-- --       -- e ⋯ᵣ ρ           ≡⟨ sym (⋯-idₛ (e ⋯ᵣ ρ)) ⟩
-- --       -- e ⋯ᵣ ρ ⋯ₛ idₛ    ≡⟨ ⋯-assoc e ρ id/` ⟩
-- --       -- e ⋯ₛ (idₛ ₛ∘ᵣ ρ) ∎

-- --     wk-cancels-⦅⦆ :
-- --       ∀ {{𝕂 : Kit}}
-- --         {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
-- --         {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
-- --         {{_ : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}} }} {µ M m}
-- --         (v : µ ⊢ M) (v' : µ ∋/⊢[ 𝕂 ] id/m→M m) →
-- --       v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡ v
-- --     wk-cancels-⦅⦆ v v' =
-- --       v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡⟨ wk-cancels-,ₖ v idₖ v' ⟩
-- --       v ⋯ idₖ          ≡⟨ ⋯-id v ⟩
-- --       v                ∎

-- --     wk-cancels-⦅⦆ᵣ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ∋ m) →
-- --       v ⋯ wkᵣ ⋯ ⦅ v' ⦆ᵣ ≡ v
-- --     wk-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

-- --     wk-cancels-⦅⦆ₛ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ⊢ m→M m) →
-- --       v ⋯ wkᵣ ⋯ ⦅ v' ⦆ₛ ≡ v
-- --     wk-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

-- --     -- TODO: prove for other combinations between ρ and σ.
-- --     ↑∘⦅⦆-is-,ₛ : ∀ {µ₁ µ₂ m} (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
-- --       ⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m) ~ σ ,ₛ t
-- --     ↑∘⦅⦆-is-,ₛ t σ _ (here refl) = ⋯-var (here refl) ⦅ t ⦆
-- --     ↑∘⦅⦆-is-,ₛ t σ _ (there x)   = wk-cancels-⦅⦆ₛ (σ _ x) t

-- --     -- TODO: prove for other combinations between ρ and σ.
-- --     ⋯↑⋯⦅⦆-is-⋯,ₛ : ∀ {µ₁ µ₂ m} (t' : (µ₁ ▷ m) ⊢ M) (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
-- --       t' ⋯ (σ ↑ m) ⋯ ⦅ t ⦆ₛ ≡ t' ⋯ (σ ,ₛ t)
-- --     ⋯↑⋯⦅⦆-is-⋯,ₛ {m = m} t' t σ =
-- --       t' ⋯ₛ (σ ↑ m) ⋯ₛ ⦅ t ⦆ₛ    ≡⟨ ⋯-assoc t' (σ ↑ m) ⦅ t ⦆ₛ ⟩
-- --       t' ⋯ₛ (⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m)) ≡⟨ ~-cong-⋯ t' (↑∘⦅⦆-is-,ₛ t σ) ⟩
-- --       t' ⋯ₛ (σ ,ₛ t)             ∎

-- --     dist-ᵣ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
-- --       ρ ᵣ∘ᵣ ⦅ x ⦆ ~ ⦅ ρ _ x ⦆ ᵣ∘ᵣ (ρ ↑ m)
-- --     dist-ᵣ∘ᵣ-⦅⦆ x σ _ (here refl) = refl
-- --     dist-ᵣ∘ᵣ-⦅⦆ x σ _ (there _)   = refl

-- --     dist-ᵣ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
-- --       ρ ᵣ∘ₛ ⦅ t ⦆ ~ ⦅ t ⋯ ρ ⦆ ₛ∘ᵣ (ρ ↑ m)
-- --     dist-ᵣ∘ₛ-⦅⦆ t σ _ (here refl) = refl
-- --     dist-ᵣ∘ₛ-⦅⦆ t σ _ (there x)   = ⋯-var x σ

-- --     dist-ₛ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
-- --       σ ₛ∘ᵣ ⦅ x ⦆ ~ ⦅ σ _ x ⦆ ₛ∘ₛ (σ ↑ m)
-- --     dist-ₛ∘ᵣ-⦅⦆ x σ _ (here refl) = sym (⋯-var (here refl) ⦅ σ _ x ⦆)
-- --     dist-ₛ∘ᵣ-⦅⦆ x σ _ (there y) =
-- --         σ _ y                             ≡⟨ sym (⋯-id (σ _ y)) ⟩
-- --         σ _ y ⋯ ((idₖ ,ₖ (σ _ x)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ y) wk ⦅ σ _ x ⦆) ⟩
-- --         (σ _ y ⋯ wk) ⋯ (idₖ ,ₖ (σ _ x))   ∎

-- --     dist-ₛ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
-- --       σ ₛ∘ₛ ⦅ t ⦆ ~ ⦅ t ⋯ σ ⦆ ₛ∘ₛ (σ ↑ m)
-- --     dist-ₛ∘ₛ-⦅⦆ t σ _ (here refl) =
-- --         t ⋯ σ                     ≡⟨⟩
-- --         ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
-- --         (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
-- --     dist-ₛ∘ₛ-⦅⦆ t σ _ (there x) =
-- --         (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
-- --         σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
-- --         σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
-- --         (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎

-- --     dist-⦅⦆ᵣ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
-- --       t ⋯ ⦅ x ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ ρ _ x ⦆
-- --     dist-⦅⦆ᵣ-⋯ᵣ t x ρ = ∘~∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ x ρ) t

-- --     dist-⦅⦆ₛ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
-- --       t ⋯ ⦅ t' ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ t' ⋯ ρ ⦆
-- --     dist-⦅⦆ₛ-⋯ᵣ t t' ρ = ∘~∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t' ρ) t

-- --     dist-⦅⦆ᵣ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
-- --       t ⋯ ⦅ x ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ σ _ x ⦆
-- --     dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘~∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

-- --     dist-⦅⦆ₛ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
-- --       t ⋯ ⦅ t' ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ t' ⋯ σ ⦆
-- --     dist-⦅⦆ₛ-⋯ₛ t₂ t σ = ∘~∘→⋯≡⋯ (dist-ₛ∘ₛ-⦅⦆ t σ) t₂

-- --     postulate TODO : ∀ {ℓ} {A : Set ℓ} → A

-- --     open import Kitty.Util.Star
-- --     open import Data.List using (_++_)

-- --     _–[_]→*_ : List VarMode → (_ : List Kit) → List VarMode → Set _
-- --     µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

-- --     infixl  6  _↑**_
-- --     _↑**_ : {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
-- --     [] ↑** µ' = []
-- --     (_∷_ {b = 𝕂} f fs) ↑** µ' = (Kit._↑*_ 𝕂 f µ') ∷ (fs ↑** µ')

-- --     infixl  5 _⋯*_
-- --     _⋯*_ : ∀ {𝕂s : List Kit} {µ₁ µ₂ M} →
-- --           µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
-- --     t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

-- --     _≈ₓ_ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
-- --     _≈ₓ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁')

-- --     _≈ₜ_ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
-- --     _≈ₜ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {M} (t : (µ₁ ▷▷ µ₁') ⊢ M) → t ⋯* (f ↑** µ₁') ≡ t ⋯* (g ↑** µ₁')

-- --     ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
-- --           f ≈ₓ g → f ≈ₜ g
-- --     ⋯-↑ = TODO

-- --     dist-⦅⦆-∘ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
-- --                   ⦃ C₂₁ : ComposeKit ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                   ⦃ C : ComposeKit ⦃ 𝕂 ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                   {µ₁ µ₂ m}
-- --                   (t' :  µ₁ ∋/⊢[ 𝕂₁ ] Kit.id/m→M 𝕂₁ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
-- --       ComposeKit._∘ₖ_ C₂₁ ϕ ⦅ t' ⦆ ~ ComposeKit._∘ₖ_ C ⦅ ComposeKit._⋯ᶜ_ C₂₁ t' ϕ ⦆ (ϕ ↑ m) 
-- --     dist-⦅⦆-∘ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t' ϕ _ (here refl) =
-- --       (ϕ ∘[ C₂₁ ] ⦅ t' ⦆) _ (here refl)                    ≡⟨ sym (ComposeKit.tm-⋯ᶜ-∘ C₂₁ ⦅ t' ⦆ ϕ (here refl) ) ⟩
-- --       ⦅ t' ⦆ _ (here refl) ⋯[ C₂₁ ] ϕ                      ≡⟨⟩
-- --       t' ⋯[ C₂₁ ] ϕ                                        ≡⟨ sym (ComposeKit.𝕂₁→𝕂₁ C refl (t' ⋯[ C₂₁ ] ϕ) ) ⟩
-- --       ComposeKit.𝕂₁→𝕂 C (t' ⋯[ C₂₁ ] ϕ)                    ≡⟨⟩
-- --       ComposeKit.𝕂₁→𝕂 C (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ _ (here refl))  ≡⟨ sym (ComposeKit.⋯ᶜ-var C (here refl) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆) ⟩
-- --       id/` _ (here refl) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆          ≡⟨⟩
-- --       (ϕ ↑ _) _ (here refl) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨ ComposeKit.tm-⋯ᶜ-∘ C (ϕ ↑ _) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆ (here refl) ⟩
-- --       (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ ∘[ C ] (ϕ ↑ _)) _ (here refl)     ∎
-- --     dist-⦅⦆-∘ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t' ϕ _ (there x) =
-- --       (ϕ ∘[ C₂₁ ] ⦅ t' ⦆) _ (there x)                    ≡⟨ sym (ComposeKit.tm-⋯ᶜ-∘ C₂₁ ⦅ t' ⦆ ϕ (there x) ) ⟩
-- --       ⦅ t' ⦆ _ (there x)  ⋯[ C₂₁ ] ϕ                      ≡⟨⟩
-- --       id/` _ x            ⋯[ C₂₁ ] ϕ                      ≡⟨ {!!} ⟩
-- --       ComposeKit.𝕂₁→𝕂 C₂₁ (ϕ _ x)                             ≡⟨ {!!} ⟩
-- --       wk _ (ϕ _ x)        ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨⟩
-- --       (ϕ ↑ _) _ (there x) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨ ComposeKit.tm-⋯ᶜ-∘ C (ϕ ↑ _) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆ (there x) ⟩
-- --       (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ ∘[ C ] (ϕ ↑ _)) _ (there x)     ∎

-- --     -- ⋯ᶜ-var : ∀ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) →
-- --     --   id/` _ x ⋯ᶜ ϕ ≡ 𝕂₁→𝕂 (ϕ _ x)

-- --     -- tm-⋯ᶜ-∘ : (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
-- --     --   (ϕ₁ _ x) ⋯ᶜ ϕ₂ ≡ (ϕ₂ ∘ₖ ϕ₁) _ x

-- --     -- dist-ₛ∘ₛ-⦅⦆ t σ _ (here refl) =
-- --     --     t ⋯ σ                     ≡⟨⟩
-- --     --     ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
-- --     --     (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
-- --     -- dist-ₛ∘ₛ-⦅⦆ t σ _ (there x) =
-- --     --     (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
-- --     --     σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
-- --     --     σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
-- --     --     (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎

-- --     dist-⦅⦆-⋯ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
-- --                   ⦃ C₂₁ : ComposeKit ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                   ⦃ C : ComposeKit ⦃ 𝕂 ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
-- --                   {µ₁ µ₂ m M}
-- --                   (t : (m ∷ µ₁) ⊢ M) (t' : Kit._∋/⊢_ 𝕂₁ µ₁ (id/m→M m)) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
-- --       t ⋯ ⦅ t' ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ ComposeKit._⋯ᶜ_ C₂₁ t' ϕ ⦆
-- --     dist-⦅⦆-⋯ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t t' ϕ =
-- --       t ⋯ ⦅ t' ⦆ ⋯ ϕ                                               ≡⟨ ⋯-assoc t ⦅ t' ⦆ ϕ ⟩
-- --       t ⋯ (ComposeKit._∘ₖ_ C₂₁ ϕ ⦅ t' ⦆)                           ≡⟨ ~-cong-⋯ t (dist-⦅⦆-∘ t' ϕ) ⟩
-- --       t ⋯ (ComposeKit._∘ₖ_ C ⦅ ComposeKit._⋯ᶜ_ C₂₁ t' ϕ ⦆ (ϕ ↑ _)) ≡⟨ sym (⋯-assoc t (ϕ ↑ _) ⦅ ComposeKit._⋯ᶜ_ C₂₁ t' ϕ ⦆) ⟩
-- --       t ⋯ (ϕ ↑ _) ⋯ ⦅ ComposeKit._⋯ᶜ_ C₂₁ t' ϕ ⦆                   ∎

-- --     dist-⦅⦆-⋯ₛ : ∀ ⦃ 𝕂 : Kit ⦄
-- --                   (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
-- --       t ⋯ ⦅ t' ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ t' ⋯ ϕ ⦆
-- --     dist-⦅⦆-⋯ₛ t t' ϕ =
-- --       t ⋯ ⦅ t' ⦆ ⋯ ϕ              ≡⟨ {!!} ⟩
-- --       -- t ⋯ (ϕ ∘ₖ ⦅ t' ⦆)           ≡⟨ {!!} ⟩
-- --       -- t ⋯ (⦅ t' ⋯ ϕ ⦆ ∘ₖ (ϕ ↑ _)) ≡⟨ {!!} ⟩
-- --       t ⋯ ϕ ↑ _ ⋯ ⦅ t' ⋯ ϕ ⦆      ∎

-- --   -- record KitTraversalLemmas : Set₁ where
-- --   --   open AssocAssumptions {{...}}
-- --   --   field
-- --   --     {{kit-traversal}} : KitTraversal
-- --   --     ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ K) → v ⋯ idₖ {{𝕂}} ≡ v

-- --   --   dist-∘-⦅⦆ :
-- --   --     ∀ {{𝕂₁ : Kit }}
-- --   --       {{𝕂₂ : Kit }}
-- --   --       {{𝕂  : Kit }}
-- --   --       {{𝔸₁ : AssocAssumptions {{kit-traversal}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
-- --   --       {{𝔸₂ : AssocAssumptions {{kit-traversal}} {{𝕂₂}} {{𝕂₁}} {{𝕂}} }}
-- --   --       {{_ : KitCompose {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{kit-traversal}} {{𝔸₁}} }}
-- --   --       {{_ : KitCompose {{𝕂₂}} {{𝕂₁}} {{𝕂}} {{kit-traversal}} {{𝔸₂}} }}
-- --   --       (t : µ ◆ k→SK k) (σ : µ₁ –[ 𝕂₁ ]→ µ₂) →
-- --   --     σ ∘ₖ ⦅ t ⦆ ≡ ⦅ `/id _ t ⋯ σ ⦆ ∘ₖ (σ ↑ k)
-- --   --   -- ⦅_⦆ : µ ◆ k→SK k → (k ∷ µ) –→ µ
-- --   --   dist-∘-⦅⦆ t σ = {!!}
-- --   --   -- dist-∘-⦅⦆ t σ = fun-ext₂ λ where
-- --   --   --   _ (here refl) →
-- --   --   --     t ⋯ σ                     ≡⟨⟩
-- --   --   --     ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
-- --   --   --     (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
-- --   --   --   _ (there x) →
-- --   --   --     (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
-- --   --   --     σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
-- --   --   --     σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
-- --   --   --     (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎
