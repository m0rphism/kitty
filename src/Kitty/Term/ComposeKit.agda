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
open import Kitty.Term.KitOrder 𝕋 𝕊
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
  infixl  9  _·ₖ_
  infixr  9  _∘ₖ_

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

    -- ap/⋯-ap' : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
    --            → id/` ⦃ 𝕂₁ ⦄ _ x ap/⋯ ϕ ~ₜ[ sym {!ι-m→M/id m!} ] apₖ ϕ _ x

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


  -- Alternative route:
    -- (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ (wkₖ _ (ϕ ,ₖ x/t)) ~ ϕ
  -- From which then follows:
    -- wkₖ _ ϕ · ⦅ x/t ⦆ ~
    -- wkₖ _ id · ϕ · ⦅ x/t ⦆ ~
    -- ϕ · wkₖ _ id · ⦅ x/t ⦆ ~
    -- ϕ · id ~
    -- ϕ
  wk-cancels-,ₖ-· :
    ∀ {µ₁} {µ₂} {m}
      (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m)
    → (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ ϕ
  wk-cancels-,ₖ-· {µ₁} {µ₂} {m} ϕ x/t mx x =
    let sub₁ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    let sub₂ = subst (µ₂ ∋/⊢[ 𝕂₁⊔𝕂₂ ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ mx) in
    `/id _ (apₖ (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) mx x)         ≡⟨ cong (`/id _) (ap/⋯-·ₖ (wkₖ _ id) (ϕ ,ₖ x/t) x) ⟩
    `/id _ (sub₁ (apₖ (wkₖ _ id) _ x ap/⋯ (ϕ ,ₖ x/t))) ≡⟨ cong (λ ■ → `/id _ (sub₁ (■ ap/⋯ (ϕ ,ₖ x/t)))) (apₖ-wkₖ-wk id x) ⟩
    `/id _ (sub₁ (wk _ (apₖ id _ x) ap/⋯ (ϕ ,ₖ x/t)))  ≡⟨ cong (λ ■ → `/id _ (sub₁ (wk ⦃ 𝕂₁ ⦄ _ ■ ap/⋯ (ϕ ,ₖ x/t)))) (apₖ-id x) ⟩
    `/id _ (sub₁ (wk _ (id/` _ x) ap/⋯ (ϕ ,ₖ x/t)))    ≡⟨ cong (λ ■ → `/id _ (sub₁ (■ ap/⋯ (ϕ ,ₖ x/t)))) (wk-id/` _ x) ⟩
    `/id _ (sub₁ (id/` _ (there x) ap/⋯ (ϕ ,ₖ x/t)))   ≡⟨ cong (`/id _) (ap/⋯-ap (there x) (ϕ ,ₖ x/t)) ⟩
    -- `/id _ (sub₂ (ι-∋/⊢ (apₖ (ϕ ,ₖ x/t) _ (there x)))) ≡⟨ {!cong (λ ■ → sub₂ (ι-∋/⊢ ■)) (apₖ-,ₖ-there ϕ x/t x)!} ⟩
    -- `/id _ (sub₂ (ι-∋/⊢ (apₖ ϕ _ x)))                  ≡⟨ {!sym (ι-ap-→ ϕ x)!} ⟩
    -- `/id _ (apₖ ϕ mx x)                          ∎
    `/id _ (sub₂ (ι-∋/⊢ (apₖ (ϕ ,ₖ x/t) _ (there x)))) ≡⟨ cong (λ ■ → `/id _ (sub₂ (ι-∋/⊢ ■))) (apₖ-,ₖ-there ϕ x/t x) ⟩
    `/id _ (sub₂ (ι-∋/⊢ (apₖ ϕ _ x)))                  ≡⟨ cong (`/id _) (sym (ι-ap-→ ϕ x)) ⟩
    `/id _ (apₖ (ι-→ ϕ) mx x)                          ≡⟨ ι-~-→ ϕ _ x ⟩
    `/id _ (apₖ ϕ mx x)                                ∎

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
~-cong-ᵣ· ⦃ 𝕂₂ ⦄ {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' = ~'→~ (λ m x →
  apₖ (ϕ₁  ᵣ· ϕ₂ ) m x        ≡⟨⟩
  apₖ (pre ϕ₂  (apₖ ϕ₁ )) m x ≡⟨ apₖ-pre ϕ₂ (apₖ ϕ₁) x ⟩
  apₖ ϕ₂  _ (apₖ ϕ₁  m x)     ≡⟨ cong (apₖ ϕ₂ _) (~→~' ϕ₁~ϕ₁' m x) ⟩
  apₖ ϕ₂  _ (apₖ ϕ₁' m x)     ≡⟨ ~→~' ϕ₂~ϕ₂' _ (apₖ ϕ₁' m x) ⟩
  apₖ ϕ₂' _ (apₖ ϕ₁' m x)     ≡⟨ sym (apₖ-pre ϕ₂' (apₖ ϕ₁') x) ⟩
  apₖ (pre ϕ₂' (apₖ ϕ₁')) m x ≡⟨⟩
  apₖ (ϕ₁' ᵣ· ϕ₂') m x        ∎)

dist-↑-ᵣ· : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} m
               (ϕ₁ : µ₁ –[ kitᵣ ]→ µ₂)
               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
             → ((ϕ₁ ᵣ· ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ᵣ· (ϕ₂ ↑ m))
dist-↑-ᵣ· ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ = ~'→~ λ where
  mx x@(here refl) →
    apₖ ((ϕ₁ ᵣ· ϕ₂) ↑ m) _ x            ≡⟨ apₖ-↑-here (ϕ₁ ᵣ· ϕ₂) ⟩
    id/` _ (here refl)                  ≡⟨ sym (apₖ-↑-here ϕ₂) ⟩
    apₖ (ϕ₂ ↑ m) _ (here refl)          ≡⟨⟩
    apₖ (ϕ₂ ↑ m) _ (id/` _ (here refl)) ≡⟨ cong (apₖ (ϕ₂ ↑ m) _) (sym (apₖ-↑-here ϕ₁)) ⟩
    apₖ (ϕ₂ ↑ m) _ (apₖ (ϕ₁ ↑ m) _ x)   ≡⟨ sym (apₖ-pre (ϕ₂ ↑ m) (apₖ (ϕ₁ ↑ m)) x) ⟩
    apₖ ((ϕ₁ ↑ m) ᵣ· (ϕ₂ ↑ m)) _ x      ∎
  mx x@(there y) →
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
  ; _·ₖ_        = _ᵣ·_
  ; ap/⋯-·ₖ     = ap-ᵣ·
  -- ; ap/⋯-wk     = ap/⋯-wkᵣ
  ; tm-⋯-·      = tm-⋯-ᵣ·
  ; dist-↑-·    = dist-↑-ᵣ·
  ; ~-cong-·    = ~-cong-ᵣ·
  ; ~-cong-ap/⋯ = λ { refl ϕ₁~ϕ₂ → ~→~' ϕ₁~ϕ₂ _ _ }
  }
