open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)
open import Kitty.Typing.ITerms using (ITerms)
open import Kitty.Typing.CtxRepr using (CtxRepr)

module Kitty.Typing.IKit
  {𝕄 : Modes}
  {𝕋 : Terms 𝕄}
  {ℓ}
  {𝕊 : SubWithLaws 𝕋 ℓ}
  {T : Traversal 𝕋 𝕊}
  {H : KitHomotopy 𝕋 𝕊 T}
  {𝕊C : SubCompose 𝕋 𝕊 T H}
  (C : ComposeTraversal 𝕋 𝕊 T H 𝕊C)
  (KT : KitType 𝕋)
  (ℂ  : CtxRepr KT)
  (IT : ITerms C KT ℂ)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using () renaming (_∋_ to _by_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.Sub 𝕋
open Kitty.Term.Sub.SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open Kitty.Term.Traversal.Traversal T
open Kitty.Term.KitHomotopy.KitHomotopy H
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open Kitty.Term.ComposeTraversal.ComposeTraversal C
open Kitty.Typing.Types.KitType KT
open CtxRepr ℂ
open import Kitty.Typing.OPE C KT ℂ
open Kitty.Typing.ITerms C KT ℂ
open Kitty.Typing.ITerms.ITerms IT

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m
    𝕂 : Kit
    𝔸₁ : ComposeKit 𝕂 kitᵣ 𝕂
    𝔸₂ : ComposeKit kitᵣ 𝕂 𝕂
    -- WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄

record IKit
    (𝕂 : Kit)
    (K : KitT 𝕂)
    (C₁ : ComposeKit 𝕂 kitᵣ 𝕂)
    (C₂ : ComposeKit 𝕂 𝕂 𝕂)
    : Set₁ where

  infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
  infixl  6  _∋↑/⊢↑_
  -- infixl  5  _,ₖ_
  -- infixl  6  _↑_  _↑*_

  private instance _ = kitᵣ
  private instance _ = kitₛ
  private instance _ = kittᵣ
  private instance _ = kittₛ
  private instance _ = ckitᵣ
  private instance _ = 𝕂
  private instance _ = K
  private instance _ = C₁
  private instance _ = C₂

  open Kit 𝕂
  open KitT K

  field
    -- Variable/Term Typing
    _∋/⊢_∶_  : ∀ {m/M} → Ctx µ → µ ∋/⊢ m/M → µ ∶⊢ m→M/id m/M → Set

    ∋/⊢∶-lookup : ∀ {m} x → Γ ∋/⊢ id/` x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) (wk-telescope Γ x)

    -- Conditional Applications of Variable-Typing-Rule
    id/⊢`    : ∀ {x : µ ∋ m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
               → Γ ∋ x ∶ t
               →  Γ ∋/⊢ id/` x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) t
    ⊢`/id    : ∀ {e : µ ∋/⊢ id/m→M m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
               → Γ ∋/⊢ e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t
               → Γ ⊢ `/id e ∶ t
    ⊢`/id'   : ∀ {m/M} {e : µ ∋/⊢ m/M} {t : µ ∶⊢ m→M/id m/M} {Γ : Ctx µ}
               → Γ ∋/⊢ e ∶ t
               → Γ ⊢ `/id' e ∶ t

    -- Weakening preserveres variable/term typings.
    ∋wk/⊢wk  : ∀ {m/M} (Γ : Ctx µ) (t' : µ ∶⊢ m→M m) (e : µ ∋/⊢ m/M) (t : µ ∶⊢ m→M/id m/M)
               → Γ ∋/⊢ e ∶ t
               → (Γ ▶ t') ∋/⊢ wk _ e ∶ Kit.wk kitₛ _ t
    -- ⊢wk-vr : ∀ {x : µ ∋ m} {t : µ ∶⊢ M} (⊢x : Γ ∋ x ∶ t) →
    --          ⊢wk (⊢vr ⊢x) ≡ ⊢vr (there x)
    -- wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
    -- id/`/id     : ∀ x → subst (µ ⊢_) (m→m/M→M m) (tm _ (vr _ x)) ≡ ` x


    ≡ᶜ-cong-∋/⊢ : ∀ {µ m} {Γ₁ Γ₂ : Ctx µ} (x/t : µ ∋/⊢ m) {t : µ ∶⊢ m→M/id m} → 
      Γ₁ ≡ᶜ Γ₂ →
      Γ₁ ∋/⊢ x/t ∶ t →
      Γ₂ ∋/⊢ x/t ∶ t

  -- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
  -- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
  -- _∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
  -- _∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ
  -- TODO: IS THIS EQUIVALENT TO OPE?

  _∋*/⊢*_∶_ : Ctx µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
  _∋*/⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
    -- ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ◆ f _ x ∶ subst (µ₂ ∶⊢_) (sym (m→m/M→M m₁)) (wk-telescope Γ₁ x ⋯ f)
    ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ∋/⊢ (x & ϕ) ∶ subst (µ₂ ∶⊢_) (sym (id/m→M/id m₁)) (t ⋯ ϕ)

  ≡ᶜ-cong-∋*/⊢* : ∀ {µ₁ µ₂} {Γ₁ : Ctx µ₁} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {Γ₂ Γ₂' : Ctx µ₂} → 
    Γ₂ ≡ᶜ Γ₂' →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂' ∋*/⊢* ϕ ∶ Γ₁
  ≡ᶜ-cong-∋*/⊢* Γ₂≡ᶜΓ₂' ⊢ϕ = λ x t ⊢x → ≡ᶜ-cong-∋/⊢ _ Γ₂≡ᶜΓ₂' (⊢ϕ x t ⊢x)

  _∋↑/⊢↑_ : ∀ {µ₁} {µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {m} →
    Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
    (t : µ₁ ∶⊢ m→M m) →
    (Γ₂ ▶ (t ⋯ ϕ)) ∋*/⊢* (ϕ ↑ m) ∶ (Γ₁ ▶ t)
  _∋↑/⊢↑_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {m} ⊢ϕ t' (here refl) _ refl =
    let sub = subst (_∶⊢_ (µ₂ ▷ _)) (sym (id/m→M/id _)) in
    Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ here refl & (ϕ ↑ m) ∶ sub (wk-telescope (Γ₁ ▶ t') (here refl) ⋯ ϕ ↑ m)
      by subst₂ (λ ■₁ ■₂ → Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ ■₁ ∶ ■₂)
        (sym (&-↑-here ϕ))
        (sub (wk-telescope (Γ₂ ▶ (t' ⋯ ϕ)) (here refl))   ≡⟨ cong sub (wk-telescope-here Γ₂ (t' ⋯ ϕ)) ⟩
         sub (wkₛ m (t' ⋯ ϕ))                             ≡⟨ cong sub (sym (dist-↑-f t' ϕ)) ⟩
         sub (wkₛ m t' ⋯ (ϕ ↑ m))                         ≡⟨ cong sub (cong (_⋯ (ϕ ↑ m)) (sym (wk-telescope-here Γ₁ t'))) ⟩
         sub (wk-telescope (Γ₁ ▶ t') (here refl) ⋯ (ϕ ↑ m)) ∎)
        (
    Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ id/` (here refl) ∶ sub (wk-telescope (Γ₂ ▶ (t' ⋯ ϕ)) (here refl))
      by id/⊢` {x = here refl} {Γ = Γ₂ ▶ (t' ⋯ ϕ)} refl)
  _∋↑/⊢↑_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {m} ⊢ϕ t (there x) _ refl =
    let sub = subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) in
    let sub' = subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) in
    Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ (there x & ϕ ↑ _) ∶ sub (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
      by subst₂ (λ ■₁ ■₂ → (Γ₂ ▶ (t ⋯ ϕ)) ∋/⊢ ■₁ ∶ ■₂)
        (sym (&-↑-there ϕ x))
        (wkₛ _ (sub' (wk-telescope Γ₁ x ⋯ ϕ))          ≡⟨ dist-subst (_⋯ᵣ wknᵣ) _ (wk-telescope Γ₁ x ⋯ ϕ) ⟩
         sub (wkₛ _ (wk-telescope Γ₁ x ⋯ ϕ))           ≡⟨ cong sub (sym (dist-↑-f (wk-telescope Γ₁ x) ϕ)) ⟩
         sub (wkₛ _ (wk-telescope Γ₁ x) ⋯ ϕ ↑ m)       ≡⟨ cong sub (sym (cong (_⋯ ϕ ↑ m) (wk-telescope-there Γ₁ t x))) ⟩
         sub (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ m) ∎)
        (∋wk/⊢wk _ _ _ _ (⊢ϕ x _ refl))

  open CtxReprSubst 𝕊 T H

  _∋↑*/⊢↑*_ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
    ∀ {µ'} (Γ' : Ctx' µ₁ µ') →
    (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋*/⊢* (ϕ ↑* µ') ∶ (Γ₁ ▶▶ Γ')
  _∋↑*/⊢↑*_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {[]}      Γ' {m} x t ∋x =
    subst₂ (Γ₂ ∋/⊢_∶_)
           (sym (~→~' (↑*-[] ϕ) _ x))
           (cong (subst (µ₂ ∶⊢_) (sym (id/m→M/id m))) (~-cong-⋯ t (~-sym (↑*-[] ϕ))))
           (⊢ϕ x t ∋x)
  _∋↑*/⊢↑*_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {µ' ▷ m'} Γ' {.m'} (here refl) t refl =
    ≡ᶜ-cong-∋/⊢ _ (≡ᶜ-cong-▶▶ ≡ᶜ-refl (≡ᶜ-cong-⋯Ctx' ≡ᶜ-refl (↑*-[] ϕ)))
    (subst₂ (λ ■₁ ■₂ → (Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* []))) ∋/⊢ ■₁ ∶ subst (_∶⊢_ ((µ' Data.List.++ µ₂) ▷ m')) (sym (id/m→M/id m')) ■₂)
            (id/` (here refl)           ≡⟨ sym (&-↑-here (ϕ ↑* µ')) ⟩
             here refl & ϕ ↑* µ' ↑ m'   ≡⟨ sym (~→~' (↑*-▷ µ' m' ϕ) _ (here refl)) ⟩
             here refl & ϕ ↑* (µ' ▷ m') ∎)
            (wk-telescope (Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* []))) (here refl)     ≡⟨ cong (λ ■ → wk-telescope ■ (here refl)) (▶▶-↓ Γ₂ (Γ' ⋯Ctx' (ϕ ↑* []))) ⟩
             wk-telescope (Γ₂ ▶▶ ((Γ' ⋯Ctx' (ϕ ↑* [])) ↓ᶜ)
               ▶ lookup' (Γ' ⋯Ctx' (ϕ ↑* [])) (here refl)) (here refl) ≡⟨ wk-telescope-here _ _ ⟩
             lookup' (Γ' ⋯Ctx' (ϕ ↑* [])) (here refl) ⋯ᵣ wknᵣ          ≡⟨ cong (_⋯ᵣ wknᵣ) (lookup-map-Ctx' _ Γ' (here refl)) ⟩
             lookup' Γ' (here refl) ⋯ (ϕ ↑* [] ↑* µ') ⋯ᵣ wknᵣ          ≡⟨ cong (_⋯ᵣ wknᵣ) (~-cong-⋯ (lookup' Γ' (here refl)) (~-cong-↑* (↑*-[] ϕ))) ⟩
             lookup' Γ' (here refl) ⋯ (ϕ ↑* µ') ⋯ᵣ wknᵣ                ≡⟨ sym (dist-↑-f (lookup' Γ' (here refl)) (ϕ ↑* µ')) ⟩
             lookup' Γ' (here refl) ⋯ᵣ wknᵣ ⋯ ϕ ↑* µ' ↑ m'             ≡⟨ ~-cong-⋯ (lookup' Γ' (here refl) ⋯ᵣ wknᵣ) (~-sym (↑*-▷ µ' m' ϕ)) ⟩
             lookup' Γ' (here refl) ⋯ᵣ wknᵣ ⋯ ϕ ↑* (µ' ▷ m')           ≡⟨ cong (_⋯ ϕ ↑* (µ' ▷ m')) (sym (wk-telescope-here _ _)) ⟩
             wk-telescope (Γ₁ ▶▶ (Γ' ↓ᶜ)
               ▶ lookup' Γ' (here refl)) (here refl) ⋯ ϕ ↑* (µ' ▷ m')  ≡⟨ cong (λ ■ → wk-telescope ■ (here refl) ⋯ ϕ ↑* (µ' ▷ m')) (sym (▶▶-↓ Γ₁ Γ')) ⟩
             wk-telescope (Γ₁ ▶▶ Γ') (here refl) ⋯ ϕ ↑* (µ' ▷ m')      ∎)
            (id/⊢` {x = here refl} {Γ = Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* _))} refl))
  _∋↑*/⊢↑*_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {µ' ▷ m'} Γ' {m}   (there x)   t ∋x =
    let sub = subst (_∶⊢_ (µ₂ ▷▷ (µ' ▷ m'))) (sym (id/m→M/id m)) in
    let ⊢ϕ↑↑ = (Γ₂ ▶▶ (Γ' ↓ᶜ ⋯Ctx' ϕ)) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* µ') ∋*/⊢* ϕ ↑* µ' ↑ m' ∶
          (Γ₁ ▶▶ Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)
            by (⊢ϕ ∋↑*/⊢↑* (Γ' ↓ᶜ) ∋↑/⊢↑ lookup' Γ' (here refl)) in
    let ⊢ϕ↑↑' = (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋*/⊢* ϕ ↑* (µ' ▷ m') ∶ (Γ₁ ▶▶ Γ')
            by λ x t ⊢x →
              ≡ᶜ-cong-∋/⊢ _
                (~ᶜ→≡ᶜ λ m₂ x₂ →
                  lookup' (Γ₂ ▶▶ (Γ' ↓ᶜ ⋯Ctx' ϕ) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* µ')) x₂ ≡⟨ ~-cong-▶ (~-cong-▶▶ ~ᶜ-refl (dist-↓ᶜ-map _ Γ')) refl _ x₂ ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* µ')) x₂ ≡⟨ cong (λ ■ → lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ ■) x₂)
                                                                                               (sym (lookup-map-Ctx' _ Γ' (here refl))) ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ lookup' (Γ' ⋯Ctx' ϕ) (here refl)) x₂   ≡⟨ cong (λ ■ → lookup' ■ x₂) (sym (▶▶-↓ Γ₂ (Γ' ⋯Ctx' ϕ))) ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) x₂ ∎)
                (
              subst₂ ((Γ₂ ▶▶ ((Γ' ↓ᶜ) ⋯Ctx' ϕ) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* µ')) ∋/⊢_∶_)
                (~→~' (~-sym (↑*-▷ µ' m' ϕ)) _ x)
                (subst (_∶⊢_ (µ₂ ▷▷ µ' ▷ m'))   (sym (id/m→M/id _)) (t ⋯ ϕ ↑* µ' ↑ m')   ≡⟨ subst-irrelevant (sym (id/m→M/id _)) _ (t ⋯ ϕ ↑* µ' ↑ m') ⟩
                subst (_∶⊢_ (µ₂ ▷▷ (µ' ▷ m'))) (sym (id/m→M/id _)) (t ⋯ ϕ ↑* µ' ↑ m')   ≡⟨ cong (subst _ _) (~-cong-⋯ t (~-sym (↑*-▷ µ' m' ϕ))) ⟩
                subst (_∶⊢_ (µ₂ ▷▷ (µ' ▷ m'))) (sym (id/m→M/id _)) (t ⋯ ϕ ↑* (µ' ▷ m')) ∎)
                (⊢ϕ↑↑ x t (wk-telescope (Γ₁ ▶▶ Γ' ↓ᶜ ▶ lookup' Γ' (here refl)) x ≡⟨ cong (λ ■ → wk-telescope ■ x) (sym (▶▶-↓ Γ₁ Γ')) ⟩
                                                                    wk-telescope (Γ₁ ▶▶ Γ') x ≡⟨ ⊢x ⟩
                                                                    t ∎))
              )
            in
    (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋/⊢ there x & ϕ ↑* (µ' ▷ m') ∶ sub (t ⋯ ϕ ↑* (µ' ▷ m'))
      by ⊢ϕ↑↑' (there x) t ∋x  -- Γ₂∋*/⊢*ϕ ∋↑*/⊢↑* (λ x → Γ' (there x))

  _,*_ : ∀ {m} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {e : µ₂ ∋/⊢ id/m→M m} {t : µ₁ ∶⊢ m→M m} →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂ ∋/⊢   e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t ⋯ ϕ →
    Γ₂ ∋*/⊢* ϕ ,ₖ e ∶ Γ₁ ▶ t
  _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (here refl) _ refl =
    Γ₂ ∋/⊢ (here refl & ϕ ,ₖ e) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
    by subst₂ (Γ₂ ∋/⊢_∶_) (sym (&-,ₖ-here ϕ e)) (
      let sub₁ = subst (µ₁ ∶⊢_) (sym (id/m→M/id _)) in
      let sub₂ = subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) in
      begin
        sub₁ t ⋯ ϕ
      ≡⟨ sym (wk-cancels-,ₖ (subst (_ ∶⊢_) (sym (id/m→M/id _)) t) ϕ e) ⟩
        (sub₁ t) ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)
      ≡⟨ dist-subst (λ ■ → ■ ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)) (sym (id/m→M/id _)) t ⟩
        sub₂ (t ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e))
      ≡⟨ cong (λ ■ → sub₂ (■ ⋯ (ϕ ,ₖ e))) (sym (wk-telescope-here Γ₁ t)) ⟩
        sub₂ (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
      ∎
    ) ⊢e
  _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (there x) _ eq@refl =
    let sub = subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) in
    Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ sub (wk-telescope (Γ₁ ▶ t) (there x) ⋯ (ϕ ,ₖ e)) by (
    -- Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ sub (wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)) by
    subst₂ (λ ■₁ ■₂ → Γ₂ ∋/⊢ ■₁ ∶ sub ■₂)
      (sym (&-,ₖ-there ϕ e x))
      (wk-telescope Γ₁ x ⋯ ϕ                    ≡⟨ sym (wk-cancels-,ₖ (wk-telescope Γ₁ x) ϕ e) ⟩
       wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)     ≡⟨ sym (cong (_⋯ ϕ ,ₖ e) (wk-telescope-there Γ₁ t x)) ⟩
       wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ,ₖ e ∎)
    (Γ₂ ∋/⊢ x & ϕ ∶ sub (wk-telescope Γ₁ x ⋯ ϕ) by ⊢ϕ x _ refl ))

  ⊢id : ∀ {µ} {Γ : Ctx µ} → Γ ∋*/⊢* id ∶ Γ
  ⊢id {Γ = Γ} x _ refl =
    let sub = subst (_ ∶⊢_) (sym (id/m→M/id _)) in
    Γ ∋/⊢ x & id ∶ sub (wk-telescope Γ x ⋯ id)
      by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ sub ■₂)
         (sym (&-id x))
         (sym (⋯-id (wk-telescope Γ x)))
         (
    Γ ∋/⊢ id/` x ∶ sub (wk-telescope Γ x)
      by ∋/⊢∶-lookup x)

  ⊢*~ :
    ∀ {µ₁} {µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂} 
    → ϕ ~ ϕ'
    → Γ₂ ∋*/⊢* ϕ ∶ Γ₁
    → Γ₂ ∋*/⊢* ϕ' ∶ Γ₁
  ⊢*~ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {ϕ'} ϕ~ϕ' ⊢ϕ {m₁} x t ⊢x =
    let sub = subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) in
    Γ₂ ∋/⊢ (x & ϕ') ∶ sub (t ⋯ ϕ')
      by subst₂
           (λ ■₁ ■₂ → Γ₂ ∋/⊢ ■₁ ∶ sub ■₂)
           (`/id-injective (ϕ~ϕ' _ x))
           (~-cong-⋯ t ϕ~ϕ') (
    Γ₂ ∋/⊢ (x & ϕ ) ∶ sub (t ⋯ ϕ )
      by ⊢ϕ x t ⊢x)

  ⊢⦅_⦆ : ∀ {m} {Γ : Ctx µ} {t : µ ∋/⊢ id/m→M m} {T : µ ∶⊢ m→M/id (id/m→M m)}
    → Γ ∋/⊢ t ∶ T 
    → Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
  ⊢⦅_⦆ {µ} {m} {Γ} {t} {T} ⊢t =
    let ⊢t' = subst (Γ ∋/⊢ t ∶_) (sym (
                begin
                  subst
                    (µ ∶⊢_)
                    (sym (id/m→M/id _))
                    (subst (µ ∶⊢_) (id/m→M/id _) T)
                  ⋯ id
                ≡⟨ cong (_⋯ id) (cancel-subst (µ ∶⊢_) (id/m→M/id _) T) ⟩
                  T ⋯ id
                ≡⟨ ⋯-id T ⟩
                  T
                ∎
              )) ⊢t in
    Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
      by ⊢*~ (~-sym (⦅⦆-,ₖ t)) (
    Γ ∋*/⊢* (id ,ₖ t) ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
      by (⊢id ,* ⊢t')
    )

open IKit ⦃ ... ⦄

infixl  5  _∋*/⊢*[_]_∶_
_∋*/⊢*[_]_∶_ :
  ∀ {𝕂} {K : KitT 𝕂} {C₁ : ComposeKit 𝕂 kitᵣ 𝕂} {C₂ : ComposeKit 𝕂 𝕂 𝕂}
  → Ctx µ₂ → IKit 𝕂 K C₁ C₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
Γ₂ ∋*/⊢*[ IK ] f ∶ Γ₁ = Γ₂ ∋*/⊢* f ∶ Γ₁ where instance _ = IK

open Kit ⦃ ... ⦄
open ComposeKit ⦃ ... ⦄

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kittᵣ
private instance _ = kittₛ
private instance _ = ckitᵣ
private instance _ = ckitₛᵣ
private instance _ = ckitₛₛ

record ITraversal : Set (lsuc ℓ) where
  infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_

  field
    -- Substitution/Renaming preserves typing
    _⊢⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
             ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
             ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
             ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
             {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
           Γ₁ ⊢ e ∶ t →
           Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
           Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ

    -- ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
    --         (` x) ⋯ f ≡ subst (µ₂ ⊢_) (id/m→M/id m) (tm _ (f _ x))

  instance
    ikitᵣ : IKit kitᵣ kittᵣ ckitᵣ ckitᵣ
    IKit._∋/⊢_∶_ ikitᵣ = _∋_∶_
    IKit.∋/⊢∶-lookup ikitᵣ = λ _ → refl
    IKit.id/⊢`   ikitᵣ = λ ⊢x → ⊢x
    IKit.⊢`/id   ikitᵣ = ⊢`
    IKit.⊢`/id'  ikitᵣ = ⊢`
    IKit.∋wk/⊢wk ikitᵣ Γ t' x t refl = wk-telescope-there Γ t' x
    IKit.≡ᶜ-cong-∋/⊢ ikitᵣ = ≡ᶜ-cong-∋

    ikitₛ : IKit kitₛ kittₛ ckitₛᵣ ckitₛₛ
    IKit._∋/⊢_∶_ ikitₛ = _⊢_∶_
    IKit.∋/⊢∶-lookup ikitₛ = λ _ → ⊢` refl
    IKit.id/⊢`   ikitₛ = ⊢`
    IKit.⊢`/id   ikitₛ = λ ⊢t → ⊢t
    IKit.⊢`/id'  ikitₛ = λ ⊢t → ⊢t
    IKit.∋wk/⊢wk ikitₛ Γ t' x t ⊢e = ⊢e ⊢⋯ λ x₁ t₁ ⊢x₁ →
      (Γ ▶ t') ∋ (x₁ & wknᵣ) ∶ (t₁ ⋯ wknᵣ)
        by subst (λ ■ → (Γ ▶ t') ∋ ■ ∶ (t₁ ⋯ wknᵣ))
                (sym (trans (&-wkₖ-wk id x₁) (cong there (&-id x₁)))) (
      (Γ ▶ t') ∋ (there x₁) ∶ (t₁ ⋯ wknᵣ)
        by (∋wk/⊢wk Γ t' x₁ t₁ ⊢x₁))
    IKit.≡ᶜ-cong-∋/⊢ ikitₛ = λ x → ≡ᶜ-cong-⊢

  open IKit ikitᵣ public using () renaming (∋wk/⊢wk to ⊢wk; _∋↑/⊢↑_ to _∋↑_; _,*_ to _,*ᵣ_; ⊢id to ⊢idᵣ; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
  open IKit ikitₛ public using () renaming (∋wk/⊢wk to ∋wk; _∋↑/⊢↑_ to _⊢↑_; _,*_ to _,*ₛ_; ⊢id to ⊢idₛ; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

  -- Renaming preserves typing

  _⊢⋯ᵣ_ : ∀ {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ρ : µ₁ →ᵣ µ₂} →
          Γ₁ ⊢ e ∶ t →
          Γ₂ ∋* ρ ∶ Γ₁ →
          Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
  _⊢⋯ᵣ_ = _⊢⋯_

  -- Substitution preserves typing

  _⊢⋯ₛ_ : ∀ {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {σ : µ₁ →ₛ µ₂} →
          Γ₁ ⊢ e ∶ t →
          Γ₂ ⊢* σ ∶ Γ₁ →
          Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
  _⊢⋯ₛ_ = _⊢⋯_

