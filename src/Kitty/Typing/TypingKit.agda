open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.TypeSorts using (TypeSorts)
open import Kitty.Typing.Typing using (Typing)
open import Kitty.Typing.CtxRepr using (CtxRepr)

module Kitty.Typing.TypingKit
  {𝕋 : Terms}
  {ℓ}
  {𝕊 : SubWithLaws 𝕋 ℓ}
  {T : Traversal 𝕋 𝕊}
  {H : KitHomotopy T}
  {𝕊C : SubCompose H}
  (C : ComposeTraversal 𝕊C)
  {TM : TypeSorts 𝕋}
  (ℂ  : CtxRepr TM)
  (IT : Typing C ℂ)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using () renaming (_∋_ to _by_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties
open import Kitty.Util.List

open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.Sub 𝕋
open Kitty.Term.Sub.SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open SubCompose 𝕊C
open Kitty.Term.Traversal.Traversal T
open Kitty.Term.KitHomotopy.KitHomotopy H
open import Kitty.Term.KitT T
open import Kitty.Term.ComposeKit H
open Kitty.Term.ComposeTraversal.ComposeTraversal C
open Kitty.Typing.TypeSorts.TypeSorts TM
open CtxRepr ℂ
open import Kitty.Typing.OPE C ℂ
open Kitty.Typing.Typing C ℂ
open Kitty.Typing.Typing.Typing IT

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx S
    x y z : S ∋ s
    _∋/⊢_ : VarScoped
    𝕂 : Kit _∋/⊢_
    𝔸₁ : ComposeKit 𝕂 kitᵣ 𝕂
    𝔸₂ : ComposeKit kitᵣ 𝕂 𝕂
    -- WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄

record TypingKit
    {_∋/⊢_ : VarScoped}
    (𝕂 : Kit _∋/⊢_)
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
    _∋/⊢_∶_  : Ctx S → S ∋/⊢ s → S ∶⊢ s → Set

    ∋/⊢∶-lookup : ∀ (x : S ∋ s) → Γ ∋/⊢ id/` x ∶ wk-telescope Γ x

    -- Conditional Applications of Variable-Typing-Rule
    id/⊢`    : ∀ {x : S ∋ s} {t : S ∶⊢ s} {Γ : Ctx S}
               → Γ ∋ x ∶ t
               → Γ ∋/⊢ id/` x ∶ t
    ⊢`/id    : ∀ {e : S ∋/⊢ s} {t : S ∶⊢ s} {Γ : Ctx S}
               → Γ ∋/⊢ e ∶ t
               → Γ ⊢ `/id e ∶ t

    -- Weakening preserveres variable/term typings.
    ∋wk/⊢wk  : ∀ {s/s} (Γ : Ctx S) (t' : S ∶⊢ s) (e : S ∋/⊢ s/s) (t : S ∶⊢ s/s)
               → Γ ∋/⊢ e ∶ t
               → (Γ ▶ t') ∋/⊢ wk _ e ∶ t ⋯ wknᵣ
    -- ⊢wk-vr : ∀ {x : S ∋ s} {t : S ∶⊢ s} (⊢x : Γ ∋ x ∶ t) →
    --          ⊢wk (⊢vr ⊢x) ≡ ⊢vr (there x)
    -- wk-vr     : ∀ s' (x : S ∋ s) → wk {s' = s'} _ (vr _ x) ≡ vr _ (there x)
    -- id/`/id     : ∀ x → subst (S ⊢_) (s→m/s→M s) (tm _ (vr _ x)) ≡ ` x


    ≡ᶜ-cong-∋/⊢ : ∀ {S s} {Γ₁ Γ₂ : Ctx S} (x/t : S ∋/⊢ s) {t : S ∶⊢ s} → 
      Γ₁ ≡ᶜ Γ₂ →
      Γ₁ ∋/⊢ x/t ∶ t →
      Γ₂ ∋/⊢ x/t ∶ t

  -- _⊢*_∶_ : Ctx S₂ → S₁ →ₛ S₂ → Ctx S₁ → Set
  -- _⊢*_∶_ {S₁ = S₁} Γ₂ σ Γ₁ = ∀ (x : S₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
  -- _∋*_∶_ : Ctx S₂ → S₁ →ᵣ S₂ → Ctx S₁ → Set
  -- _∋*_∶_ {S₁ = S₁} Γ₂ ρ Γ₁ = ∀ (x : S₁ ∋ 𝕖) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ
  -- TODO: IS THIS EQUIVALENT TO OPE?

  _∋*/⊢*_∶_ : Ctx S₂ → S₁ –[ 𝕂 ]→ S₂ → Ctx S₁ → Set
  _∋*/⊢*_∶_ {S₂ = S₂} {S₁ = S₁} Γ₂ ϕ Γ₁ =
    -- ∀ {s₁} → (x : S₁ ∋ s₁) → Γ₂ ◆ f _ x ∶ subst (S₂ ∶⊢_) (sym (s→m/s→M s₁)) (wk-telescope Γ₁ x ⋯ f)
    ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ∋/⊢ (x & ϕ) ∶ (t ⋯ ϕ)

  ≡ᶜ-cong-∋*/⊢* : ∀ {S₁ S₂} {Γ₁ : Ctx S₁} {ϕ : S₁ –[ 𝕂 ]→ S₂} {Γ₂ Γ₂' : Ctx S₂} → 
    Γ₂ ≡ᶜ Γ₂' →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂' ∋*/⊢* ϕ ∶ Γ₁
  ≡ᶜ-cong-∋*/⊢* Γ₂≡ᶜΓ₂' ⊢ϕ = λ x t ⊢x → ≡ᶜ-cong-∋/⊢ _ Γ₂≡ᶜΓ₂' (⊢ϕ x t ⊢x)

  _∋↑/⊢↑_ : ∀ {S₁} {S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} {s} →
    Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
    (t : S₁ ∶⊢ s) →
    (Γ₂ ▶ (t ⋯ ϕ)) ∋*/⊢* (ϕ ↑ s) ∶ (Γ₁ ▶ t)
  _∋↑/⊢↑_ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} {s} ⊢ϕ t' (here refl) _ refl =
    Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ here refl & (ϕ ↑ s) ∶ (wk-telescope (Γ₁ ▶ t') (here refl) ⋯ ϕ ↑ s)
      by subst₂ (λ ■₁ ■₂ → Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ ■₁ ∶ ■₂)
        (sym (&-↑-here ϕ))
        (wk-telescope (Γ₂ ▶ (t' ⋯ ϕ)) (here refl)    ≡⟨ wk-telescope-here Γ₂ (t' ⋯ ϕ) ⟩
         t' ⋯ ϕ ⋯ wknᵣ                                ≡⟨ sym (dist-↑-f t' ϕ) ⟩
         t' ⋯ wknᵣ ⋯ (ϕ ↑ s)                          ≡⟨ cong (_⋯ (ϕ ↑ s)) (sym (wk-telescope-here Γ₁ t')) ⟩
         wk-telescope (Γ₁ ▶ t') (here refl) ⋯ (ϕ ↑ s) ∎)
        (
    Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ id/` (here refl) ∶ wk-telescope (Γ₂ ▶ (t' ⋯ ϕ)) (here refl)
      by id/⊢` {x = here refl} {Γ = Γ₂ ▶ (t' ⋯ ϕ)} refl)
  _∋↑/⊢↑_ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} {s} ⊢ϕ t (there x) _ refl =
    Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ (there x & ϕ ↑ _) ∶ (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
      by subst₂ (λ ■₁ ■₂ → (Γ₂ ▶ (t ⋯ ϕ)) ∋/⊢ ■₁ ∶ ■₂)
        (sym (&-↑-there ϕ x))
        (wk-telescope Γ₁ x ⋯ ϕ ⋯ wknᵣ            ≡⟨ sym (dist-↑-f (wk-telescope Γ₁ x) ϕ) ⟩
         wk-telescope Γ₁ x ⋯ wknᵣ ⋯ ϕ ↑ s        ≡⟨ sym (cong (_⋯ ϕ ↑ s) (wk-telescope-there Γ₁ t x)) ⟩
         wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ s ∎)
        (∋wk/⊢wk _ _ _ _ (⊢ϕ x _ refl))

  open CtxReprSubst 𝕊 T H public

  _∋↑*/⊢↑*_ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
    Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
    ∀ {S'} (Γ' : Ctx' S₁ S') →
    (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋*/⊢* (ϕ ↑* S') ∶ (Γ₁ ▶▶ Γ')
  _∋↑*/⊢↑*_ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {[]}      Γ' {s} x t ∋x =
    subst₂ (Γ₂ ∋/⊢_∶_)
           (sym (use-~-hom (↑*-[] ϕ) _ x))
           (~-cong-⋯ t (~-sym (↑*-[] ϕ)))
           (⊢ϕ x t ∋x)
  _∋↑*/⊢↑*_ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {S' ▷ s'} Γ' {.s'} (here refl) t refl =
    ≡ᶜ-cong-∋/⊢ _ (≡ᶜ-cong-▶▶ ≡ᶜ-refl (≡ᶜ-cong-⋯Ctx' ≡ᶜ-refl (↑*-[] ϕ)))
    (subst₂ (λ ■₁ ■₂ → (Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* []))) ∋/⊢ ■₁ ∶ ■₂)
            (id/` (here refl)           ≡⟨ sym (&-↑-here (ϕ ↑* S')) ⟩
             here refl & ϕ ↑* S' ↑ s'   ≡⟨ sym (use-~-hom (↑*-▷ S' s' ϕ) _ (here refl)) ⟩
             here refl & ϕ ↑* (S' ▷ s') ∎)
            (wk-telescope (Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* []))) (here refl)     ≡⟨ cong (λ ■ → wk-telescope ■ (here refl)) (▶▶-↓ Γ₂ (Γ' ⋯Ctx' (ϕ ↑* []))) ⟩
             wk-telescope (Γ₂ ▶▶ ((Γ' ⋯Ctx' (ϕ ↑* [])) ↓ᶜ)
               ▶ lookup' (Γ' ⋯Ctx' (ϕ ↑* [])) (here refl)) (here refl) ≡⟨ wk-telescope-here _ _ ⟩
             lookup' (Γ' ⋯Ctx' (ϕ ↑* [])) (here refl) ⋯ᵣ wknᵣ          ≡⟨ cong (_⋯ᵣ wknᵣ) (lookup-map-Ctx' _ Γ' (here refl)) ⟩
             lookup' Γ' (here refl) ⋯ (ϕ ↑* [] ↑* S') ⋯ᵣ wknᵣ          ≡⟨ cong (_⋯ᵣ wknᵣ) (~-cong-⋯ (lookup' Γ' (here refl)) (~-cong-↑* (↑*-[] ϕ))) ⟩
             lookup' Γ' (here refl) ⋯ (ϕ ↑* S') ⋯ᵣ wknᵣ                ≡⟨ sym (dist-↑-f (lookup' Γ' (here refl)) (ϕ ↑* S')) ⟩
             lookup' Γ' (here refl) ⋯ᵣ wknᵣ ⋯ ϕ ↑* S' ↑ s'             ≡⟨ ~-cong-⋯ (lookup' Γ' (here refl) ⋯ᵣ wknᵣ) (~-sym (↑*-▷ S' s' ϕ)) ⟩
             lookup' Γ' (here refl) ⋯ᵣ wknᵣ ⋯ ϕ ↑* (S' ▷ s')           ≡⟨ cong (_⋯ ϕ ↑* (S' ▷ s')) (sym (wk-telescope-here _ _)) ⟩
             wk-telescope (Γ₁ ▶▶ (Γ' ↓ᶜ)
               ▶ lookup' Γ' (here refl)) (here refl) ⋯ ϕ ↑* (S' ▷ s')  ≡⟨ cong (λ ■ → wk-telescope ■ (here refl) ⋯ ϕ ↑* (S' ▷ s')) (sym (▶▶-↓ Γ₁ Γ')) ⟩
             wk-telescope (Γ₁ ▶▶ Γ') (here refl) ⋯ ϕ ↑* (S' ▷ s')      ∎)
            (id/⊢` {x = here refl} {Γ = Γ₂ ▶▶ (Γ' ⋯Ctx' (ϕ ↑* _))} refl))
  _∋↑*/⊢↑*_ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {S' ▷ s'} Γ' {s}   (there x)   t ∋x =
    let ⊢ϕ↑↑ = (Γ₂ ▶▶ (Γ' ↓ᶜ ⋯Ctx' ϕ)) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* S') ∋*/⊢* ϕ ↑* S' ↑ s' ∶
          (Γ₁ ▶▶ Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)
            by (⊢ϕ ∋↑*/⊢↑* (Γ' ↓ᶜ) ∋↑/⊢↑ lookup' Γ' (here refl)) in
    let ⊢ϕ↑↑' = (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋*/⊢* ϕ ↑* (S' ▷ s') ∶ (Γ₁ ▶▶ Γ')
            by λ x t ⊢x →
              ≡ᶜ-cong-∋/⊢ _
                (~ᶜ→≡ᶜ λ s₂ x₂ →
                  lookup' (Γ₂ ▶▶ (Γ' ↓ᶜ ⋯Ctx' ϕ) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* S')) x₂ ≡⟨ ~-cong-▶ (~-cong-▶▶ ~ᶜ-refl (dist-↓ᶜ-map _ Γ')) refl _ x₂ ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* S')) x₂ ≡⟨ cong (λ ■ → lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ ■) x₂)
                                                                                               (sym (lookup-map-Ctx' _ Γ' (here refl))) ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ) ↓ᶜ ▶ lookup' (Γ' ⋯Ctx' ϕ) (here refl)) x₂   ≡⟨ cong (λ ■ → lookup' ■ x₂) (sym (▶▶-↓ Γ₂ (Γ' ⋯Ctx' ϕ))) ⟩
                  lookup' (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) x₂ ∎)
                (
              subst₂ ((Γ₂ ▶▶ ((Γ' ↓ᶜ) ⋯Ctx' ϕ) ▶ (lookup' Γ' (here refl) ⋯ ϕ ↑* S')) ∋/⊢_∶_)
                (use-~-hom (~-sym (↑*-▷ S' s' ϕ)) _ x)
                (t ⋯ ϕ ↑* S' ↑ s'   ≡⟨ ~-cong-⋯ t (~-sym (↑*-▷ S' s' ϕ)) ⟩
                 t ⋯ ϕ ↑* (S' ▷ s') ∎)
                (⊢ϕ↑↑ x t (wk-telescope (Γ₁ ▶▶ Γ' ↓ᶜ ▶ lookup' Γ' (here refl)) x ≡⟨ cong (λ ■ → wk-telescope ■ x) (sym (▶▶-↓ Γ₁ Γ')) ⟩
                                                                    wk-telescope (Γ₁ ▶▶ Γ') x ≡⟨ ⊢x ⟩
                                                                    t ∎))
              )
            in
    (Γ₂ ▶▶ (Γ' ⋯Ctx' ϕ)) ∋/⊢ there x & ϕ ↑* (S' ▷ s') ∶ (t ⋯ ϕ ↑* (S' ▷ s'))
      by ⊢ϕ↑↑' (there x) t ∋x  -- Γ₂∋*/⊢*ϕ ∋↑*/⊢↑* (λ x → Γ' (there x))

  _,*_ : ∀ {s} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} {e : S₂ ∋/⊢ s} {t : S₁ ∶⊢ s} →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂ ∋/⊢   e ∶ t ⋯ ϕ →
    Γ₂ ∋*/⊢* ϕ ,ₖ e ∶ Γ₁ ▶ t
  _,*_ {S₁ = S₁} {S₂ = S₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (here refl) _ refl =
    Γ₂ ∋/⊢ (here refl & ϕ ,ₖ e) ∶ (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
    by subst₂ (Γ₂ ∋/⊢_∶_) (sym (&-,ₖ-here ϕ e)) (
      begin
        t ⋯ ϕ
      ≡⟨ sym (wk-cancels-,ₖ t ϕ e) ⟩
        t ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)
      ≡⟨ cong (λ ■ → ■ ⋯ (ϕ ,ₖ e)) (sym (wk-telescope-here Γ₁ t)) ⟩
        wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e)
      ∎
    ) ⊢e
  _,*_ {S₁ = S₁} {S₂ = S₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (there x) _ eq@refl =
    Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ (wk-telescope (Γ₁ ▶ t) (there x) ⋯ (ϕ ,ₖ e)) by (
    -- Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ (wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)) by
    subst₂ (Γ₂ ∋/⊢_∶_)
      (sym (&-,ₖ-there ϕ e x))
      (wk-telescope Γ₁ x ⋯ ϕ                    ≡⟨ sym (wk-cancels-,ₖ (wk-telescope Γ₁ x) ϕ e) ⟩
       wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)     ≡⟨ sym (cong (_⋯ ϕ ,ₖ e) (wk-telescope-there Γ₁ t x)) ⟩
       wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ,ₖ e ∎)
    (Γ₂ ∋/⊢ x & ϕ ∶ (wk-telescope Γ₁ x ⋯ ϕ) by ⊢ϕ x _ refl ))

  ⊢id : ∀ {S} {Γ : Ctx S} → Γ ∋*/⊢* id ∶ Γ
  ⊢id {Γ = Γ} x _ refl =
    Γ ∋/⊢ x & id ∶ (wk-telescope Γ x ⋯ id)
      by subst₂ (Γ ∋/⊢_∶_)
         (sym (&-id x))
         (sym (⋯-id (wk-telescope Γ x)))
         (
    Γ ∋/⊢ id/` x ∶ (wk-telescope Γ x)
      by ∋/⊢∶-lookup x)

  _⊢↓ : ∀ {S₁ S₂ s₁} {Γ₁ : Ctx (S₁ ▷ s₁)} {Γ₂ : Ctx S₂} {ϕ : (S₁ ▷ s₁) –[ 𝕂 ]→ S₂} →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂ ∋*/⊢* ϕ ↓ ∶ Γ₁ ↓ᶜ
  _⊢↓ {S₁} {S₂} {s₁} {Γ₁} {Γ₂} {ϕ} ⊢ϕ {sx} x t refl =
    Γ₂ ∋/⊢ x & (ϕ ↓) ∶ (t ⋯ (ϕ ↓))
      by subst₂ (Γ₂ ∋/⊢_∶_)
                (sym (&-↓ ϕ x))
                (wk-telescope Γ₁ (there x) ⋯ ϕ           ≡⟨ cong (_⋯ ϕ) (wk-telescope-there' Γ₁ x) ⟩
                 wk-telescope (Γ₁ ↓ᶜ) x ⋯ wkₖ _ idᵣ ⋯ ϕ  ≡⟨ ⋯-assoc _ (wkₖ _ idᵣ) ϕ ⟩
                 wk-telescope (Γ₁ ↓ᶜ) x ⋯ wkₖ _ idᵣ ·ₖ ϕ ≡⟨ ~-cong-⋯ _ (wk-↓ ϕ) ⟩
                 wk-telescope (Γ₁ ↓ᶜ) x ⋯ (ϕ ↓)          ∎)
                (⊢ϕ (there x) _ refl)


  -- match (1 , 2)
  --   (x , y) => e

  -- Γ ⊢ (1 , 2) : ℕ × ℕ
  -- Γ ⊢ (x , y) : ℕ ▶ᵖ ℕ ▶ᵖ []ᵖ 
  -- Γ ⊢* id ∥ { 1 / x, 2 / y } : Γ ▶ ℕ ▶ ℕ
  -- Note: Type of `x` might use vars from Γ
  -- Note: Type of `y` might use `x`
  -- Note: Type of `1` might use vars from Γ
  -- Note: Type of `2` might use `1`
  -- Γ ⊢* { 1 / x, 2 / y } : ℕ ▶ ℕ
  -- Note: Types of `1` and `2` may contain vars from Γ 
  -- Note: ℕ ▶ ℕ can only be a Ctx', because types of `x` and `y` may contain vars from Γ 
  -- Γ ⊢ 1 : ℕ ⋯ { 1 / x, 2 / y }
  -- Γ ⊢ 2 : ℕ ⋯ { 1 / x, 2 / y }

  _∋*/⊢*''_∶_ : Ctx S₂ → S₁ –[ 𝕂 ]→ S₂ → Ctx S₁ → Set
  _∋*/⊢*''_∶_ {S₂ = S₂} {S₁ = S₁} Γ₂ ϕ Γ₁ =
    -- ∀ {s₁} → (x : S₁ ∋ s₁) → Γ₂ ◆ f _ x ∶ subst (S₂ ∶⊢_) (sym (s→m/s→M s₁)) (wk-telescope Γ₁ x ⋯ f)
    ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ∋/⊢ (x & ϕ) ∶ (t ⋯ ϕ)

  wk-drop-∈' : (x : S ∋ s) → (S' ▷▷ drop-∈ x S) ⊢ s' → (S' ▷▷ S) ⊢ s'
  wk-drop-∈' (here _)  t = t ⋯ wknᵣ
  wk-drop-∈' (there x) t = wk-drop-∈' x t ⋯ wknᵣ

  wk-telescope' : Ctx' S' S → S ∋ s → S' ▷▷ S ∶⊢ s
  wk-telescope' Γ x = wk-drop-∈' x (lookup' Γ x)

  infix   4  _∋'_∶_
  _∋'_∶_ : Ctx' S' S → S ∋ s → S' ▷▷ S ∶⊢ s → Set
  Γ ∋' x ∶ t = wk-telescope' Γ x ≡ t

  _∋*/⊢*_∶_via_ : ∀ {S S₁ S₂} → Ctx S₂ → S₁ –[ 𝕂 ]→ S₂ → Ctx' S S₁ → S –[ 𝕂 ]→ S₂ → Set
  _∋*/⊢*_∶_via_ {S} {S₁} {S₂} Γ₂ ϕ Γ₁ ϕ' =
    ∀ {s₁} (x : S₁ ∋ s₁) (t : S ▷▷ S₁ ∶⊢ s₁) (⊢x : Γ₁ ∋' x ∶ t)
    → Γ₂ ∋/⊢ x & ϕ ∶ (t ⋯ (ϕ' ∥ ϕ) )

  postulate
    _⊢∥'_ : ∀ {S S₁ S₂} {Γ : Ctx S} {Γ₁ : Ctx S₁} {Γ₂ : Ctx' S₁ S₂} {ϕ₁ : S₁ –[ 𝕂 ]→ S} {ϕ₂ : S₂ –[ 𝕂 ]→ S} →
      Γ ∋*/⊢* ϕ₁ ∶ Γ₁ →
      Γ ∋*/⊢* ϕ₂ ∶ Γ₂ via ϕ₁ →
      Γ ∋*/⊢* (ϕ₁ ∥ ϕ₂) ∶ Γ₁ ▶▶ Γ₂
  -- _⊢∥'_ {S} {S₁} {[]} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} x _ refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/sx)) in
  --   Γ ∋/⊢ x & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶ Γ₂) x ⋯ ϕ₁ ∥ ϕ₂)
  --     by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ sub ■₂)
  --               (use-~-hom (~-sym (∥-[] ϕ₁ ϕ₂)) sx x)
  --               (~-cong-⋯ _ (~-sym (∥-[] ϕ₁ ϕ₂)))
  --               (⊢ϕ₁ x _ refl)
  -- _⊢∥'_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} x@(here refl) _ refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/sx)) in
  --   Γ ∋/⊢ x & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶ Γ₂) x ⋯ ϕ₁ ∥ ϕ₂)
  --     by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ sub ■₂)
  --               (sym (&-∥-here ϕ₁ ϕ₂))
  --               (wk-telescope' Γ₂ (here refl) ⋯ ϕ₁ ∥ ϕ₂        ≡⟨ {!!} ⟩
  --                wk-telescope (Γ₁ ▶▶ Γ₂) (here refl) ⋯ ϕ₁ ∥ ϕ₂ ∎)
  --               (⊢ϕ₂ (here refl) _ refl)
  -- _⊢∥'_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} x@(there y) _ refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/sx)) in
  --   Γ ∋/⊢ x & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶ Γ₂) x ⋯ ϕ₁ ∥ ϕ₂)
  --     by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ sub ■₂)
  --               {!!}
  --               {!!}
  --               {!(⊢ϕ₁ ⊢∥' (⊢ϕ₂ ⊢↓)) x _ refl!}

  -- TODO: Dependency not yet upgraded to 2.6.4
  postulate
    _⊢∥_ : ∀ {S S₁ S₂} {Γ : Ctx S} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ₁ : S₁ –[ 𝕂 ]→ S} {ϕ₂ : S₂ –[ 𝕂 ]→ S} →
      Γ ∋*/⊢* ϕ₁ ∶ Γ₁ →
      Γ ∋*/⊢* ϕ₂ ∶ Γ₂ →
      Γ ∋*/⊢* (ϕ₁ ∥ ϕ₂) ∶ Γ₁ ▶▶ wk*-Ctx _ Γ₂
  -- _⊢∥_ : ∀ {S S₁ S₂} {Γ : Ctx S} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ₁ : S₁ –[ 𝕂 ]→ S} {ϕ₂ : S₂ –[ 𝕂 ]→ S} →
  --   Γ ∋*/⊢* ϕ₁ ∶ Γ₁ →
  --   Γ ∋*/⊢* ϕ₂ ∶ Γ₂ →
  --   Γ ∋*/⊢* (ϕ₁ ∥ ϕ₂) ∶ Γ₁ ▶▶ wk*-Ctx _ Γ₂
  -- _⊢∥_ {S} {S₁} {[]}      {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} x t ∋x =
  --   subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ subst (S ∶⊢_) (sym (id/sx)) ■₂)
  --          (use-~-hom (~-sym (∥-[] ϕ₁ ϕ₂)) sx x)
  --          (~-cong-⋯ t (~-sym (∥-[] ϕ₁ ϕ₂)))
  --          (⊢ϕ₁ x t ∋x)
  -- _⊢∥_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {.s₂} x@(here refl) t ∋x@refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/s₂)) in
  --   let sub' = subst (([] ▷▷ S₂) →ᵣ_) (cong (_▷▷ S₂) (++-identityʳ S₁)) in
  --   let sub'' = subst (λ ■ → Ctx' ■ (S₂ ▷ s₂)) (++-identityʳ S₁) in
  --   let sub''x = subst (λ ■ → (■ ▷▷ S₂) ∶⊢ _) (++-identityʳ S₁) in
  --   let sub₂ = subst₂ _→ᵣ_ (++-identityʳ (S₂ ▷ s₂)) (cong (_▷▷ (S₂ ▷ s₂)) (++-identityʳ S₁)) in
  --   let sub₂₁ = subst (_∶⊢ s₂) (sym (++-identityʳ (S₂ ▷ s₂))) in
  --   let sub₂₂ = subst (_∶⊢ s₂) (cong (_▷▷ (S₂ ▷ s₂)) (++-identityʳ S₁)) in
  --   let sub₂₁' = subst (_∶⊢ s₂) (sym (++-identityʳ S₂)) in
  --   let sub₂₂' = subst (_∶⊢ s₂) (cong (_▷▷ S₂) (++-identityʳ S₁)) in
  --   let sub₂₁'⁻¹ = subst (_∶⊢ s₂) (++-identityʳ S₂) in
  --   Γ ∋/⊢ here refl & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) (here refl) ⋯ ϕ₁ ∥ ϕ₂)
  --     by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ sub ■₂)
  --          (sym (&-∥-here ϕ₁ ϕ₂))
  --          (wk-telescope Γ₂ (here refl) ⋯ ϕ₂                           ≡⟨⟩
  --           wkₛ _ (lookup Γ₂ (here refl)) ⋯ ϕ₂                         ≡⟨ ~-cong-⋯ _ (~-sym (wk*-∥₁ ϕ₁ ϕ₂)) ⟩
  --           wkₛ _ (lookup Γ₂ (here refl)) ⋯ sub₂ (wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂)) ·[ ckitᵣ ] (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ sym (⋯-assoc _ _ (ϕ₁ ∥ ϕ₂)) ⟩
  --           wkₛ _ (lookup Γ₂ (here refl)) ⋯ᵣ sub₂ (wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (_⋯ ϕ₁ ∥ ϕ₂) (dist-subst-sub' _ _ (wkₛ _ (lookup Γ₂ (here refl))) (wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂))) ⟩
  --           sub₂₂ (sub₂₁ (wkₛ _ (lookup Γ₂ (here refl))) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong
  --                  (λ ■ → sub₂₂ (■ ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂)) ⋯ ϕ₁ ∥ ϕ₂)
  --                  (sym (dist-subst' (λ S → S ▷ s₂) (wkₛ s₂) (sym (++-identityʳ S₂)) (sym (++-identityʳ (S₂ ▷ s₂))) _)) ⟩
  --           sub₂₂ (wkₛ _ (sub₂₁' (lookup Γ₂ (here refl))) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* (S₂ ▷ s₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (λ ■ → sub₂₂ ■ ⋯ ϕ₁ ∥ ϕ₂) (~-cong-⋯ (wkₛ _ _) (↑*-▷ S₂ s₂ (wkₖ* S₁ (id {S = []})))) ⟩
  --           sub₂₂ (wkₛ _ (sub₂₁' (lookup Γ₂ (here refl))) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂ ↑ s₂) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (λ ■ → sub₂₂ ■ ⋯ ϕ₁ ∥ ϕ₂) (⋯-assoc _ (wkₖ s₂ idᵣ) (wkₖ* S₁ (id {S = []}) ↑* S₂ ↑ s₂)) ⟩
  --           sub₂₂ (sub₂₁' (lookup Γ₂ (here refl)) ⋯ wkₖ s₂ idᵣ ·ₖ wkₖ* S₁ idᵣ ↑* S₂ ↑ s₂) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (λ ■ → sub₂₂ ■ ⋯ ϕ₁ ∥ ϕ₂) (~-cong-⋯ _ (~-sym (↑-wk (wkₖ* S₁ idᵣ ↑* S₂) s₂))) ⟩
  --           sub₂₂ (sub₂₁' (lookup Γ₂ (here refl)) ⋯ wkₖ* S₁ idᵣ ↑* S₂ ·ₖ wkₖ s₂ idᵣ) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (λ ■ → sub₂₂ ■ ⋯ ϕ₁ ∥ ϕ₂) (sym (⋯-assoc _ (wkₖ* S₁ idᵣ ↑* S₂) (wkₖ s₂ idᵣ))) ⟩
  --           sub₂₂ (wkₛ _ (sub₂₁' (lookup Γ₂ (here refl)) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ (ϕ₁ ∥ ϕ₂) ≡⟨⟩
  --           sub₂₂ (wkₛ _ (sub₂₁' (sub₂₁'⁻¹ (lookup' Γ₂ (here refl))) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong
  --                  (λ ■ → sub₂₂ (wkₛ _ (■ ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ ϕ₁ ∥ ϕ₂)
  --                  (cancel-subst _ (++-identityʳ S₂) _) ⟩
  --           sub₂₂ (wkₛ _ (lookup' Γ₂ (here refl) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (_⋯ ϕ₁ ∥ ϕ₂) (sym (dist-subst' (λ S → S ▷ s₂) (wkₛ s₂)
  --                 (cong (_▷▷ S₂) (++-identityʳ S₁))
  --                 (cong (_▷▷ (S₂ ▷ s₂)) (++-identityʳ S₁))
  --                 _)) ⟩
  --           wkₛ _ (sub₂₂' (lookup' Γ₂ (here refl) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --             ≡⟨ cong (λ ■ → wkₛ _ ■ ⋯ ϕ₁ ∥ ϕ₂) (sym (comm-subst (_▷▷ S₂) (++-identityʳ S₁) _)) ⟩
  --           wkₛ _ (sub''x (lookup' Γ₂ (here refl) ⋯ᵣ wkₖ* S₁ (id {S = []}) ↑* S₂)) ⋯ (ϕ₁ ∥ ϕ₂)
  --                                                                      ≡⟨⟩
  --           wkₛ _ (sub''x (lookup' Γ₂ (here refl) ⋯ᵣ ((wkₖ* S₁ (id {S = []})) ↑* drop-∈ x (S₂ ▷ s₂)))) ⋯ ϕ₁ ∥ ϕ₂
  --                                                                      ≡⟨ sym (cong (λ ■ → wkₛ _ (sub''x ■) ⋯ ϕ₁ ∥ ϕ₂)
  --                                                                           (lookup-map-Ctx' _ Γ₂ (here refl))) ⟩
  --           wkₛ _ (sub''x (lookup' (wk*-Ctx' S₁ Γ₂) (here refl))) ⋯ ϕ₁ ∥ ϕ₂ ≡⟨ cong (λ ■ → wkₛ _ ■ ⋯ ϕ₁ ∥ ϕ₂)
  --                                                                                (sym (dist-subst (λ Γ → lookup' Γ (here refl))
  --                                                                                       (++-identityʳ S₁) (wk*-Ctx' S₁ Γ₂))) ⟩
  --           wkₛ _ (lookup' (sub'' (wk*-Ctx' S₁ Γ₂)) (here refl)) ⋯ ϕ₁ ∥ ϕ₂      ≡⟨ refl ⟩
  --           wkₛ _ (lookup' (wk*-Ctx S₁ Γ₂) (here refl)) ⋯ ϕ₁ ∥ ϕ₂      ≡⟨ cong (λ ■ → wkₛ _ ■ ⋯ ϕ₁ ∥ ϕ₂)
  --                                                                              (sym (lookup-▶▶-here Γ₁ (wk*-Ctx S₁ Γ₂))) ⟩
  --           wkₛ _ (lookup (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) (here refl)) ⋯ ϕ₁ ∥ ϕ₂ ≡⟨⟩
  --           wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) (here refl) ⋯ ϕ₁ ∥ ϕ₂   ∎)
  --          (
  --   Γ ∋/⊢ here refl & ϕ₂ ∶ sub (wk-telescope Γ₂ (here refl) ⋯ ϕ₂)
  --     by ⊢ϕ₂ (here refl) (wk-telescope Γ₂ (here refl)) refl)
  -- _⊢∥_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} (there x) t ∋x@refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/sx)) in
  --   Γ ∋/⊢ there x & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) (there x) ⋯ ϕ₁ ∥ ϕ₂)
  --     by subst₂ (Γ ∋/⊢_∶_)
  --               (x & ϕ₁ ∥ (ϕ₂ ↓)   ≡⟨ sym (use-~-hom (∥-↓ ϕ₁ ϕ₂) _ x) ⟩
  --                x & (ϕ₁ ∥ ϕ₂) ↓   ≡⟨ &-↓ (ϕ₁ ∥ ϕ₂) x ⟩
  --                there x & ϕ₁ ∥ ϕ₂ ∎)
  --               (sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ (Γ₂ ↓ᶜ)) x ⋯ ϕ₁ ∥ (ϕ₂ ↓))
  --                  ≡⟨ cong sub (~-cong-⋯ _ (~-sym (∥-↓ ϕ₁ ϕ₂))) ⟩
  --                sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ (Γ₂ ↓ᶜ)) x ⋯ (ϕ₁ ∥ ϕ₂) ↓)
  --                  ≡⟨ cong (λ ■ → sub (■ ⋯ ((ϕ₁ ∥ ϕ₂) ↓))) (cong (wk-drop-∈ x) (cong-lookup
  --                       (≡ᶜ→~ᶜ (≡ᶜ-cong-▶▶ (≡ᶜ-refl {Γ = Γ₁}) (wk*-Ctx-↓ Γ₂)) _ x))) ⟩
  --                sub (wk-telescope (Γ₁ ▶▶ (wk*-Ctx S₁ Γ₂ ↓ᶜ)) x ⋯ (ϕ₁ ∥ ϕ₂) ↓)
  --                  ≡⟨ cong (λ ■ → sub (■ ⋯ ((ϕ₁ ∥ ϕ₂) ↓))) (cong (wk-drop-∈ x) (cong-lookup
  --                       (sym (dist-↓-▶▶-~ Γ₁ (wk*-Ctx S₁ Γ₂) _ x)))) ⟩
  --                sub (wk-telescope ((Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) ↓ᶜ) x ⋯ (ϕ₁ ∥ ϕ₂) ↓)
  --                  ≡⟨ cong sub (~-cong-⋯ _ (~-sym (wk-↓ (ϕ₁ ∥ ϕ₂)))) ⟩
  --                sub (wk-telescope ((Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) ↓ᶜ) x ⋯ wkₖ _ idᵣ ·ₖ (ϕ₁ ∥ ϕ₂))
  --                  ≡⟨ cong sub (sym (⋯-assoc _ (wkₖ _ idᵣ) (ϕ₁ ∥ ϕ₂))) ⟩
  --                sub (wk-telescope ((Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) ↓ᶜ) x ⋯ wkₖ _ idᵣ ⋯ ϕ₁ ∥ ϕ₂)
  --                  ≡⟨⟩
  --                sub (wkₛ _ (wk-telescope ((Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) ↓ᶜ) x) ⋯ ϕ₁ ∥ ϕ₂)
  --                  ≡⟨ cong (λ ■ → sub (■ ⋯ ϕ₁ ∥ ϕ₂))
  --                       (sym (wk-telescope-there' (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) x)) ⟩
  --                sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ Γ₂) (there x) ⋯ ϕ₁ ∥ ϕ₂)  ∎)
  --               (
  --   Γ ∋/⊢ x & ϕ₁ ∥ (ϕ₂ ↓) ∶ sub (wk-telescope (Γ₁ ▶▶ wk*-Ctx S₁ (Γ₂ ↓ᶜ)) x ⋯ ϕ₁ ∥ (ϕ₂ ↓))
  --     by (⊢ϕ₁ ⊢∥ (⊢ϕ₂ ⊢↓)) x _ refl
  --   )

  -- -- TODO: shouldn't substitution Typings allow Ctx' instead of Ctx?
  -- _⊢∥_ : ∀ {S S₁ S₂} {Γ : Ctx S} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ₁ : S₁ –[ 𝕂 ]→ S} {ϕ₂ : S₂ –[ 𝕂 ]→ S} →
  --   Γ ∋*/⊢* ϕ₁ ∶ Γ₁ →
  --   Γ ∋*/⊢* ϕ₂ ∶ Γ₂ →
  --   Γ ∋*/⊢* (ϕ₁ ∥ ϕ₂) ∶ Γ₁ ▶▶' wk*-Ctx' _ Γ₂
  -- _⊢∥_ {S} {S₁} {[]}      {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} x t ∋x =
  --   subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ subst (S ∶⊢_) (sym (id/sx)) ■₂)
  --          (use-~-hom (~-sym (∥-[] ϕ₁ ϕ₂)) sx x)
  --          (~-cong-⋯ t (~-sym (∥-[] ϕ₁ ϕ₂)))
  --          (⊢ϕ₁ x t ∋x)
  -- _⊢∥_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {.s₂} x@(here refl) t ∋x@refl =
  --   let sub = subst (_∶⊢_ S) (sym (id/s₂)) in
  --   Γ ∋/⊢ here refl & ϕ₁ ∥ ϕ₂ ∶ sub (wk-telescope (Γ₁ ▶▶' wk*-Ctx' S₁ Γ₂) (here refl) ⋯ ϕ₁ ∥ ϕ₂)
  --     by (
  --   Γ ∋/⊢ here refl & ϕ₁ ∥ ϕ₂ ∶ sub (wkₛ _ (lookup (Γ₁ ▶▶' wk*-Ctx' S₁ Γ₂) (here refl)) ⋯ ϕ₁ ∥ ϕ₂)
  --     by {!⊢ϕ₂ (here refl) (lookup Γ₂ (here refl)) !}
  --     )
  -- _⊢∥_ {S} {S₁} {S₂ ▷ s₂} {Γ} {Γ₁} {Γ₂} {ϕ₁} {ϕ₂} ⊢ϕ₁ ⊢ϕ₂ {sx} (there x) t ∋x = {!!}

  ⊢*~ :
    ∀ {S₁} {S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ ϕ' : S₁ –[ 𝕂 ]→ S₂} 
    → ϕ ~ ϕ'
    → Γ₂ ∋*/⊢* ϕ ∶ Γ₁
    → Γ₂ ∋*/⊢* ϕ' ∶ Γ₁
  ⊢*~ {S₁} {S₂} {Γ₁} {Γ₂} {ϕ} {ϕ'} ϕ~ϕ' ⊢ϕ {s₁} x t ⊢x =
    Γ₂ ∋/⊢ (x & ϕ') ∶ (t ⋯ ϕ')
      by subst₂
           (Γ₂ ∋/⊢_∶_)
           (`/id-injective (use-~ ϕ~ϕ' _ x))
           (~-cong-⋯ t ϕ~ϕ') (
    Γ₂ ∋/⊢ (x & ϕ ) ∶ (t ⋯ ϕ )
      by ⊢ϕ x t ⊢x)

  ⊢⦅_⦆ : ∀ {s} {Γ : Ctx S} {t : S ∋/⊢ s} {T : S ∶⊢ (s)}
    → Γ ∋/⊢ t ∶ T 
    → Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ T
  ⊢⦅_⦆ {S} {s} {Γ} {t} {T} ⊢t =
    let ⊢t' = subst (Γ ∋/⊢ t ∶_) (sym (
                begin
                  T ⋯ id
                ≡⟨ ⋯-id T ⟩
                  T
                ∎
              )) ⊢t in
    Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ T
      by ⊢*~ (~-sym (⦅⦆-,ₖ t)) (
    Γ ∋*/⊢* (id ,ₖ t) ∶ Γ ▶ T
      by (⊢id ,* ⊢t')
    )

open TypingKit ⦃ ... ⦄

infixl  5  _∋*/⊢*[_]_∶_
_∋*/⊢*[_]_∶_ :
  ∀ {_∋/⊢_ : VarScoped} {𝕂 : Kit _∋/⊢_}
    {K : KitT 𝕂} {C₁ : ComposeKit 𝕂 kitᵣ 𝕂} {C₂ : ComposeKit 𝕂 𝕂 𝕂}
  → Ctx S₂ → TypingKit 𝕂 K C₁ C₂ → S₁ –[ 𝕂 ]→ S₂ → Ctx S₁ → Set
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

record TypingTraversal : Set (lsuc ℓ) where
  infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_

  field
    -- Substitution/Renaming preserves typing
    _⊢⋯_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
             ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
             ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
             ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
             ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
             {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
           Γ₁ ⊢ e ∶ t →
           Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
           Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ

    -- ⋯-var : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (x : S₁ ∋ s) (f : S₁ –→ S₂) →
    --         (` x) ⋯ f ≡ subst (S₂ ⊢_) (id/s) (tm _ (f _ x))

  instance
    ikitᵣ : TypingKit kitᵣ kittᵣ ckitᵣ ckitᵣ
    TypingKit._∋/⊢_∶_ ikitᵣ = _∋_∶_
    TypingKit.∋/⊢∶-lookup ikitᵣ = λ _ → refl
    TypingKit.id/⊢`   ikitᵣ = λ ⊢x → ⊢x
    TypingKit.⊢`/id   ikitᵣ = ⊢`
    TypingKit.∋wk/⊢wk ikitᵣ Γ t' x t refl = wk-telescope-there Γ t' x
    TypingKit.≡ᶜ-cong-∋/⊢ ikitᵣ = ≡ᶜ-cong-∋

    ikitₛ : TypingKit kitₛ kittₛ ckitₛᵣ ckitₛₛ
    TypingKit._∋/⊢_∶_ ikitₛ = _⊢_∶_
    TypingKit.∋/⊢∶-lookup ikitₛ = λ _ → ⊢` refl
    TypingKit.id/⊢`   ikitₛ = ⊢`
    TypingKit.⊢`/id   ikitₛ = λ ⊢t → ⊢t
    TypingKit.∋wk/⊢wk ikitₛ Γ t' x t ⊢e = ⊢e ⊢⋯ λ x₁ t₁ ⊢x₁ →
      (Γ ▶ t') ∋ (x₁ & wknᵣ) ∶ (t₁ ⋯ wknᵣ)
        by subst (λ ■ → (Γ ▶ t') ∋ ■ ∶ (t₁ ⋯ wknᵣ))
                (sym (trans (&-wkₖ-wk id x₁) (cong there (&-id x₁)))) (
      (Γ ▶ t') ∋ (there x₁) ∶ (t₁ ⋯ wknᵣ)
        by (∋wk/⊢wk Γ t' x₁ t₁ ⊢x₁))
    TypingKit.≡ᶜ-cong-∋/⊢ ikitₛ = λ x → ≡ᶜ-cong-⊢

  open TypingKit ikitᵣ public using () renaming
    (∋wk/⊢wk to ⊢wk; _∋↑/⊢↑_ to _∋↑_; _,*_ to _,*ᵣ_; ⊢id to ⊢idᵣ; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ; _⊢↓ to ⊢↓ᵣ; _⊢∥_ to _⊢∥ᵣ_; _⊢∥'_ to _⊢∥'ᵣ_;
    _∋*/⊢*_∶_via_ to _∋*_∶_via_)
  open TypingKit ikitₛ public using () renaming
    (∋wk/⊢wk to ∋wk; _∋↑/⊢↑_ to _⊢↑_; _,*_ to _,*ₛ_; ⊢id to ⊢idₛ; ⊢⦅_⦆ to ⊢⦅_⦆ₛ; _⊢↓ to ⊢↓ₛ; _⊢∥_ to _⊢∥ₛ_; _⊢∥'_ to _⊢∥'ₛ_;
    _∋*/⊢*_∶_via_ to _⊢*_∶_via_)

  -- Renaming preserves typing

  _⊢⋯ᵣ_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ρ : S₁ →ᵣ S₂} →
          Γ₁ ⊢ e ∶ t →
          Γ₂ ∋* ρ ∶ Γ₁ →
          Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
  _⊢⋯ᵣ_ = _⊢⋯_

  -- Substitution preserves typing

  _⊢⋯ₛ_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ₛ S₂} →
          Γ₁ ⊢ e ∶ t →
          Γ₂ ⊢* σ ∶ Γ₁ →
          Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
  _⊢⋯ₛ_ = _⊢⋯_

