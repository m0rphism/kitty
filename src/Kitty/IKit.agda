open import Kitty.Modes
open import Kitty.Kit using (KitTraversal; KitHomotopy)
open import Kitty.Compose using (KitAssoc)
open import Kitty.Types using (KitType)
open import Kitty.ITerms using (ITerms)
open KitAssoc using (KitAssocLemmas)

module Kitty.IKit {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) (H : KitHomotopy 𝕋 T) (A : KitAssoc 𝕋 T H) (AL : KitAssocLemmas A) (KT : KitType 𝕋) (IT : ITerms 𝕋 T H A AL KT) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_) renaming (_∋_ to _by_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Prelude
open import Kitty.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Kitty.Kit 𝕋
open Kitty.Kit.KitTraversal T
open Kitty.Compose 𝕋 T H
open Kitty.Compose.KitAssoc A
open Kitty.Compose.KitAssoc.KitAssocLemmas AL
open Kitty.Types.KitType KT
open import Kitty.OPE AL KT
open Kitty.ITerms 𝕋 T H A AL KT
open Kitty.ITerms.ITerms IT

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m
    𝕂 : Kit
    𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}}
    𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}}
    WK : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}}

record IKit
    (𝕂 : Kit)
    {𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }
    {𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }
    (WK : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}} )
    : Set₁ where

  infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
  infixl  6  _∋↑/⊢↑_
  -- infixl  5  _,ₖ_
  -- infixl  6  _↑_  _↑*_

  private instance _ = 𝕂
  private instance _ = 𝔸₁
  private instance _ = 𝔸₂

  open Kit 𝕂
  open WkDistKit WK

  field
    -- Variable/Term Typing
    _∋/⊢_∶_  : ∀ {SM} → Ctx µ → µ ∋/⊢ SM → µ ∶⊢ m→M/id SM → Set

    ∋/⊢∶-lookup : ∀ {m} x → Γ ∋/⊢ id/` m x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) (wk-telescope Γ x)

    -- Conditional Applications of Variable-Typing-Rule
    id/⊢`    : ∀ {x : µ ∋ m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
               → Γ ∋ x ∶ t
               →  Γ ∋/⊢ id/` _ x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) t
    ⊢`/id    : ∀ {e : µ ∋/⊢ id/m→M m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
               → Γ ∋/⊢ e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t
               → Γ ⊢ `/id _ e ∶ t
    ⊢`/id'   : ∀ {SM} {e : µ ∋/⊢ SM} {t : µ ∶⊢ m→M/id SM} {Γ : Ctx µ}
               → Γ ∋/⊢ e ∶ t
               → Γ ⊢ `/id' _ e ∶ t

    -- Weakening preserveres variable/term typings.
    ∋wk/⊢wk  : ∀ {SM} (Γ : Ctx µ) (t' : µ ∶⊢ m→M m) (e : µ ∋/⊢ SM) (t : µ ∶⊢ m→M/id SM)
               → Γ ∋/⊢ e ∶ t
               → (Γ ▶ t') ∋/⊢ wk _ e ∶ Kit.wk kitₛ _ t
    -- ⊢wk-vr : ∀ {x : µ ∋ m} {t : µ ∶⊢ M} (⊢x : Γ ∋ x ∶ t) →
    --          ⊢wk (⊢vr ⊢x) ≡ ⊢vr (there x)
    -- wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
    -- id/`/id     : ∀ x → subst (µ ⊢_) (m→SM→M m) (tm _ (vr _ x)) ≡ ` x

  -- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
  -- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
  -- _∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
  -- _∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ
  -- TODO: IS THIS EQUIVALENT TO OPE?

  _∋*/⊢*_∶_ : Ctx µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
  _∋*/⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
    -- ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ◆ f _ x ∶ subst (µ₂ ∶⊢_) (sym (m→SM→M m₁)) (wk-telescope Γ₁ x ⋯ f)
    ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ∋/⊢ ϕ _ x ∶ subst (µ₂ ∶⊢_) (sym (id/m→M/id m₁)) (t ⋯ ϕ)

  _∋↑/⊢↑_ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
    ∀ t →
    (Γ₂ ▶ (t ⋯ ϕ)) ∋*/⊢* (ϕ ↑ m) ∶ (Γ₁ ▶ t)
  _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} ⊢ϕ t' (here refl) .(t' ⋯ᵣ wkᵣ) refl =
    Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ id/` _ (here refl) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (t' ⋯ᵣ wkᵣ ⋯ ϕ ↑ _)
      by subst (Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ id/` _ (here refl) ∶_)
           (cong (subst _ _) (sym (dist-↑-f t' ϕ)))
           (id/⊢` {x = here refl} {Γ = Γ₂ ▶ (t' ⋯ ϕ)} refl)
  _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} ⊢ϕ t (there x) _ refl =
    Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ wk (id/m→M _) (ϕ _ x) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
      by subst (λ ■ → Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ wk (id/m→M _) (ϕ _ x) ∶ ■)
        (
         begin
           subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ) ⋯ᵣ wkᵣ
         ≡⟨ dist-subst (_⋯ᵣ wkᵣ) ((sym (id/m→M/id _))) (wk-telescope Γ₁ x ⋯ ϕ) ⟩
           subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ ⋯ᵣ wkᵣ)
         ≡⟨ cong (subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _))) (sym (dist-↑-f (wk-telescope Γ₁ x) ϕ)) ⟩
           subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ᵣ wkᵣ ⋯ ϕ ↑ _)
         ≡⟨⟩
           subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
         ∎
        )
      (∋wk/⊢wk _ _ _ _ (⊢ϕ x _ refl) )

  _,*_ : ∀ {m} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {e : µ₂ ∋/⊢ id/m→M m} {t : µ₁ ∶⊢ m→M m} →
    Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
    Γ₂ ∋/⊢   e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t ⋯ ϕ →
    Γ₂ ∋*/⊢* ϕ ,ₖ e ∶ Γ₁ ▶ t
  _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (here refl) _ refl =
    subst (Γ₂ ∋/⊢ e ∶_) (
      begin
        subst (µ₁ ∶⊢_) (sym (id/m→M/id _)) t ⋯ ϕ
      ≡⟨ sym (wk-cancels-,ₖ (subst (_ ∶⊢_) (sym (id/m→M/id _)) t) ϕ e) ⟩
        (subst (µ₁ ∶⊢_) (sym (id/m→M/id _)) t) ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ e)
      ≡⟨ dist-subst (λ ■ → ■ ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ e)) (sym (id/m→M/id _)) t ⟩
        subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (t ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ e))
      ≡⟨⟩
        subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
      ∎
    ) ⊢e
  _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (there x) _ eq@refl =
    Γ₂ ∋/⊢ (ϕ ,ₖ e) _ (there x) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ (ϕ ,ₖ e)) by (
    Γ₂ ∋/⊢ ϕ _ x ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ e)) by
    subst (λ ■ → Γ₂ ∋/⊢ ϕ _ x ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) ■)
      (wk-telescope Γ₁ x ⋯ ϕ               ≡⟨ sym (wk-cancels-,ₖ (wk-telescope Γ₁ x) ϕ e) ⟩
       wk-telescope Γ₁ x ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ e) ∎)
    (Γ₂ ∋/⊢ ϕ _ x ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ) by ⊢ϕ x _ refl ))

  ⊢idₖ : Γ ∋*/⊢* idₖ ∶ Γ
  ⊢idₖ {Γ = Γ} x _ refl =
    Γ ∋/⊢ idₖ _ x ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ x ⋯ idₖ)
      by subst (λ ■ → Γ ∋/⊢ _ ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) ■)
         (sym (⋯-id (wk-telescope Γ x)))
         (
    Γ ∋/⊢ id/` _ x ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ x)
      by ∋/⊢∶-lookup x)

  ⊢⦅_⦆ : ∀ {m} {Γ : Ctx µ} {t : µ ∋/⊢ id/m→M m} {T : µ ∶⊢ m→M/id (id/m→M m)}
    → Γ ∋/⊢ t ∶ T 
    → Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
  ⊢⦅_⦆ {µ = µ} {Γ = Γ} {t} {T} ⊢t = ⊢idₖ ,* subst (Γ ∋/⊢ t ∶_) (sym (
      begin
        subst
          (µ ∶⊢_)
          (sym (id/m→M/id _))
          (subst (µ ∶⊢_) (id/m→M/id _) T)
        ⋯ idₖ
      ≡⟨ cong (_⋯ idₖ) (cancel-subst (µ ∶⊢_) (id/m→M/id _) T) ⟩
        T ⋯ idₖ
      ≡⟨ ⋯-id T ⟩
        T
      ∎
    )) ⊢t

open IKit {{...}}

infixl  5  _∋*/⊢*[_]_∶_
_∋*/⊢*[_]_∶_ : Ctx µ₂ → IKit 𝕂 WK → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
Γ₂ ∋*/⊢*[ IK ] f ∶ Γ₁ = Γ₂ ∋*/⊢* f ∶ Γ₁ where instance _ = IK

open Kit {{...}}
open ComposeKit {{...}}

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kitᵣᵣ
private instance _ = kitᵣₛ
private instance _ = kitₛᵣ
private instance _ = kitₛₛ
private instance _ = wk-kitᵣ
private instance _ = wk-kitₛ

record IKitTraversal : Set₁ where
  infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_

  field
    -- Substitution/Renaming preserves typing
    _⊢⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦃ WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦄ ⦃ IK : IKit 𝕂 WK ⦄
             {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
           Γ₁ ⊢ e ∶ t →
           Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
           Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ

    -- ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
    --         (` x) ⋯ f ≡ subst (µ₂ ⊢_) (m→SM→M m) (tm _ (f _ x))

  ikitᵣ : IKit kitᵣ wk-kitᵣ
  IKit._∋/⊢_∶_ ikitᵣ = _∋_∶_
  IKit.∋/⊢∶-lookup ikitᵣ = λ _ → refl
  IKit.id/⊢`   ikitᵣ = id
  IKit.⊢`/id   ikitᵣ = ⊢`
  IKit.⊢`/id'  ikitᵣ = ⊢`
  IKit.∋wk/⊢wk ikitᵣ _ _ _ _ refl = refl

  private instance _ = ikitᵣ

  ikitₛ : IKit kitₛ wk-kitₛ
  IKit._∋/⊢_∶_ ikitₛ = _⊢_∶_
  IKit.∋/⊢∶-lookup ikitₛ = λ _ → ⊢` refl
  IKit.id/⊢`   ikitₛ = ⊢`
  IKit.⊢`/id   ikitₛ = id
  IKit.⊢`/id'  ikitₛ = id
  IKit.∋wk/⊢wk ikitₛ Γ t' x t ⊢e = ⊢e ⊢⋯ ∋wk/⊢wk Γ t'

  private instance _ = ikitₛ

  open IKit ikitᵣ public using () renaming (_∋*/⊢*_∶_ to _∋*_∶_; ∋wk/⊢wk to ⊢wk; _∋↑/⊢↑_ to _∋↑_; _,*_ to _,*ᵣ_; ⊢idₖ to ⊢idᵣ; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
  open IKit ikitₛ public using () renaming (_∋*/⊢*_∶_ to _⊢*_∶_; ∋wk/⊢wk to ∋wk; _∋↑/⊢↑_ to _⊢↑_; _,*_ to _,*ₛ_; ⊢idₖ to ⊢idₛ; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

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

