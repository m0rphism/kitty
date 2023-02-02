open import Kitty.Modes
open import Kitty.Kit using (KitTraversal; KitHomotopy)
open import Kitty.Compose using (KitAssoc)
open import Kitty.Types using (KitType)
open import Kitty.Experimental.ITerms using (ITerms)
open KitAssoc using (KitAssocLemmas)

module Kitty.Experimental.IKit {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) (H : KitHomotopy 𝕋 T) (A : KitAssoc 𝕋 T H) (AL : KitAssocLemmas A) (KT : KitType 𝕋) (IT : ITerms 𝕋 T H A AL KT) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_) renaming (_∋_ to _by_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Prelude

open Modes 𝕄
open Terms 𝕋
open Kitty.Kit 𝕋
open Kitty.Kit.KitTraversal T
open Kitty.Compose 𝕋 T H
open Kitty.Compose.KitAssoc A
open Kitty.Compose.KitAssoc.KitAssocLemmas AL
open Kitty.Types.KitType KT
open import Kitty.OPE AL KT
open Kitty.Experimental.ITerms 𝕋 T H A AL KT
open Kitty.Experimental.ITerms.ITerms IT

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
    _∋/⊢_∶_  : ∀ {SM} → Ctx µ → µ ∋/⊢ SM → µ ∶⊢ m→M/id SM → Set
    id/⊢`    : ∀ {x : µ ∋ m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ} →
               Γ ∋ x ∶ t →  Γ ∋/⊢ id/` _ x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) t
    ⊢`/id    : ∀ {e : µ ∋/⊢ id/m→M m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ} →
               Γ ∋/⊢ e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t →  Γ ⊢ `/id _ e ∶ t
    -- ⊢`/id  : ∀ {SM} {e : µ ∋/⊢ SM} {t : µ ∶⊢ SM→M SM} {Γ : Ctx µ} →
    --          Γ ∋/⊢ e ∶ t →  Γ ⊢ `/id _ e ∶ t
    ∋wk/⊢wk  : ∀ {SM} (Γ : Ctx µ) (t' : µ ∶⊢ m→M m) (e : µ ∋/⊢ SM) (t : µ ∶⊢ m→M/id SM) →
               Γ ∋/⊢ e ∶ t → (Γ ▶ t') ∋/⊢ wk _ e ∶ Kit.wk kitₛ _ t
    -- ⊢wk    : ∀ {SM} {t : µ ∶⊢ SM→M SM} (Γ : Ctx µ) (e : µ ∋/⊢ SM) (t' : µ ∶⊢ m→M m) →
    --          Γ ∋/⊢ e ∶ t → (Γ ,, t') ∋/⊢ wk _ e ∶ Kit.wk kitₛ _ t
    -- ⊢wk-vr : ∀ {x : µ ∋ m} {t : µ ∶⊢ M} (⊢x : Γ ∋ x ∶ t) →
    --          ⊢wk (⊢vr ⊢x) ≡ ⊢vr (there x)
    -- wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
    -- id/`/id     : ∀ x → subst (µ ⊢_) (m→SM→M m) (tm _ (vr _ x)) ≡ ` x

  _∋*/⊢*_∶_ : Ctx µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
  _∋*/⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ f Γ₁ =
    -- ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ◆ f _ x ∶ subst (µ₂ ∶⊢_) (sym (m→SM→M m₁)) (wk-telescope Γ₁ x ⋯ f)
    ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) → (⊢x : Γ₁ ∋ x ∶ t) → Γ₂ ∋/⊢ f _ x ∶ subst (µ₂ ∶⊢_) (sym (id/m→M/id m₁)) (t ⋯ f)

  _∋↑/⊢↑_ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {f : µ₁ –[ 𝕂 ]→ µ₂} →
         Γ₂ ∋*/⊢* f ∶ Γ₁ → ∀ t → (Γ₂ ▶ (t ⋯ f)) ∋*/⊢* (f ↑ m) ∶ (Γ₁ ▶ t)
  _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {f = f} ⊢f t' (here refl) .(t' ⋯ᵣ wkᵣ) refl =
    Γ₂ ▶ (t' ⋯ f) ∋/⊢ id/` _ (here refl) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (t' ⋯ᵣ wkᵣ ⋯ f ↑ _)
      by subst (Γ₂ ▶ (t' ⋯ f) ∋/⊢ id/` _ (here refl) ∶_)
           (cong (subst _ _) (sym (dist-↑-f t' f)))
           (id/⊢` {x = here refl} {Γ = Γ₂ ▶ (t' ⋯ f)} refl)
  _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {f = f} ⊢f t' (there x) t ∋x =
    Γ₂ ▶ (t' ⋯ f) ∋/⊢ wk (id/m→M _) (f _ x) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (t ⋯ f ↑ _)
      by {!⊢f !}
      -- by {!◆wk _ _ _ _ (⊢f _ (t ⋯ f) _)!}

  -- _↑_ : µ₁ –→ µ₂ → ∀ m → (m ∷ µ₁) –→ (m ∷ µ₂)
  -- (f ↑ m) _ (here p)  = vr _ (here p)
  -- (f ↑ m) _ (there x) = wk _ (f _ x)

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
  -- infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_
  infixl  5  _⊢⋯_

  field
    _⊢⋯_   : ∀ {{𝕂 : Kit}} {{𝔸₁}} {{𝔸₂}} {{WK : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}} }} {{IK : IKit 𝕂 WK}} {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {f : µ₁ –[ 𝕂 ]→ µ₂} →
            Γ₁ ⊢ e ∶ t → Γ₂ ∋*/⊢*[ IK ] f ∶ Γ₁ → Γ₂ ⊢ e ⋯ f ∶ t ⋯ f
    -- ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
    --         (` x) ⋯ f ≡ subst (µ₂ ⊢_) (m→SM→M m) (tm _ (f _ x))

  ikitᵣ : IKit kitᵣ wk-kitᵣ
  IKit._∋/⊢_∶_ ikitᵣ = _∋_∶_
  IKit.id/⊢`   ikitᵣ = id
  IKit.⊢`/id   ikitᵣ = ⊢`
  IKit.∋wk/⊢wk ikitᵣ _ _ _ _ refl = refl

  private instance _ = ikitᵣ

  ikitₛ : IKit kitₛ wk-kitₛ
  IKit._∋/⊢_∶_ ikitₛ = _⊢_∶_
  IKit.id/⊢`   ikitₛ = ⊢`
  IKit.⊢`/id   ikitₛ = id
  IKit.∋wk/⊢wk ikitₛ Γ t' x t ⊢e = ⊢e ⊢⋯ ∋wk/⊢wk Γ t'

  private instance _ = ikitₛ

  open IKit ikitᵣ public using () renaming (_∋*/⊢*_∶_ to _∋*_∶_; ∋wk/⊢wk to ⊢wk)
  open IKit ikitₛ public using () renaming (_∋*/⊢*_∶_ to _⊢*_∶_; ∋wk/⊢wk to ∋wk)
