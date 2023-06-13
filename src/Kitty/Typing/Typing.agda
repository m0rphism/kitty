open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.TypeSorts using (TypeSorts)
open import Kitty.Typing.CtxRepr using (CtxRepr)

module Kitty.Typing.Typing
  {𝕋 : Terms}
  {ℓ}
  {𝕊 : SubWithLaws 𝕋 ℓ}
  {T : Traversal 𝕋 𝕊}
  {H : KitHomotopy T}
  {𝕊C : SubCompose H}
  (C : ComposeTraversal 𝕊C)
  {TM : TypeSorts 𝕋}
  (ℂ  : CtxRepr TM)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude

open import Kitty.Term.Kit 𝕋
open Terms 𝕋
open Kitty.Typing.TypeSorts.TypeSorts TM
open CtxRepr ℂ
open import Kitty.Typing.OPE C ℂ
open Traversal T
open SubWithLaws 𝕊
open import Kitty.Term.Sub 𝕋
open Sub SubWithLaws-Sub
open Kit ⦃ … ⦄

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx S
    x y z : S ∋ s

private instance _ = Kᵣ; _ = Kₛ

_∋*_∶_ : Ctx S₂ → S₁ →ᵣ S₂ → Ctx S₁ → Set
_∋*_∶_ {S₂ = S₂} {S₁ = S₁} Γ₂ ϕ Γ₁ =
  ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) (⊢x : Γ₁ ∋ x ∶ t)
  → Γ₂ ∋ (x & ϕ) ∶ t ⋯ ϕ

record Typing : Set₁ where
  infix   4  _⊢_∶_
  field
    _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set

    ⊢` : ∀ {Γ : Ctx S} {x : S ∋ s} {t} →
         Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

    ≡ᶜ-cong-⊢ : ∀ {S st} {s : Sort st} {Γ₁ Γ₂ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → 
      Γ₁ ≡ᶜ Γ₂ →
      Γ₁ ⊢ e ∶ t →
      Γ₂ ⊢ e ∶ t

  _⊢*_∶_ : Ctx S₂ → S₁ →ₛ S₂ → Ctx S₁ → Set
  _⊢*_∶_ {S₂ = S₂} {S₁ = S₁} Γ₂ ϕ Γ₁ =
    ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ⊢ (x & ϕ) ∶ t ⋯ ϕ


open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Kitty.Util.List

~ᶜ-cong-wk-telescope : ∀ {S s} {Γ₁ Γ₂ : Ctx S} →
  Γ₁ ~ᶜ Γ₂ →
  (x : S ∋ s) →
  wk-telescope Γ₁ x ≡ wk-telescope Γ₂ x
~ᶜ-cong-wk-telescope {S} {s} {Γ₁} {Γ₂} Γ₁~Γ₂ x =
  let sub = subst (_∶⊢ s) (++-identityʳ (drop-∈ x S)) in
  wk-telescope Γ₁ x                ≡⟨⟩
  wk-drop-∈ x (lookup Γ₁ x)        ≡⟨⟩
  wk-drop-∈ x (sub (lookup' Γ₁ x)) ≡⟨ cong (λ ■ → wk-drop-∈ x (sub ■)) (Γ₁~Γ₂ _ x) ⟩
  wk-drop-∈ x (sub (lookup' Γ₂ x)) ≡⟨⟩
  wk-drop-∈ x (lookup Γ₂ x)        ≡⟨⟩
  wk-telescope Γ₂ x                ∎

≡ᶜ-cong-wk-telescope : {Γ₁ Γ₂ : Ctx S} →
  Γ₁ ≡ᶜ Γ₂ →
  (x : S ∋ s) →
  wk-telescope Γ₁ x ≡ wk-telescope Γ₂ x
≡ᶜ-cong-wk-telescope Γ₁~Γ₂ x = ~ᶜ-cong-wk-telescope (≡ᶜ→~ᶜ Γ₁~Γ₂) x

~₂-cong-∋ : ∀ {S s} {Γ₁ Γ₂ : Ctx S} (x : S ∋ s) {t : S ∶⊢ s} → 
  Γ₁ ~ᶜ Γ₂ →
  Γ₁ ∋ x ∶ t →
  Γ₂ ∋ x ∶ t
~₂-cong-∋ x Γ₁~Γ₂ refl = sym (~ᶜ-cong-wk-telescope Γ₁~Γ₂ x)

≡ᶜ-cong-∋ : ∀ {S s} {Γ₁ Γ₂ : Ctx S} (x : S ∋ s) {t : S ∶⊢ s} → 
  Γ₁ ≡ᶜ Γ₂ →
  Γ₁ ∋ x ∶ t →
  Γ₂ ∋ x ∶ t
≡ᶜ-cong-∋ x Γ₁~Γ₂ refl = sym (≡ᶜ-cong-wk-telescope Γ₁~Γ₂ x)
