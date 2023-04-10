open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)
open import Kitty.Typing.CtxRepr using (CtxRepr)

module Kitty.Typing.ITerms
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
open Modes 𝕄
open Terms 𝕋
open Kitty.Typing.Types.KitType KT
open CtxRepr ℂ
open import Kitty.Typing.OPE C KT ℂ
open Traversal T
open SubWithLaws 𝕊
open import Kitty.Term.Sub 𝕋
open Sub SubWithLaws-Sub
open Kit ⦃ … ⦄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m

private instance _ = kitᵣ; _ = kitₛ

_∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
_∋*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
  ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
  → Γ₂ ∋ (x & ϕ) ∶ t ⋯ ϕ

record ITerms : Set₁ where
  infix   4  _⊢_∶_
  field
    _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set

    ⊢` : ∀ {Γ : Ctx µ} {x : µ ∋ m} {t} →
         Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

    ≡ᶜ-cong-⊢ : ∀ {µ M} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} → 
      Γ₁ ≡ᶜ Γ₂ →
      Γ₁ ⊢ e ∶ t →
      Γ₂ ⊢ e ∶ t

  _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
  _⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
    ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ⊢ (x & ϕ) ∶ t ⋯ ϕ


open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Kitty.Util.List

~ᶜ-cong-wk-telescope : ∀ {µ m} {Γ₁ Γ₂ : Ctx µ} →
  Γ₁ ~ᶜ Γ₂ →
  (x : µ ∋ m) →
  wk-telescope Γ₁ x ≡ wk-telescope Γ₂ x
~ᶜ-cong-wk-telescope {µ} {m} {Γ₁} {Γ₂} Γ₁~Γ₂ x =
  let sub = subst (_∶⊢ m→M m) (++-identityʳ (drop-∈ x µ)) in
  wk-telescope Γ₁ x                ≡⟨⟩
  wk-drop-∈ x (lookup Γ₁ x)        ≡⟨⟩
  wk-drop-∈ x (sub (lookup' Γ₁ x)) ≡⟨ cong (λ ■ → wk-drop-∈ x (sub ■)) (Γ₁~Γ₂ _ x) ⟩
  wk-drop-∈ x (sub (lookup' Γ₂ x)) ≡⟨⟩
  wk-drop-∈ x (lookup Γ₂ x)        ≡⟨⟩
  wk-telescope Γ₂ x                ∎

≡ᶜ-cong-wk-telescope : {Γ₁ Γ₂ : Ctx µ} →
  Γ₁ ≡ᶜ Γ₂ →
  (x : µ ∋ m) →
  wk-telescope Γ₁ x ≡ wk-telescope Γ₂ x
≡ᶜ-cong-wk-telescope Γ₁~Γ₂ x = ~ᶜ-cong-wk-telescope (≡ᶜ→~ᶜ Γ₁~Γ₂) x

~₂-cong-∋ : ∀ {µ m} {Γ₁ Γ₂ : Ctx µ} (x : µ ∋ m) {t : µ ∶⊢ m→M m} → 
  Γ₁ ~ᶜ Γ₂ →
  Γ₁ ∋ x ∶ t →
  Γ₂ ∋ x ∶ t
~₂-cong-∋ x Γ₁~Γ₂ refl = sym (~ᶜ-cong-wk-telescope Γ₁~Γ₂ x)

≡ᶜ-cong-∋ : ∀ {µ m} {Γ₁ Γ₂ : Ctx µ} (x : µ ∋ m) {t : µ ∶⊢ m→M m} → 
  Γ₁ ≡ᶜ Γ₂ →
  Γ₁ ∋ x ∶ t →
  Γ₂ ∋ x ∶ t
≡ᶜ-cong-∋ x Γ₁~Γ₂ refl = sym (≡ᶜ-cong-wk-telescope Γ₁~Γ₂ x)
