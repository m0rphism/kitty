open import Kitty.Term.Modes

module Kitty.Term.Sub.Syntax {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Data.Sum using (inj₁; inj₂; _⊎_)

open Modes 𝕄
open Terms 𝕋

open import Kitty.Term.Kit 𝕋 using (Kit; _∋/⊢[_]_)
open import Kitty.Term.Sub 𝕋

open Kit ⦃ … ⦄
open import Kitty.Term.KitOrder 𝕋
open _⊑ₖ_ ⦃ … ⦄

data _–[_]→_ : List VarMode → Kit → List VarMode → Set₁ where
  []ₖ  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→ []
  _,ₖ_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
  wkₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
  wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
  _↑_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
  _↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
  id   : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
  []*  : ∀ ⦃ 𝕂 ⦄ {µ₂} → [] –[ 𝕂 ]→ µ₂
  _↓   : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₂
  _∥_  : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
  ⦅_⦆  : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
  ⦅_⦆₀ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → ([] ▷ m) –[ 𝕂 ]→ µ
  ι-→  : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂₁ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₂

import Kitty.Term.Sub.Functional 𝕋 as F

⟦_⟧ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ F.–[ 𝕂 ]→ µ₂
⟦ []ₖ ⟧      = F.[]ₖ
⟦ ϕ ,ₖ x/t ⟧ = ⟦ ϕ ⟧ F.,ₖ x/t
⟦ wkₖ m ϕ ⟧  = F.wkₖ m ⟦ ϕ ⟧
⟦ wkₖ* µ ϕ ⟧ = F.wkₖ* µ ⟦ ϕ ⟧
⟦ ϕ ↑ m ⟧    = ⟦ ϕ ⟧ F.↑ m
⟦ ϕ ↑* µ' ⟧  = ⟦ ϕ ⟧ F.↑* µ'
⟦ id ⟧       = F.id
⟦ []* ⟧      = F.[]ₖ
⟦ ϕ ↓ ⟧      = ⟦ ϕ ⟧ F.↓
⟦ ϕ₁ ∥ ϕ₂ ⟧  = ⟦ ϕ₁ ⟧ F.∥ ⟦ ϕ₂ ⟧
⟦ ⦅ x/t ⦆ ⟧  = F.⦅ x/t ⦆
⟦ ⦅ x/t ⦆₀ ⟧ = F.⦅ x/t ⦆₀
⟦ ι-→ ϕ ⟧    = F.ι-→ ⟦ ϕ ⟧

_&_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ ∋ m → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m
x & f = ⟦ f ⟧ _ x

instance
  Sub-Syntax : Sub (lsuc 0ℓ) 
  Sub-Syntax = record
    { _–[_]→_ = _–[_]→_
    ; []ₖ     = []ₖ
    ; _,ₖ_    = _,ₖ_
    ; wkₖ     = wkₖ
    ; wkₖ*    = wkₖ*
    ; _↑_     = _↑_
    ; _↑*_    = _↑*_
    ; id      = id
    ; []*     = []*
    ; _↓      = _↓
    ; _∥_     = _∥_
    ; ⦅_⦆     = ⦅_⦆
    ; ⦅_⦆₀    = ⦅_⦆₀
    ; _&_     = _&_
    ; ι-→     = ι-→
    }

open Sub Sub-Syntax hiding (_–[_]→_; []ₖ; _,ₖ_; wkₖ; wkₖ*; _↑_; _↑*_; id; []*; _↓; _∥_; ⦅_⦆; _&_)

module FL = SubWithLaws F.SubWithLaws-→

instance
  SubWithLaws-Syntax : SubWithLaws (lsuc 0ℓ)
  SubWithLaws-Syntax = record
    { SubWithLaws-Sub = Sub-Syntax
    ; &-,ₖ-here  = λ ϕ x/t → FL.&-,ₖ-here ⟦ ϕ ⟧ x/t
    ; &-,ₖ-there = λ ϕ x/t x → FL.&-,ₖ-there ⟦ ϕ ⟧ x/t x
    ; &-wkₖ-wk   = λ ϕ x → FL.&-wkₖ-wk ⟦ ϕ ⟧ x
    ; &-↓        = λ ϕ x → FL.&-↓ ⟦ ϕ ⟧ x
    ; wkₖ*-[]    = λ ϕ m x → FL.wkₖ*-[] ⟦ ϕ ⟧ m x
    ; wkₖ*-▷     = λ µ m ϕ mx x → FL.wkₖ*-▷ µ m ⟦ ϕ ⟧ mx x
    ; ↑-,ₖ       = λ ϕ m mx x → FL.↑-,ₖ ⟦ ϕ ⟧ m mx x
    ; ↑*-[]      = λ ϕ m x → FL.↑*-[] ⟦ ϕ ⟧ m x
    ; ↑*-▷       = λ µ m ϕ mx x → FL.↑*-▷ µ m ⟦ ϕ ⟧ mx x
    ; id-[]      = FL.id-[]
    ; id-▷       = FL.id-▷
    ; []*-[]     = FL.[]*-[]
    ; []*-▷      = FL.[]*-▷
    ; ↓-,ₖ       = λ ϕ x/t m x → FL.↓-,ₖ ⟦ ϕ ⟧ x/t m x
    ; ∥-[]       = λ ϕ₁ ϕ₂ m x → FL.∥-[] ⟦ ϕ₁ ⟧ ⟦ ϕ₂ ⟧ m x
    ; ∥-▷        = λ ϕ₁ ϕ₂ m x → FL.∥-▷ ⟦ ϕ₁ ⟧ ⟦ ϕ₂ ⟧ m x
    ; ⦅⦆-,ₖ      = FL.⦅⦆-,ₖ
    ; ⦅⦆₀-,ₖ     = FL.⦅⦆₀-,ₖ
    ; invert'    = λ ϕ → {!FL.invert' ⟦ ϕ ⟧!}
    ; ι-ap-→     = λ ϕ x → FL.ι-ap-→ ⟦ ϕ ⟧ x
    }

open import Kitty.Term.Traversal 𝕋 SubWithLaws-Syntax
open import Kitty.Term.KitHomotopy 𝕋 SubWithLaws-Syntax
module Syntax-SubCompose (T : Traversal) (H : KitHomotopy T) where
  open Traversal T
  open KitHomotopy T H
  open import Kitty.Term.ComposeKit 𝕋 SubWithLaws-Syntax T H
  open import Kitty.Term.SubCompose 𝕋 SubWithLaws-Syntax T H
  open ComposeKit ⦃ … ⦄

  _·ₖ_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ µ₃}
        → µ₁ –[ 𝕂₁ ]→ µ₂
        → µ₂ –[ 𝕂₂ ]→ µ₃
        → µ₁ –[ 𝕂  ]→ µ₃
  _·ₖ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} ϕ₁ ϕ₂ =
    {!!}
    -- λ m x → subst (µ₃ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) (x & ϕ₁ &/⋯ ϕ₂)

  SubCompose-Syntax : SubCompose
  SubCompose-Syntax = record
    { _·ₖ_     = _·ₖ_
    ; &-·ₖ-&/⋯ = {!!}
    }
