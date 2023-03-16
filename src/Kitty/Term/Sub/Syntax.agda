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
open import Function using (_$_)

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

_&_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ ∋ m → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m
_&_  = ?

instance
  Sub-Syntax : Sub (lsuc 0ℓ) 
  Sub-Syntax = record
    { _–[_]→_ = _–[_]→_
    ; []ₖ     = []ₖ
    ; _,ₖ_    = _,ₖ_
    ; wkₖ     = wkₖ
    ; wkₖ*    = {!!}
    ; _↑_     = {!!}
    ; _↑*_    = {!!}
    ; id      = {!!}
    ; []*     = {!!}
    ; _↓      = {!!}
    ; _∥_     = {!!}
    ; ⦅_⦆     = {!!}
    ; ⦅_⦆₀    = {!!}
    ; _&_     = {!!}
    ; ι-→     = {!!}
    }
