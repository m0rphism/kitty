open import Kitty.Term.Modes

module Kitty.Term.Sub.Functional {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Level using (Level; _⊔_; 0ℓ)
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

open Kit ⦃ … ⦄ hiding (_,ₖ_; _↑_; _↑*_; _–→_; ~-cong-↑; ~-cong-↑*; _∥_; ⦅_⦆; _↓)

_–[_]→_ : List VarMode → Kit → List VarMode → Set
_–[_]→_ = λ µ₁ 𝕂 µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m)

[]ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ} → [] –[ 𝕂 ]→ µ
[]ₖ _ ()

_,ₖ_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
(ϕ ,ₖ t) _ (here refl) = t
(ϕ ,ₖ t) _ (there x)   = ϕ _ x

wkₖ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
wkₖ m ϕ mx x = wk (id/m→M mx) (ϕ mx x)

wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
wkₖ* []      ϕ = ϕ
wkₖ* (µ ▷ m) ϕ = wkₖ m (wkₖ* µ ϕ)

_↑_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
ϕ ↑ m = wkₖ m ϕ ,ₖ id/` _ (here refl)

_↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
ϕ ↑* []       = ϕ
ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

id : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
id = id/`

_↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → ((µ₁ ▷ m) –[ 𝕂 ]→ µ₂) → (µ₁ –[ 𝕂 ]→ µ₂)
(ϕ ↓) _ x = ϕ _ (there x)

_∥_ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
_∥_            {µ₂ = []}    σ₁ σ₂ = σ₁
_∥_ ⦃ 𝕂 ⦄ {µ₁} {µ₂ ▷ m} {µ} σ₁ σ₂ = subst (_–[ 𝕂 ]→ µ) (sym (++-assoc ([] ▷ m) µ₂ µ₁)) ((σ₁ ∥ (σ₂ ↓)) ,ₖ σ₂ _ (here refl))

⦅_⦆ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
⦅ v ⦆ = idₖ ,ₖ v

apₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
apₖ ϕ = ϕ

instance
  Sub-→ : Sub
  Sub-→ = record
    { _–[_]→_      = _–[_]→_
    ; []ₖ          = []ₖ
    ; _,ₖ_         = _,ₖ_
    ; wkₖ          = wkₖ
    ; wkₖ*         = wkₖ*
    ; _↑_          = _↑_
    ; _↑*_         = _↑*_
    ; id           = id
    ; []*          = []ₖ
    ; _↓           = _↓
    ; _∥_          = _∥_
    ; ⦅_⦆          = ⦅_⦆
    ; apₖ          = apₖ
    }

open Sub Sub-→ hiding (_–[_]→_; []ₖ; _,ₖ_; wkₖ; wkₖ*; _↑_; _↑*_; id; []*; _↓; _∥_; ⦅_⦆; apₖ)

id-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
  → id {µ ▷ m} ~ (id {µ} ↑ m)
id-▷ m (here refl) = refl
id-▷ m (there x) = sym (wk-id/` _ x)

invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ
invert' {µ₁ = []}      ϕ = ϕ~[]* refl (λ m ())
invert' {µ₁ = µ₁ ▷ m₁} ϕ = ϕ~,ₖ refl (ϕ ↓) (ϕ _ (here refl)) λ where
  m (here refl) → refl
  m (there x) → refl

instance
  SubWithLaws-→ : SubWithLaws
  SubWithLaws-→ = record
    { apₖ-,ₖ-here  = λ ϕ x/t → refl
    ; apₖ-,ₖ-there = λ ϕ x/t x → refl
    ; apₖ-wkₖ-wk   = λ ϕ x → refl
    ; apₖ-↓        = λ ϕ x → refl
    ; wkₖ*-[]      = λ ϕ m x → refl
    ; wkₖ*-▷       = λ µ m ϕ mx x → refl
    ; ↑-,ₖ         = λ ϕ m mx x → refl
    ; ↑*-[]        = λ ϕ m x → refl
    ; ↑*-▷         = λ µ m ϕ m₁ x → refl
    ; id-[]        = λ m ()
    ; id-▷         = id-▷
    ; []*-[]       = λ m x → refl
    ; []*-▷        = λ m ()
    ; ↓-,ₖ         = λ ϕ x/t m x → refl
    ; ∥-[]         = λ ϕ₁ ϕ₂ m x → refl
    ; ∥-▷          = λ ϕ₁ ϕ₂ m x → refl
    ; ⦅⦆-,ₖ        = λ x/t m x → refl
    ; invert'      = invert'
    }

-- open SubWithLaws SubWithLaws-→
-- x : ∀ ⦃ 𝕂 : Kit ⦄ (µ : List VarMode) (m : VarMode) → {!!}
-- x µ m = {!invert'-rec (id {µ ▷ m})!}
