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

open Kit ⦃ … ⦄

_–[_]→_ : List VarMode → Kit → List VarMode → Set
µ₁ –[ 𝕂 ]→ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m

[]ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ} → [] –[ 𝕂 ]→ µ
[]ₖ _ ()

_,ₖ_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
(ϕ ,ₖ t) _ (here refl) = t
(ϕ ,ₖ t) _ (there x)   = ϕ _ x

wkₖ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
wkₖ m ϕ mx x = wk m (ϕ mx x)

wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
wkₖ* []      ϕ = ϕ
wkₖ* (µ ▷ m) ϕ = wkₖ m (wkₖ* µ ϕ)

_↑_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
ϕ ↑ m = wkₖ m ϕ ,ₖ id/` (here refl)

_↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
ϕ ↑* []       = ϕ
ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

id : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
id m = id/`

_↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → ((µ₁ ▷ m) –[ 𝕂 ]→ µ₂) → (µ₁ –[ 𝕂 ]→ µ₂)
(ϕ ↓) _ x = ϕ _ (there x)

_∥_ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
_∥_            {µ₂ = []}    σ₁ σ₂ = σ₁
_∥_ ⦃ 𝕂 ⦄ {µ₁} {µ₂ ▷ m} {µ} σ₁ σ₂ = subst (_–[ 𝕂 ]→ µ) (sym (++-assoc ([] ▷ m) µ₂ µ₁)) ((σ₁ ∥ (σ₂ ↓)) ,ₖ σ₂ _ (here refl))

⦅_⦆ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
⦅ x/t ⦆ = id ,ₖ x/t

⦅_⦆₀ : ∀ ⦃ 𝕂 ⦄ {m} {µ} → µ ∋/⊢ id/m→M m → ([] ▷ m) –[ 𝕂 ]→ µ
⦅ x/t ⦆₀ = []ₖ ,ₖ x/t

_&_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ ∋ m → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m
x & ϕ = ϕ _ x

open import Kitty.Term.KitOrder 𝕋
open _⊑ₖ_ ⦃ … ⦄

ι-→ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂₁ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₂
ι-→ ϕ m x = ι-∋/⊢ (ϕ m x)

open import Kitty.Term.KitOrder 𝕋

instance
  Sub-→ : Sub 0ℓ
  Sub-→ = record
    { _–[_]→_ = _–[_]→_
    ; []ₖ     = []ₖ
    ; _,ₖ_    = _,ₖ_
    ; wkₖ     = wkₖ
    ; wkₖ*    = wkₖ*
    ; _↑_     = _↑_
    ; _↑*_    = _↑*_
    ; id      = id
    ; []*     = []ₖ
    ; _↓      = _↓
    ; _∥_     = _∥_
    ; ⦅_⦆     = ⦅_⦆
    ; ⦅_⦆₀    = ⦅_⦆₀
    ; _&_     = _&_
    ; ι-→     = ι-→
    }

open Sub Sub-→ hiding (_–[_]→_; []ₖ; _,ₖ_; wkₖ; wkₖ*; _↑_; _↑*_; id; []*; _↓; _∥_; ⦅_⦆; _&_)

id-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
  → id {µ ▷ m} ~ (id {µ} ↑ m)
id-▷ m (here refl) = refl
id-▷ m (there x) = sym (cong `/id (wk-id/` _ x))

invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ
invert' {µ₁ = []}      ϕ = ϕ~[]* refl (λ m ())
invert' {µ₁ = µ₁ ▷ m₁} ϕ = ϕ~,ₖ refl (ϕ ↓) (ϕ _ (here refl)) λ where
  m (here refl) → refl
  m (there x) → refl

instance
  SubWithLaws-→ : SubWithLaws 0ℓ
  SubWithLaws-→ = record
    { &-,ₖ-here  = λ ϕ x/t → refl
    ; &-,ₖ-there = λ ϕ x/t x → refl
    ; &-wkₖ-wk   = λ ϕ x → refl
    ; &-↓        = λ ϕ x → refl
    ; wkₖ*-[]    = λ ϕ m x → refl
    ; wkₖ*-▷     = λ µ m ϕ mx x → refl
    ; ↑-,ₖ       = λ ϕ m mx x → refl
    ; ↑*-[]      = λ ϕ m x → refl
    ; ↑*-▷       = λ µ m ϕ m₁ x → refl
    ; id-[]      = λ m ()
    ; id-▷       = id-▷
    ; []*-[]     = λ m x → refl
    ; []*-▷      = λ m ()
    ; ↓-,ₖ       = λ ϕ x/t m x → refl
    ; ∥-[]       = λ ϕ₁ ϕ₂ m x → refl
    ; ∥-▷        = λ ϕ₁ ϕ₂ m x → refl
    ; ⦅⦆-,ₖ      = λ x/t m x → refl
    ; ⦅⦆₀-,ₖ     = λ x/t m x → refl
    ; &-ι-→      = λ ϕ x → refl
    ; invert'    = invert'
    }

open import Kitty.Term.Traversal 𝕋 SubWithLaws-→
open import Kitty.Term.KitHomotopy 𝕋 SubWithLaws-→
module Fun-SubCompose (T : Traversal) (H : KitHomotopy T) where
  open Traversal T
  open KitHomotopy T H
  open import Kitty.Term.ComposeKit 𝕋 SubWithLaws-→ T H
  open import Kitty.Term.SubCompose 𝕋 SubWithLaws-→ T H
  open ComposeKit ⦃ … ⦄

  _·ₖ_ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ µ₃}
        → µ₁ –[ 𝕂₁ ]→ µ₂
        → µ₂ –[ 𝕂₂ ]→ µ₃
        → µ₁ –[ 𝕂  ]→ µ₃
  (ϕ₁ ·ₖ ϕ₂) m x = x & ϕ₁ &/⋯ ϕ₂

  SubCompose-→ : SubCompose
  SubCompose-→ = record
    { _·ₖ_     = _·ₖ_
    ; &-·ₖ-&/⋯ = λ ϕ₁ ϕ₂ x → refl
    }
