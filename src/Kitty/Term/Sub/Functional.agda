open import Kitty.Term.Terms

module Kitty.Term.Sub.Functional (𝕋 : Terms) where

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

open Terms 𝕋

open import Kitty.Term.Kit 𝕋 using (Kit; _∋/⊢[_]_)
open import Kitty.Term.Sub 𝕋

open Kit ⦃ … ⦄

_–[_]→_ : ∀ {_∋/⊢_ : VarScoped} → SortCtx → Kit _∋/⊢_ → SortCtx → Set
S₁ –[ 𝕂 ]→ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢[ 𝕂 ] s

[]ₖ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} → [] –[ 𝕂 ]→ S
[]ₖ _ ()

_,ₖ_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ s} → S₁ –[ 𝕂 ]→ S₂ → S₂ ∋/⊢ s → (S₁ ▷ s) –[ 𝕂 ]→ S₂
(ϕ ,ₖ t) _ (here refl) = t
(ϕ ,ₖ t) _ (there x)   = ϕ _ x

wkₖ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} s → S₁ –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ (S₂ ▷ s)
wkₖ s ϕ mx x = wk s (ϕ mx x)

wkₖ* : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S → S₁ –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ (S₂ ▷▷ S)
wkₖ* []      ϕ = ϕ
wkₖ* (S ▷ s) ϕ = wkₖ s (wkₖ* S ϕ)

_↑_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂 ]→ S₂ → ∀ s → (S₁ ▷ s) –[ 𝕂 ]→ (S₂ ▷ s)
ϕ ↑ s = wkₖ s ϕ ,ₖ id/` (here refl)

_↑*_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂 ]→ S₂ → ∀ S' → (S₁ ▷▷ S') –[ 𝕂 ]→ (S₂ ▷▷ S')
ϕ ↑* []       = ϕ
ϕ ↑* (S' ▷ s) = (ϕ ↑* S') ↑ s

id : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} → S –[ 𝕂 ]→ S
id s = id/`

_↓ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → ((S₁ ▷ s) –[ 𝕂 ]→ S₂) → (S₁ –[ 𝕂 ]→ S₂)
(ϕ ↓) _ x = ϕ _ (there x)

_∥_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ S} → (S₁ –[ 𝕂 ]→ S) → (S₂ –[ 𝕂 ]→ S) → ((S₁ ▷▷ S₂) –[ 𝕂 ]→ S)
_∥_            {S₂ = []}    σ₁ σ₂ = σ₁
_∥_ ⦃ 𝕂 ⦄ {S₁} {S₂ ▷ s} {S} σ₁ σ₂ = subst (_–[ 𝕂 ]→ S) (sym (++-assoc ([] ▷ s) S₂ S₁)) ((σ₁ ∥ (σ₂ ↓)) ,ₖ σ₂ _ (here refl))

⦅_⦆ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S S' s} → (S ▷▷ S') ∋/⊢ s → (S ▷ s) –[ 𝕂 ]→ (S ▷▷ S')
⦅ x/t ⦆ = wkₖ* _ id ,ₖ x/t

⦅_⦆₀ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {s} {S} → S ∋/⊢ s → ([] ▷ s) –[ 𝕂 ]→ S
⦅ x/t ⦆₀ = []ₖ ,ₖ x/t

_&_  : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → S₁ ∋ s → S₁ –[ 𝕂 ]→ S₂ → S₂ ∋/⊢ s
x & ϕ = ϕ _ x

open import Kitty.Term.KitOrder 𝕋
open _⊑ₖ_ ⦃ … ⦄

ι-→ :
  ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
    {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
    ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {S₁} {S₂} →
  S₁ –[ 𝕂₁ ]→ S₂ →
  S₁ –[ 𝕂₂ ]→ S₂
ι-→ ϕ s x = ι-∋/⊢ (ϕ s x)

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

id-▷ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s}
  → id {S = S ▷ s} ~ (id {S = S} ↑ s)
id-▷ = mk-~ λ where
  s (here refl) → refl
  s (there x)   → sym (cong `/id (wk-id/` _ x))

invert' : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) → Invert-ϕ' ϕ
invert' {S₁ = []}      ϕ = ϕ~[]* refl (mk-~ λ s ())
invert' {S₁ = S₁ ▷ s₁} ϕ = ϕ~,ₖ refl (ϕ ↓) (ϕ _ (here refl)) (mk-~ λ where
  s (here refl) → refl
  s (there x) → refl)

instance
  SubWithLaws-→ : SubWithLaws 0ℓ
  SubWithLaws-→ = record
    { &-,ₖ-here  = λ ϕ x/t → refl
    ; &-,ₖ-there = λ ϕ x/t x → refl
    ; &-wkₖ-wk   = λ ϕ x → refl
    ; &-↓        = λ ϕ x → refl
    ; wkₖ*-[]    = λ ϕ → mk-~ λ s x → refl
    ; wkₖ*-▷     = λ S s ϕ → mk-~ λ mx x → refl
    ; ↑-,ₖ       = λ ϕ s → mk-~ λ mx x → refl
    ; ↑*-[]      = λ ϕ → mk-~ λ s x → refl
    ; ↑*-▷       = λ S s ϕ → mk-~ λ s₁ x → refl
    ; id-[]      = mk-~ λ s ()
    ; id-▷       = id-▷
    ; []*-[]     = mk-~ λ s x → refl
    ; []*-▷      = mk-~ λ s ()
    ; ↓-,ₖ       = λ ϕ x/t → mk-~ λ s x → refl
    ; ∥-[]       = λ ϕ₁ ϕ₂ → mk-~ λ s x → refl
    ; ∥-▷        = λ ϕ₁ ϕ₂ → mk-~ λ s x → refl
    ; ⦅⦆-,ₖ      = λ x/t → mk-~ λ s x → refl
    ; ⦅⦆₀-,ₖ     = λ x/t → mk-~ λ s x → refl
    ; &-ι-→      = λ ϕ x → refl
    ; invert'    = invert'
    }

open import Kitty.Term.Traversal 𝕋 SubWithLaws-→
open import Kitty.Term.KitHomotopy {𝕋 = 𝕋} {𝕊 = SubWithLaws-→}
module Fun-SubCompose {T : Traversal} (H : KitHomotopy T) where
  open Traversal T
  open KitHomotopy T H
  open import Kitty.Term.ComposeKit H
  open import Kitty.Term.SubCompose H
  open ComposeKit ⦃ … ⦄

  _·ₖ_ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_  : VarScoped} ⦃ 𝕂  : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {S₁ S₂ S₃}
        → S₁ –[ 𝕂₁ ]→ S₂
        → S₂ –[ 𝕂₂ ]→ S₃
        → S₁ –[ 𝕂  ]→ S₃
  (ϕ₁ ·ₖ ϕ₂) s x = x & ϕ₁ &/⋯ ϕ₂

  SubCompose-→ : SubCompose
  SubCompose-→ = record
    { _·ₖ_     = _·ₖ_
    ; &-·ₖ-&/⋯ = λ ϕ₁ ϕ₂ x → refl
    }
