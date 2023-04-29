open import Kitty.Term.Modes

module Kitty.Term.Sub.All {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _++_)
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

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties

_++A_ : ∀ {a b} {A : Set a} {P : A → Set b} → {xs ys : List A} → 
  All P xs → All P ys → All P (xs ++ ys)
[]         ++A pys = pys
(px ∷ pxs) ++A pys = px ∷ (pxs ++A pys)

_–[_]→_ : List VarMode → Kit → List VarMode → Set
µ₁ –[ 𝕂 ]→ µ₂ = All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁

[]ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ} → [] –[ 𝕂 ]→ µ
[]ₖ = []

_,ₖ_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
ϕ ,ₖ t = t ∷ ϕ

wkₖ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
wkₖ m ϕ = map (wk _) ϕ

wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
wkₖ* µ ϕ = map (wk* _) ϕ

_↑_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
ϕ ↑ m = wkₖ m ϕ ,ₖ id/` (here refl)

_↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
ϕ ↑* []       = ϕ
ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

id : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
id {µ = []}    = []
id {µ = µ ▷ m} = id {µ} ↑ m

_↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → ((µ₁ ▷ m) –[ 𝕂 ]→ µ₂) → (µ₁ –[ 𝕂 ]→ µ₂)
(x/t ∷ ϕ) ↓ = ϕ

_∥_ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
ϕ₁ ∥ ϕ₂ = ϕ₂ ++A ϕ₁

⦅_⦆ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
⦅ x/t ⦆ = id ,ₖ x/t

⦅_⦆₀ : ∀ ⦃ 𝕂 ⦄ {m} {µ} → µ ∋/⊢ id/m→M m → ([] ▷ m) –[ 𝕂 ]→ µ
⦅ x/t ⦆₀ = [] ,ₖ x/t

apₖ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
apₖ (x/t ∷ ϕ) m (here refl) = x/t
apₖ (x/t ∷ ϕ) m (there x) = apₖ ϕ m x

pre : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} → µ₂ –[ 𝕂 ]→ µ₃ → (∀ m → µ₁ ∋ m → µ₂ ∋ m) → µ₁ –[ 𝕂 ]→ µ₃
pre {µ₁ = []}     ϕ f = []
pre {µ₁ = µ₁ ▷ m} ϕ f = pre ϕ (λ _ x → f _ (there x)) ,ₖ apₖ ϕ _ (f m (here refl))

post : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → µ₃ ∋/⊢[ 𝕂 ] id/m→M m) → µ₁ –[ 𝕂 ]→ µ₃
post ϕ f = map (f _) ϕ

instance
  Sub-All : Sub 0ℓ
  Sub-All = record
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
    ; apₖ     = apₖ
    ; pre     = pre
    ; post    = post
    }

open Sub Sub-All hiding (_–[_]→_; []ₖ; _,ₖ_; wkₖ; wkₖ*; _↑_; _↑*_; id; []*; _↓; _∥_; ⦅_⦆; apₖ)

invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ
invert' []        = ϕ~[]* refl (λ m ())
invert' (x/t ∷ ϕ) = ϕ~,ₖ refl ϕ x/t (~-refl {f = x/t ∷ ϕ})

apₖ-wkₖ-wk : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
              → apₖ (wkₖ m ϕ) _ x ≡ wk _ (apₖ ϕ _ x)
apₖ-wkₖ-wk (x/t ∷ ϕ) (here refl) = refl
apₖ-wkₖ-wk (x/t ∷ ϕ) (there x)   = apₖ-wkₖ-wk ϕ x

wkₖ*-[] : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  → wkₖ* [] ϕ ~ ϕ
wkₖ*-[] ϕ m x = cong (λ ■ → apₖ ■ m x) (map-id ϕ)

wkₖ*-▷ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  → wkₖ* (µ ▷ m) ϕ ~ wkₖ m (wkₖ* µ ϕ)
wkₖ*-▷ µ m (x/t ∷ ϕ) mx (here refl) = refl
wkₖ*-▷ µ m (x/t ∷ ϕ) mx (there x)   = wkₖ*-▷ µ m ϕ mx x

instance
  SubWithLaws-→ : SubWithLaws
  SubWithLaws-→ = record
    { apₖ-,ₖ-here  = λ ϕ x/t → refl
    ; apₖ-,ₖ-there = λ ϕ x/t x → refl
    ; apₖ-wkₖ-wk   = apₖ-wkₖ-wk
    ; apₖ-↓        = λ { (x/t ∷ ϕ) x → refl }
    ; apₖ-pre      = λ ϕ f x → {!!}
    ; apₖ-post     = λ ϕ f x → {!!}
    ; wkₖ*-[]      = wkₖ*-[]
    ; wkₖ*-▷       = wkₖ*-▷
    ; ↑-,ₖ         = λ ϕ m mx x → refl
    ; ↑*-[]        = λ ϕ m x → refl
    ; ↑*-▷         = λ µ m ϕ m₁ x → refl
    ; id-[]        = λ m ()
    ; id-▷         = λ m x → refl
    ; []*-[]       = λ m x → refl
    ; []*-▷        = λ m ()
    ; ↓-,ₖ         = λ ϕ x/t m x → refl
    ; ∥-[]         = λ { ϕ₁ [] m x → refl }
    ; ∥-▷          = λ { ϕ₁ (x/t ∷ ϕ₂) m x → refl }
    ; ⦅⦆-,ₖ        = λ x/t m x → refl
    ; ⦅⦆₀-,ₖ       = λ x/t m x → refl
    ; invert'      = invert'
    }
