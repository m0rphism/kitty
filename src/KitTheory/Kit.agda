open import KitTheory.Modes

module KitTheory.Kit {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import KitTheory.Prelude

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

fun-ext₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

record Kit : Set₁ where
  infix   4  _◆_
  infixl  5  _,ₖ_
  infixl  6  _↑_  _↑*_

  field
    StuffMode : Set
    _◆_       : Stuff StuffMode
    m→SM      : VarMode → StuffMode
    SM→M      : StuffMode → TermMode
    vr        : ∀ m → µ ∋ m → µ ◆ m→SM m
    tm        : ∀ m → µ ◆ m→SM m → µ ⊢ m→M m
    wk        : ∀ SM → µ ◆ SM → (µ ▷ m') ◆ SM
    m→SM→M    : ∀ m → SM→M (m→SM m) ≡ m→M m
    wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
    tm-vr     : ∀ x → tm {µ = µ} m (vr _ x) ≡ ` x

  wk* : ∀ SM → µ ◆ SM → (µ ▷▷ µ') ◆ SM
  wk* {µ' = []} sm x = x
  wk* {µ' = µ' ▷ m} sm x = wk sm (wk* sm x)

  _–→_ : List VarMode → List VarMode → Set
  _–→_ µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ◆ m→SM m

  idₖ : µ –→ µ
  idₖ = vr

  -- TODO: Can we express this as weakened f + ,ₖ ?
  _↑_ : µ₁ –→ µ₂ → ∀ m → (µ₁ ▷ m) –→ (µ₂ ▷ m)
  (ϕ ↑ m) _ (here p)  = vr _ (here p)
  (ϕ ↑ m) _ (there x) = wk _ (ϕ _ x)

  _↑*_ : µ₁ –→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –→ (µ₂ ▷▷ µ')
  ϕ ↑* []       = ϕ
  ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

  id↑≡id : ∀ m µ → idₖ {µ = µ} ↑ m ≡ idₖ {µ = µ ▷ m}
  id↑≡id m µ = fun-ext₂ λ where
    _ (here _)  → refl
    _ (there x) → wk-vr m x

  id↑*≡id : ∀ µ' µ → idₖ {µ = µ} ↑* µ' ≡ idₖ {µ = µ ▷▷ µ'}
  id↑*≡id []       µ = refl
  id↑*≡id (µ' ▷ m) µ =
    (idₖ ↑* µ') ↑ m ≡⟨ cong (_↑ m) (id↑*≡id µ' µ) ⟩
    idₖ ↑ m         ≡⟨ id↑≡id m (µ ▷▷ µ') ⟩
    idₖ             ∎

  -- Extending a renaming/substitution
  _,ₖ_ : µ₁ –→ µ₂ → µ₂ ◆ m→SM m → (µ₁ ▷ m) –→ µ₂
  (ϕ ,ₖ t) _ (here refl) = t
  (ϕ ,ₖ t) _ (there x)   = ϕ _ x

  -- Singleton renaming/substitution
  ⦅_⦆ : µ ◆ m→SM m → (µ ▷ m) –→ µ
  ⦅ v ⦆ = idₖ ,ₖ v

open Kit {{...}}

_◆[_]_ : List VarMode → (𝕂 : Kit) → Kit.StuffMode 𝕂 → Set
µ ◆[ 𝕂 ] sm = Kit._◆_ 𝕂 µ sm

_–[_]→_ : List VarMode → (_ : Kit) → List VarMode → Set _
µ₁ –[ 𝕂 ]→ µ₂ = Kit._–→_ 𝕂 µ₁ µ₂

_∥_ : ∀ {{𝕂}} {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
_∥_ {µ₂ = []}     σ₁ σ₂ _ x = σ₁ _ x
_∥_ {µ₂ = µ₂ ▷ _} σ₁ σ₂ _ (here px) = σ₂ _ (here px)
_∥_ {µ₂ = µ₂ ▷ _} σ₁ σ₂ _ (there x) = (σ₁ ∥ (λ m y → σ₂ m (there y))) _ x

record KitTraversal : Set₁ where
  infixl  5  _⋯_  _⋯ᵣ_  _⋯ₛ_

  field
    _⋯_   : ∀ {{𝕂 : Kit}} →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (ϕ : µ₁ –→ µ₂) →
            (` x) ⋯ ϕ ≡ tm _ (ϕ _ x)

  -- TODO: This could also be defined outside of KitTraversal.
  kitᵣ : Kit
  Kit.StuffMode kitᵣ = VarMode
  Kit._◆_       kitᵣ = _∋_
  Kit.m→SM      kitᵣ = λ x → x
  Kit.SM→M      kitᵣ = m→M
  Kit.vr        kitᵣ = λ _ x → x
  Kit.tm        kitᵣ = λ _ → `_
  Kit.wk        kitᵣ = λ _ → there
  Kit.m→SM→M    kitᵣ = λ _ → refl
  Kit.wk-vr     kitᵣ = λ _ _ → refl
  Kit.tm-vr     kitᵣ = λ _ → refl

  private instance _ = kitᵣ

  kitₛ : Kit
  Kit.StuffMode kitₛ = TermMode
  Kit._◆_       kitₛ = _⊢_
  Kit.m→SM      kitₛ = m→M
  Kit.SM→M      kitₛ = λ x → x
  Kit.vr        kitₛ = λ _ → `_
  Kit.tm        kitₛ = λ _ x → x
  Kit.wk        kitₛ = λ _ x → x ⋯ wk
  Kit.m→SM→M    kitₛ = λ _ → refl
  Kit.wk-vr     kitₛ = λ _ x → ⋯-var x wk
  Kit.tm-vr     kitₛ = λ x → refl

  private instance _ = kitₛ

  open Kit kitᵣ using () renaming (wk to wkᵣ; _–→_ to _→ᵣ_; idₖ to idᵣ; _↑_ to _↑ᵣ_; _,ₖ_ to _,ᵣ_; ⦅_⦆ to ⦅_⦆ᵣ) public
  open Kit kitₛ using () renaming (wk to wkₛ; _–→_ to _→ₛ_; idₖ to idₛ; _↑_ to _↑ₛ_; _,ₖ_ to _,ₛ_; ⦅_⦆ to ⦅_⦆ₛ) public

  -- Alternative without duplication and `R.id` instead of `idᵣ`:
  module R = Kit kitᵣ
  module S = Kit kitₛ

  _⋯ₛ_ : µ₁ ⊢ M → µ₁ →ₛ µ₂ → µ₂ ⊢ M
  _⋯ₛ_ = _⋯_

  _⋯ᵣ_ : µ₁ ⊢ M → µ₁ →ᵣ µ₂ → µ₂ ⊢ M
  _⋯ᵣ_ = _⋯_

  _∘ᵣ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₃
  (ϕ ∘ᵣ ρ) _ x = ϕ _ (ρ _ x)

  _∘ₛ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  (ϕ ∘ₛ σ) _ x = σ _ x ⋯ ϕ

  _ᵣ∘ᵣ_ : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
  _ₛ∘ᵣ_ : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ₛ_ : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ₛ∘ₛ_ : µ₂ →ₛ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_
  _ᵣ∘ₛ_ = _∘ₛ_
  _ₛ∘ₛ_ = _∘ₛ_

  _∥ᵣ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ᵣ µ) → (µ₂ →ᵣ µ) → ((µ₁ ▷▷ µ₂) →ᵣ µ)
  _∥ᵣ_ = _∥_

  _∥ₛ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ₛ µ) → (µ₂ →ₛ µ) → ((µ₁ ▷▷ µ₂) →ₛ µ)
  _∥ₛ_ = _∥_
