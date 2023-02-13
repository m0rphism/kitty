open import Kitty.Term.Modes

module Kitty.Term.Traversal {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude

open Modes 𝕄
open Terms 𝕋

open import Kitty.Term.Kit 𝕋
open import Kitty.Term.Sub 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- open import Kitty.Util.Homotopy
-- open ~-Reasoning

open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄

record Traversal : Set₁ where
  infixl   8  _⋯_

  field
    _⋯_   : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄
            → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ; 𝕊 ]→ µ₂)
            → (` x) ⋯ ϕ ≡ `/id _ (apₖ ϕ _ x)
    -- ⋯-var' : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –→ µ₂)
    --         → let sub = subst (µ₂ ⊢_) (id/m→M/id m) in
    --           (` x) ⋯ ϕ ≡ sub (`/id' _ (ϕ _ x))

  -- TODO: This could also be defined outside of Traversal.
  kitᵣ : Kit
  Kit.VarMode/TermMode kitᵣ = VarMode
  Kit._∋/⊢_            kitᵣ = _∋_
  Kit.id/m→M           kitᵣ = λ m → m
  Kit.m→M/id           kitᵣ = m→M
  Kit.id/m→M/id        kitᵣ = λ m → refl
  Kit.id/`             kitᵣ = λ m x → x
  Kit.`/id             kitᵣ = λ m x → ` x
  Kit.`/id'            kitᵣ = λ m x → ` x
  Kit.id/`/id          kitᵣ = λ x → refl
  Kit.id/`/id'         kitᵣ = λ x → refl
  Kit.wk               kitᵣ = λ m x → there x
  Kit.wk-id/`          kitᵣ = λ m x → refl
  Kit.kit-tag          kitᵣ = K-Ren

  private instance _ = kitᵣ

  kitₛ : ⦃ 𝕊 : SubWithLaws ⦄ → Kit
  Kit.VarMode/TermMode kitₛ = TermMode
  Kit._∋/⊢_            kitₛ = _⊢_
  Kit.id/m→M           kitₛ = m→M
  Kit.m→M/id           kitₛ = λ M → M
  Kit.id/m→M/id        kitₛ = λ m → refl
  Kit.id/`             kitₛ = λ m x → ` x
  Kit.`/id             kitₛ = λ M t → t
  Kit.`/id'            kitₛ = λ M t → t
  Kit.id/`/id          kitₛ = λ x → refl
  Kit.id/`/id'         kitₛ = λ x → refl
  Kit.wk               kitₛ = λ M t → t ⋯ wkₖ _ id
  Kit.wk-id/`          kitₛ = λ m x →
    (` x) ⋯ wkₖ m id            ≡⟨ ⋯-var x (wkₖ m id) ⟩
    `/id _ (apₖ (wkₖ m id) _ x) ≡⟨ cong (`/id _) (apₖ-wkₖ-wk id x) ⟩
    `/id _ (wk _ (apₖ id _ x))  ≡⟨ cong (`/id _) (cong (wk _) (apₖ-id x)) ⟩
    `/id _ (wk _ x)             ≡⟨⟩
    (` there x)                 ∎
  Kit.kit-tag          kitₛ = K-Sub

  private instance _ = kitₛ

  module Specialized ⦃ 𝕊 : SubWithLaws ⦄ where
    infixl   8   _⋯ᵣ_  _⋯ₛ_
    infixl   9  _∥ᵣ_  _∥ₛ_

    open Kit kitᵣ using () renaming (wk to wkᵣ) public
    open Kit kitₛ using () renaming (wk to wkₛ) public

    -- Substitution / Renaming

    _→ᵣ_ : List VarMode → List VarMode → Set
    _→ₛ_ : List VarMode → List VarMode → Set
    _→ᵣ_ = _–[ kitᵣ ]→_
    _→ₛ_ = _–[ kitₛ ]→_

    -- Empty

    []ᵣ : [] →ᵣ []
    []ₛ : [] →ₛ []
    []ᵣ = []ₖ
    []ₛ = []ₖ

    []*ᵣ : ∀ {µ₂} → [] →ᵣ µ₂
    []*ₛ : ∀ {µ₂} → [] →ₛ µ₂
    []*ᵣ = []*
    []*ₛ = []*

    -- Extension

    _,ᵣ_ : ∀ {µ₁} {µ₂} {m} → µ₁ →ᵣ µ₂ → µ₂ ∋ m     → (µ₁ ▷ m) →ᵣ µ₂
    _,ₛ_ : ∀ {µ₁} {µ₂} {m} → µ₁ →ₛ µ₂ → µ₂ ⊢ m→M m → (µ₁ ▷ m) →ₛ µ₂
    _,ᵣ_ = _,ₖ_
    _,ₛ_ = _,ₖ_

    -- Weakening

    wk→ᵣ  : ∀ {µ₁} {µ₂} m → µ₁ →ᵣ µ₂ → µ₁ →ᵣ (µ₂ ▷ m)
    wk→ₛ  : ∀ {µ₁} {µ₂} m → µ₁ →ₛ µ₂ → µ₁ →ₛ (µ₂ ▷ m)
    wk→ᵣ* : ∀ {µ₁} {µ₂} µ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ (µ₂ ▷▷ µ)
    wk→ₛ* : ∀ {µ₁} {µ₂} µ → µ₁ →ₛ µ₂ → µ₁ →ₛ (µ₂ ▷▷ µ)
    wk→ᵣ  = wkₖ
    wk→ₛ  = wkₖ
    wk→ᵣ* = wkₖ*
    wk→ₛ* = wkₖ*

    -- Lifting

    _↑ᵣ_  : ∀ {µ₁} {µ₂} → µ₁ →ᵣ µ₂ → ∀ m  → (µ₁ ▷  m)  →ᵣ (µ₂ ▷ m)
    _↑ₛ_  : ∀ {µ₁} {µ₂} → µ₁ →ₛ µ₂ → ∀ m  → (µ₁ ▷  m)  →ₛ (µ₂ ▷ m)
    _↑ᵣ*_ : ∀ {µ₁} {µ₂} → µ₁ →ᵣ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') →ᵣ (µ₂ ▷▷ µ')
    _↑ₛ*_ : ∀ {µ₁} {µ₂} → µ₁ →ₛ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') →ₛ (µ₂ ▷▷ µ')
    _↑ᵣ_  = _↑_
    _↑ₛ_  = _↑_
    _↑ᵣ*_ = _↑*_
    _↑ₛ*_ = _↑*_

    -- Identity

    idᵣ : ∀ {µ} → µ →ᵣ µ
    idₛ : ∀ {µ} → µ →ₛ µ
    idᵣ = id
    idₛ = id

    -- Lowering

    _↓ᵣ : ∀ {µ₁} {µ₂} {m} → (µ₁ ▷ m) →ᵣ µ₂ → µ₁ →ᵣ µ₂
    _↓ₛ : ∀ {µ₁} {µ₂} {m} → (µ₁ ▷ m) →ₛ µ₂ → µ₁ →ₛ µ₂
    _↓ᵣ = _↓
    _↓ₛ = _↓

    -- Parallel composition

    _∥ᵣ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ᵣ µ) → (µ₂ →ᵣ µ) → ((µ₁ ▷▷ µ₂) →ᵣ µ)
    _∥ₛ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ₛ µ) → (µ₂ →ₛ µ) → ((µ₁ ▷▷ µ₂) →ₛ µ)
    _∥ᵣ_ = _∥_
    _∥ₛ_ = _∥_

    -- Single substitution

    ⦅_⦆ᵣ  : ∀ {µ m} → µ ∋ m     → (µ ▷ m)  →ᵣ µ
    ⦅_⦆ₛ  : ∀ {µ m} → µ ⊢ m→M m → (µ ▷ m)  →ₛ µ
    ⦅_⦆ᵣ  = ⦅_⦆
    ⦅_⦆ₛ  = ⦅_⦆

    -- Singleton renaming/substitution for terms with 1 free variable.
    -- Allows the term to be substituted to have arbitrary free variables.
    -- This is useful for things like pattern matching in combination with `_∥_`,
    -- where a matching substitution needs to be built up piece by piece.
    ⦅_⦆ᵣ₀ : ∀ {µ m} → µ ∋ m     → ([] ▷ m) →ᵣ µ
    ⦅_⦆ₛ₀ : ∀ {µ m} → µ ⊢ m→M m → ([] ▷ m) →ₛ µ
    ⦅_⦆ᵣ₀ = ⦅_⦆₀
    ⦅_⦆ₛ₀ = ⦅_⦆₀

    -- Specialized application
    _⋯ₛ_ : µ₁ ⊢ M → µ₁ →ₛ µ₂ → µ₂ ⊢ M
    _⋯ᵣ_ : µ₁ ⊢ M → µ₁ →ᵣ µ₂ → µ₂ ⊢ M
    _⋯ₛ_ = _⋯_
    _⋯ᵣ_ = _⋯_

  open Specialized public

  -- -- Alternative without duplication and `R.id` instead of `idᵣ`:
  -- module R = Kit kitᵣ
  -- module S = Kit kitₛ

  -- -- Composition

  -- infixr  10  _ᵣ∘ᵣ_  _ₛ∘ₛ_
  -- infixl  10  _ᵣ·ᵣ_  _ₛ·ₛ_
  -- infixr  10  _∘ᵣ_  _∘ₛ_  _ₛ∘ᵣ_  _ᵣ∘ₛ_
  -- infixl  10  _ᵣ·_  _ₛ·_  _ᵣ·ₛ_  _ₛ·ᵣ_

  -- -- Composition

  -- _ᵣ∘ᵣ_ : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
  -- _ₛ∘ₛ_ : µ₂ →ₛ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  -- _ᵣ∘ᵣ_ = _∘ₖ_
  -- _ₛ∘ₛ_ = _∘ₖ_

  -- _ᵣ·ᵣ_ : µ₁ →ᵣ µ₂ → µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₃
  -- _ₛ·ₛ_ : µ₁ →ₛ µ₂ → µ₂ →ₛ µ₃ → µ₁ →ₛ µ₃
  -- _ᵣ·ᵣ_ = _·ₖ_
  -- _ₛ·ₛ_ = _·ₖ_

  -- _∘ᵣ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₃
  -- _∘ₛ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  -- (ϕ ∘ᵣ ρ) _ x = ϕ _ (ρ _ x)
  -- (ϕ ∘ₛ σ) _ x = σ _ x ⋯ ϕ

  -- _ₛ∘ᵣ_ : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
  -- _ᵣ∘ₛ_ : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  -- _ₛ∘ᵣ_ = _∘ᵣ_
  -- _ᵣ∘ₛ_ = _∘ₛ_

  -- -- Reverse composition

  -- _ᵣ·_ : {{K : Kit}} → µ₁ →ᵣ µ₂ → µ₂ –[ K ]→ µ₃ → µ₁ –[ K ]→ µ₃
  -- _ₛ·_ : {{K : Kit}} → µ₁ →ₛ µ₂ → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₃
  -- ϕ₁ ᵣ·  ϕ₂ = ϕ₂ ∘ᵣ ϕ₁
  -- ϕ₁ ₛ·  ϕ₂ = ϕ₂ ∘ₛ ϕ₁

  -- _ᵣ·ₛ_ : µ₁ →ᵣ µ₂ → µ₂ →ₛ µ₃ → µ₁ →ₛ µ₃
  -- _ₛ·ᵣ_ : µ₁ →ₛ µ₂ → µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₃
  -- ϕ₁ ᵣ·ₛ ϕ₂ = ϕ₂ ∘ᵣ ϕ₁
  -- ϕ₁ ₛ·ᵣ ϕ₂ = ϕ₂ ∘ₛ ϕ₁

  -- -- Embedding renamings as substitutions

  -- toₛ : {{K : Kit}} → µ₁ –[ K ]→ µ₂ → µ₁ →ₛ µ₂
  -- toₛ ϕ = λ m x → `/id m (ϕ m x)
  -- -- toₛ ϕ = idₛ ∘ₖ ϕ

  -- ᵣtoₛ : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  -- ᵣtoₛ ϕ = toₛ ϕ

  -- fromᵣ : {{K : Kit}} → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₂
  -- fromᵣ ϕ = λ m x → id/` m (ϕ m x)

  -- ₛfromᵣ : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  -- ₛfromᵣ ϕ = fromᵣ ϕ

  -- ₛfromᵣ' : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  -- ₛfromᵣ' ϕ = λ m x → ` (ϕ m x)

  -- toₛ∘fromᵣ : {{K : Kit}} → (ϕ : µ₁ →ᵣ µ₂) → toₛ ⦃ K ⦄ (fromᵣ ⦃ K ⦄ ϕ) ~ ₛfromᵣ ϕ
  -- toₛ∘fromᵣ ϕ m x = id/`/id (ϕ m x)

  -- ₛfromᵣ≡ᵣtoₛ : (λ {µ₁} {µ₂} → ₛfromᵣ {µ₁} {µ₂}) ≡ (λ {µ₁} {µ₂} → ᵣtoₛ {µ₁} {µ₂})
  -- ₛfromᵣ≡ᵣtoₛ = refl

  -- ₛfromᵣ'≡ᵣtoₛ : (λ {µ₁} {µ₂} → ₛfromᵣ' {µ₁} {µ₂}) ≡ (λ {µ₁} {µ₂} → ᵣtoₛ {µ₁} {µ₂})
  -- ₛfromᵣ'≡ᵣtoₛ = refl
  
-- record KitHomotopy (T : Traversal) : Set₁ where
--   open Traversal T
--   field
--     ~-cong-⋯ :
--       ∀ ⦃ 𝕂 : Kit ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂} (t : µ₁ ⊢ M)
--       → f ~ g
--       → t ⋯ f ≡ t ⋯ g

-- open import Axiom.Extensionality.Propositional using (Extensionality)

-- Extensionality→KitHomotopy : ∀ {T} → Extensionality 0ℓ 0ℓ → KitHomotopy T
-- Extensionality→KitHomotopy {T} fun-ext =
--   let open Traversal T in record
--   { ~-cong-⋯ = λ t f~g → cong (t ⋯_) (fun-ext (λ m → fun-ext (λ x → f~g m x))) }
