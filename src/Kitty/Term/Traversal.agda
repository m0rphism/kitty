open import Kitty.Term.Modes
import Kitty.Term.Sub as S

module Kitty.Term.Traversal {𝕄 : Modes} (𝕋 : Terms 𝕄) {ℓ} (𝕊 : S.SubWithLaws 𝕋 ℓ) where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Level using () renaming (suc to lsuc)

open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open Modes 𝕄
open Terms 𝕋
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws 𝕊
open _⊑ₖ_ ⦃ … ⦄
open import Kitty.Term.MultiSub 𝕋

private variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

private instance _ = kitᵣ

record Traversal : Set (lsuc ℓ) where
  infixl   5  _⋯_

  field
    _⋯_   : ∀ ⦃ 𝕂 : Kit ⦄ → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

    ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
            → (` x) ⋯ ϕ ≡ `/id (x & ϕ)

    ⋯-id : ∀ ⦃ 𝕂 : Kit ⦄ {µ} {M} (t : µ ⊢ M)
            → t ⋯ id ⦃ 𝕂 = 𝕂 ⦄ ≡ t

  ~-ι-→ : ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
          → ϕ ~ ι-→ ϕ
  ~-ι-→ {µ₁} {µ₂} ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ ⦄ ϕ m x =
    let sub = subst (µ₂ ∋/⊢_) (ι-id/m→M m ) in
    `/id (x & ϕ)               ≡⟨ sym (ι-∋/⊢-~ₜ (x & ϕ)) ⟩
    `/id (sub (ι-∋/⊢ (x & ϕ))) ≡⟨ cong `/id (sym (ι-ap-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₁⊑𝕂₂ ⦄ ϕ x)) ⟩
    `/id (x & ι-→ ϕ)           ∎

  ⋯-var' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
           → let sub = subst (µ₂ ⊢_) (id/m→M/id m) in
             (` x) ⋯ ϕ ≡ sub (`/id' ⦃ 𝕂 ⦄ (x & ϕ))
  ⋯-var' ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} x ϕ =
    let sub = subst (µ₂ ⊢_) (id/m→M/id m) in
    (` x) ⋯ ϕ                 ≡⟨ ⋯-var x ϕ ⟩
    `/id (x & ϕ)              ≡⟨ `/id≡`/id' (x & ϕ) ⟩
    sub (`/id' ⦃ 𝕂 ⦄ (x & ϕ)) ∎

  kitₛ : Kit
  Kit.VarMode/TermMode kitₛ = TermMode
  Kit._∋/⊢_            kitₛ = _⊢_
  Kit.id/m→M           kitₛ = m→M
  Kit.m→M/id           kitₛ = λ M → M
  Kit.id/m→M/id        kitₛ = λ m → refl
  Kit.id/`             kitₛ = `_
  Kit.`/id             kitₛ = λ t → t
  Kit.`/id'            kitₛ = λ t → t
  Kit.id/`/id          kitₛ = λ x → refl
  Kit.id/`/id'         kitₛ = λ x → refl
  Kit.`/id≡`/id'       kitₛ = λ t → refl
  Kit.wk               kitₛ = λ M t → t ⋯ wkₖ _ id
  Kit.wk-id/`          kitₛ = λ m x →
    (` x) ⋯ wkₖ m id     ≡⟨ ⋯-var x (wkₖ m id) ⟩
    `/id (x & wkₖ m id)  ≡⟨ cong (`/id) (&-wkₖ-wk id x) ⟩
    `/id (wk _ (x & id)) ≡⟨ cong (`/id) (cong (wk _) (&-id x)) ⟩
    `/id (wk _ x)        ≡⟨⟩
    (` there x)          ∎
  Kit.kit-tag          kitₛ = K-Sub
  Kit.id/`-injective   kitₛ = λ eq → `-injective eq
  Kit.`/id-injective   kitₛ = λ eq → eq
  Kit.`/id'-injective  kitₛ = λ eq → eq

  private instance _ = kitₛ

  ⊑-ᵣₛ : kitᵣ ⊑ₖ kitₛ
  ⊑-ᵣₛ = record
    { ι-Mode   = m→M
    ; ι-id/m→M = λ m → refl
    ; ι-m→M/id = λ m/M → refl
    ; ι-∋/⊢    = `_
    ; ι-id/`   = λ x → refl
    ; ι-`/id   = λ x/t → refl
    ; ι-`/id'  = λ x/t → refl
    ; ι-wk     = λ {m'} {m} {µ} {m} x →
        ` Kit.wk kitᵣ _ x   ≡⟨⟩
        ` there x           ≡⟨ cong (λ ■ → ` there ■) (sym (&-id x)) ⟩
        ` there (x & id)    ≡⟨ cong `_ (sym (&-wkₖ-wk id x)) ⟩
        ` (x & wkₖ _ id)    ≡⟨ sym (⋯-var ⦃ kitᵣ ⦄ x (wkₖ _ id)) ⟩
        (` x) ⋯ wkₖ _ id    ≡⟨⟩
        Kit.wk kitₛ _ (` x) ∎
    ; ι-∋/⊢-id = λ ()
    ; ι-∋/⊢-~ₜ = λ x/t → refl
    ; ι-∋/⊢-~ₜ[] = λ x/t → refl
    }

  ⊑ₖ-⊥ : ∀ ⦃ 𝕂 : Kit ⦄ → kitᵣ ⊑ₖ 𝕂
  ⊑ₖ-⊥ ⦃ 𝕂 ⦄ = record
    { ι-Mode   = Kit.id/m→M 𝕂
    ; ι-id/m→M = λ m → refl
    ; ι-m→M/id = λ m → sym (Kit.id/m→M/id 𝕂 m)
    ; ι-∋/⊢    = Kit.id/` 𝕂
    ; ι-id/`   = λ x → refl
    ; ι-`/id   = λ x → sym (Kit.id/`/id 𝕂 x)
    ; ι-`/id'  = λ {µ} {m/M} x →
        let sub = subst (_⊢_ µ) (sym (sym (Kit.id/m→M/id 𝕂 m/M))) in
        let sub' = subst (_⊢_ µ) (Kit.id/m→M/id 𝕂 m/M) in
        Kit.`/id' kitᵣ x                  ≡⟨⟩
        ` x                               ≡⟨ sym (subst-sym (Kit.id/m→M/id 𝕂 m/M) _ (` x)
                                                            (Kit.id/`/id' 𝕂 x)) ⟩
        sub' (Kit.`/id' 𝕂 (Kit.id/` 𝕂 x)) ≡⟨ subst-irrelevant (Kit.id/m→M/id 𝕂 m/M) _ _ ⟩
        sub (Kit.`/id' 𝕂 (Kit.id/` 𝕂 x))  ∎
    ; ι-wk     = λ x → sym (wk-id/` _ x)
    ; ι-∋/⊢-id = λ { refl x/t → refl }
    ; ι-∋/⊢-~ₜ = id/`/id
    ; ι-∋/⊢-~ₜ[] = λ {µ} {m/M} x →
        let sub = subst (_⊢_ µ) (sym (sym (id/m→M/id m/M))) in
        let sub' = subst (_⊢_ µ) (id/m→M/id m/M) in
        sub (`/id' ⦃ 𝕂 ⦄ (id/` x))  ≡⟨ subst-irrelevant (sym (sym (id/m→M/id m/M))) (id/m→M/id m/M) (`/id' ⦃ 𝕂 ⦄ (id/` x)) ⟩
        sub' (`/id' ⦃ 𝕂 ⦄ (id/` x)) ≡⟨ subst-sym (id/m→M/id m/M) (`/id' ⦃ 𝕂 ⦄ (id/` x)) (` x) (id/`/id' x) ⟩
        Kit.`/id' kitᵣ x            ∎
    }

  infixl   5   _⋯ᵣ_  _⋯ₛ_ _⋯[_]_
  infixl   9  _∥ᵣ_  _∥ₛ_

  open Kit kitᵣ using () renaming (wk to wkᵣ; wk* to wk*ᵣ) public
  open Kit kitₛ using () renaming (wk to wkₛ; wk* to wk*ₛ) public

  -- Substitution / Renaming

  _→ᵣ_ : List VarMode → List VarMode → Set ℓ
  _→ₛ_ : List VarMode → List VarMode → Set ℓ
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

  wkn : ∀ ⦃ 𝕂 ⦄ {µ} {m} → µ –[ 𝕂 ]→ (µ ▷ m)
  wkn = wkₖ _ id

  wknᵣ : ∀ {µ} {m} → µ →ᵣ (µ ▷ m)
  wknₛ : ∀ {µ} {m} → µ →ₛ (µ ▷ m)
  wknᵣ = wkn
  wknₛ = wkn

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

  _⋯[_]_ : µ₁ ⊢ M → (𝕂 : Kit) → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  t ⋯[ 𝕂 ] ϕ = t ⋯ ϕ where instance _ = 𝕂

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
