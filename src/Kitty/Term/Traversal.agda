open import Kitty.Term.Terms
import Kitty.Term.Sub as S

module Kitty.Term.Traversal
    (𝕋 : Terms)
    {ℓ} (𝕊 : S.SubWithLaws 𝕋 ℓ)
  where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Level using () renaming (suc to lsuc)

open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open Terms 𝕋
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws 𝕊
open _⊑ₖ_ ⦃ … ⦄

private variable
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx

private instance _ = Kᵣ

record Traversal : Set (lsuc ℓ) where
  infixl   5  _⋯_

  field
    _⋯_   :
      ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
        {S₁ S₂ st} {s : Sort st} 
      → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s

    ⋯-var :
      ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
        (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂)
      → (` x) ⋯ ϕ ≡ `/id (x & ϕ)

    ⋯-id :
      ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
        {S} {st} {s : Sort st} (t : S ⊢ s)
      → t ⋯ id ⦃ K = K ⦄ ≡ t

  Kₛ : Kit _⊢_
  Kit.id/`             Kₛ = `_
  Kit.`/id             Kₛ = λ t → t
  Kit.id/`/id          Kₛ = λ x → refl
  Kit.wk               Kₛ = λ s t → t ⋯ wkₖ _ id
  Kit.wk-id/`          Kₛ = λ s x →
    (` x) ⋯ wkₖ s id     ≡⟨ ⋯-var x (wkₖ s id) ⟩
    `/id (x & wkₖ s id)  ≡⟨ cong (`/id) (&-wkₖ-wk id x) ⟩
    `/id (wk _ (x & id)) ≡⟨ cong (`/id) (cong (wk _) (&-id x)) ⟩
    `/id (wk _ x)        ≡⟨⟩
    (` there x)          ∎
  Kit.kit-tag          Kₛ = K-Sub
  Kit.id/`-injective   Kₛ = λ eq → `-injective eq
  Kit.`/id-injective   Kₛ = λ eq → eq

  private instance _ = Kₛ

  ⊑-ᵣₛ : Kᵣ ⊑ₖ Kₛ
  ⊑-ᵣₛ = record
    { ι-∋/⊢    = `_
    ; ι-id/`   = λ x → refl
    ; ι-`/id   = λ x/t → refl
    ; ι-wk     = λ {s'} {s} {S} x →
        ` Kit.wk Kᵣ _ x   ≡⟨⟩
        ` there x           ≡⟨ cong (λ ■ → ` there ■) (sym (&-id x)) ⟩
        ` there (x & id)    ≡⟨ cong `_ (sym (&-wkₖ-wk id x)) ⟩
        ` (x & wkₖ _ id)    ≡⟨ sym (⋯-var ⦃ Kᵣ ⦄ x (wkₖ _ id)) ⟩
        (` x) ⋯ wkₖ _ id    ≡⟨⟩
        Kit.wk Kₛ _ (` x) ∎
    }

  ⊑ₖ-⊥ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
    → Kᵣ ⊑ₖ K
  ⊑ₖ-⊥ ⦃ K ⦄ = record
    { ι-∋/⊢    = Kit.id/` K
    ; ι-id/`   = λ x → refl
    ; ι-`/id   = λ x → sym (Kit.id/`/id K x)
    ; ι-wk     = λ x → sym (wk-id/` _ x)
    }

  infixl   5   _⋯ᵣ_  _⋯ₛ_ _⋯[_]_
  infixl   9  _∥ᵣ_  _∥ₛ_

  open Kit Kᵣ using () renaming (wk to wkᵣ; wk* to wk*ᵣ) public
  open Kit Kₛ using () renaming (wk to wkₛ; wk* to wk*ₛ) public

  -- Substitution / Renaming

  _→ᵣ_ : SortCtx → SortCtx → Set ℓ
  _→ₛ_ : SortCtx → SortCtx → Set ℓ
  _→ᵣ_ = _–[ Kᵣ ]→_
  _→ₛ_ = _–[ Kₛ ]→_

  -- Empty

  []ᵣ : [] →ᵣ []
  []ₛ : [] →ₛ []
  []ᵣ = []ₖ
  []ₛ = []ₖ

  []*ᵣ : ∀ {S₂} → [] →ᵣ S₂
  []*ₛ : ∀ {S₂} → [] →ₛ S₂
  []*ᵣ = []*
  []*ₛ = []*

  -- Extension

  _,ᵣ_ : ∀ {S₁} {S₂} {s} → S₁ →ᵣ S₂ → S₂ ∋ s → (S₁ ▷ s) →ᵣ S₂
  _,ₛ_ : ∀ {S₁} {S₂} {s} → S₁ →ₛ S₂ → S₂ ⊢ s → (S₁ ▷ s) →ₛ S₂
  _,ᵣ_ = _,ₖ_
  _,ₛ_ = _,ₖ_

  -- Weakening

  wk→ᵣ  : ∀ {S₁} {S₂} s → S₁ →ᵣ S₂ → S₁ →ᵣ (S₂ ▷ s)
  wk→ₛ  : ∀ {S₁} {S₂} s → S₁ →ₛ S₂ → S₁ →ₛ (S₂ ▷ s)
  wk→ᵣ* : ∀ {S₁} {S₂} S → S₁ →ᵣ S₂ → S₁ →ᵣ (S₂ ▷▷ S)
  wk→ₛ* : ∀ {S₁} {S₂} S → S₁ →ₛ S₂ → S₁ →ₛ (S₂ ▷▷ S)
  wk→ᵣ  = wkₖ
  wk→ₛ  = wkₖ
  wk→ᵣ* = wkₖ*
  wk→ₛ* = wkₖ*

  wkn :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ {S} {s}
    → S –[ K ]→ (S ▷ s)
  wkn = wkₖ _ id

  wknᵣ : ∀ {S} {s} → S →ᵣ (S ▷ s)
  wknₛ : ∀ {S} {s} → S →ₛ (S ▷ s)
  wknᵣ = wkn
  wknₛ = wkn

  wkn* :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ {S} S'
    → S –[ K ]→ (S ▷▷ S')
  wkn* S = wkₖ* S id

  wknᵣ* : ∀ {S} S' → S →ᵣ (S ▷▷ S')
  wknₛ* : ∀ {S} S' → S →ₛ (S ▷▷ S')
  wknᵣ* S = wkn* S
  wknₛ* S = wkn* S

  -- Lifting

  _↑ᵣ_  : ∀ {S₁} {S₂} → S₁ →ᵣ S₂ → ∀ s  → (S₁ ▷  s)  →ᵣ (S₂ ▷ s)
  _↑ₛ_  : ∀ {S₁} {S₂} → S₁ →ₛ S₂ → ∀ s  → (S₁ ▷  s)  →ₛ (S₂ ▷ s)
  _↑ᵣ*_ : ∀ {S₁} {S₂} → S₁ →ᵣ S₂ → ∀ S' → (S₁ ▷▷ S') →ᵣ (S₂ ▷▷ S')
  _↑ₛ*_ : ∀ {S₁} {S₂} → S₁ →ₛ S₂ → ∀ S' → (S₁ ▷▷ S') →ₛ (S₂ ▷▷ S')
  _↑ᵣ_  = _↑_
  _↑ₛ_  = _↑_
  _↑ᵣ*_ = _↑*_
  _↑ₛ*_ = _↑*_

  -- Identity

  idᵣ : ∀ {S} → S →ᵣ S
  idₛ : ∀ {S} → S →ₛ S
  idᵣ = id
  idₛ = id

  -- Lowering

  _↓ᵣ : ∀ {S₁} {S₂} {s} → (S₁ ▷ s) →ᵣ S₂ → S₁ →ᵣ S₂
  _↓ₛ : ∀ {S₁} {S₂} {s} → (S₁ ▷ s) →ₛ S₂ → S₁ →ₛ S₂
  _↓ᵣ = _↓
  _↓ₛ = _↓

  -- Parallel composition

  _∥ᵣ_ : ∀ {S₁ S₂ S} → (S₁ →ᵣ S) → (S₂ →ᵣ S) → ((S₁ ▷▷ S₂) →ᵣ S)
  _∥ₛ_ : ∀ {S₁ S₂ S} → (S₁ →ₛ S) → (S₂ →ₛ S) → ((S₁ ▷▷ S₂) →ₛ S)
  _∥ᵣ_ = _∥_
  _∥ₛ_ = _∥_

  -- Single substitution

  ⦅_⦆ᵣ  : ∀ {S S' s} → (S ▷▷ S') ∋ s → (S ▷ s)  →ᵣ (S ▷▷ S')
  ⦅_⦆ₛ  : ∀ {S S' s} → (S ▷▷ S') ⊢ s → (S ▷ s)  →ₛ (S ▷▷ S')
  ⦅_⦆ᵣ  = ⦅_⦆
  ⦅_⦆ₛ  = ⦅_⦆

  ⦅_⦆'ᵣ  : ∀ {S s} → S ∋ s → (S ▷ s)  →ᵣ S
  ⦅_⦆'ₛ  : ∀ {S s} → S ⊢ s → (S ▷ s)  →ₛ S
  ⦅_⦆'ᵣ  = ⦅_⦆
  ⦅_⦆'ₛ  = ⦅_⦆

  -- Singleton renaming/substitution for terms with 1 free variable.
  -- Allows the term to be substituted to have arbitrary free variables.
  -- This is useful for things like pattern matching in combination with `_∥_`,
  -- where a matching substitution needs to be built up piece by piece.
  ⦅_⦆ᵣ₀ : ∀ {S s} → S ∋ s → ([] ▷ s) →ᵣ S
  ⦅_⦆ₛ₀ : ∀ {S s} → S ⊢ s → ([] ▷ s) →ₛ S
  ⦅_⦆ᵣ₀ = ⦅_⦆₀
  ⦅_⦆ₛ₀ = ⦅_⦆₀

  -- Specialized application
  _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
  _⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
  _⋯ₛ_ = _⋯_
  _⋯ᵣ_ = _⋯_

  _⋯[_]_ :
    ∀ {_∋/⊢_ : VarScoped}
    → S₁ ⊢ s → (K : Kit _∋/⊢_) → S₁ –[ K ]→ S₂ → S₂ ⊢ s
  t ⋯[ K ] ϕ = t ⋯ ϕ where instance _ = K

  -- -- Alternative without duplication and `R.id` instead of `idᵣ`:
  -- module R = Kit Kᵣ
  -- module S = Kit Kₛ

  -- -- Composition

  -- infixr  10  _ᵣ∘ᵣ_  _ₛ∘ₛ_
  -- infixl  10  _ᵣ·ᵣ_  _ₛ·ₛ_
  -- infixr  10  _∘ᵣ_  _∘ₛ_  _ₛ∘ᵣ_  _ᵣ∘ₛ_
  -- infixl  10  _ᵣ·_  _ₛ·_  _ᵣ·ₛ_  _ₛ·ᵣ_

  -- -- Composition

  -- _ᵣ∘ᵣ_ : S₂ →ᵣ S₃ → S₁ →ᵣ S₂ → S₁ →ᵣ S₃
  -- _ₛ∘ₛ_ : S₂ →ₛ S₃ → S₁ →ₛ S₂ → S₁ →ₛ S₃
  -- _ᵣ∘ᵣ_ = _∘ₖ_
  -- _ₛ∘ₛ_ = _∘ₖ_

  -- _ᵣ·ᵣ_ : S₁ →ᵣ S₂ → S₂ →ᵣ S₃ → S₁ →ᵣ S₃
  -- _ₛ·ₛ_ : S₁ →ₛ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  -- _ᵣ·ᵣ_ = _·ₖ_
  -- _ₛ·ₛ_ = _·ₖ_

  -- _∘ᵣ_ : {{K : Kit}} → S₂ –[ K ]→ S₃ → S₁ →ᵣ S₂ → S₁ –[ K ]→ S₃
  -- _∘ₛ_ : {{K : Kit}} → S₂ –[ K ]→ S₃ → S₁ →ₛ S₂ → S₁ →ₛ S₃
  -- (ϕ ∘ᵣ ρ) _ x = ϕ _ (ρ _ x)
  -- (ϕ ∘ₛ σ) _ x = σ _ x ⋯ ϕ

  -- _ₛ∘ᵣ_ : S₂ →ₛ S₃ → S₁ →ᵣ S₂ → S₁ →ₛ S₃
  -- _ᵣ∘ₛ_ : S₂ →ᵣ S₃ → S₁ →ₛ S₂ → S₁ →ₛ S₃
  -- _ₛ∘ᵣ_ = _∘ᵣ_
  -- _ᵣ∘ₛ_ = _∘ₛ_

  -- -- Reverse composition

  -- _ᵣ·_ : {{K : Kit}} → S₁ →ᵣ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ K ]→ S₃
  -- _ₛ·_ : {{K : Kit}} → S₁ →ₛ S₂ → S₂ –[ K ]→ S₃ → S₁ →ₛ S₃
  -- ϕ₁ ᵣ·  ϕ₂ = ϕ₂ ∘ᵣ ϕ₁
  -- ϕ₁ ₛ·  ϕ₂ = ϕ₂ ∘ₛ ϕ₁

  -- _ᵣ·ₛ_ : S₁ →ᵣ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  -- _ₛ·ᵣ_ : S₁ →ₛ S₂ → S₂ →ᵣ S₃ → S₁ →ₛ S₃
  -- ϕ₁ ᵣ·ₛ ϕ₂ = ϕ₂ ∘ᵣ ϕ₁
  -- ϕ₁ ₛ·ᵣ ϕ₂ = ϕ₂ ∘ₛ ϕ₁

  -- -- Embedding renamings as substitutions

  -- toₛ : {{K : Kit}} → S₁ –[ K ]→ S₂ → S₁ →ₛ S₂
  -- toₛ ϕ = λ m x → `/id m (ϕ m x)
  -- -- toₛ ϕ = idₛ ∘ₖ ϕ

  -- ᵣtoₛ : S₁ →ᵣ S₂ → S₁ →ₛ S₂
  -- ᵣtoₛ ϕ = toₛ ϕ

  -- fromᵣ : {{K : Kit}} → S₁ →ᵣ S₂ → S₁ –[ K ]→ S₂
  -- fromᵣ ϕ = λ m x → id/` m (ϕ m x)

  -- ₛfromᵣ : S₁ →ᵣ S₂ → S₁ →ₛ S₂
  -- ₛfromᵣ ϕ = fromᵣ ϕ

  -- ₛfromᵣ' : S₁ →ᵣ S₂ → S₁ →ₛ S₂
  -- ₛfromᵣ' ϕ = λ m x → ` (ϕ m x)

  -- toₛ∘fromᵣ : {{K : Kit}} → (ϕ : S₁ →ᵣ S₂) → toₛ ⦃ K ⦄ (fromᵣ ⦃ K ⦄ ϕ) ~ ₛfromᵣ ϕ
  -- toₛ∘fromᵣ ϕ m x = id/`/id (ϕ m x)

  -- ₛfromᵣ≡ᵣtoₛ : (λ {S₁} {S₂} → ₛfromᵣ {S₁} {S₂}) ≡ (λ {S₁} {S₂} → ᵣtoₛ {S₁} {S₂})
  -- ₛfromᵣ≡ᵣtoₛ = refl

  -- ₛfromᵣ'≡ᵣtoₛ : (λ {S₁} {S₂} → ₛfromᵣ' {S₁} {S₂}) ≡ (λ {S₁} {S₂} → ᵣtoₛ {S₁} {S₂})
  -- ₛfromᵣ'≡ᵣtoₛ = refl
