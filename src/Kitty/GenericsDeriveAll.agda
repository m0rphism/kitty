module Kitty.GenericsDeriveExamples where

open import Kitty.Prelude
open import Kitty.Modes
open import Kitty.Generics hiding (⟦_⟧)
open import Kitty.GenericsDerive

open import Data.List using (List; []; _∷_)

open import Kitty.Iso
-- open import Kitty.Kit using (Kit; KitTraversal)
-- open import Kitty.Compose using (ComposeKit; KitAssoc)
-- open KitAssoc using (KitAssocLemmas)

module Modules {𝕄 : Modes} {_⊢_ : Scoped 𝕄} {d : Desc 𝕄} (iso : ∀ {µ} {e} → (µ ⊢ e) ≃ Tm 𝕄 d µ e) where
  private module I = FromIso 𝕄 iso
  open import Kitty.Kit I.terms using (Kit; KitTraversal) public
  open import Kitty.Compose I.terms I.kit-traversal using (ComposeKit; KitAssoc) public
  open KitAssoc I.kit-assoc using (WkDistKit; KitAssocLemmas) public

open import Relation.Binary.PropositionalEquality using (_≡_)
module Derived {𝕄 : Modes} {_⊢_ : Scoped 𝕄} {d : Desc 𝕄} (iso : ∀ {µ} {e} → (µ ⊢ e) ≃ Tm 𝕄 d µ e) where
  module I = FromIso 𝕄 iso

  open Modes 𝕄
  open Terms I.terms using (`_)

  private variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

  open Modules iso public using (Kit; KitTraversal; ComposeKit; KitAssoc; WkDistKit; KitAssocLemmas)

  terms            : Terms 𝕄
  kit-traversal    : KitTraversal
  kit-assoc        : KitAssoc
  kit-assoc-lemmas : KitAssocLemmas
  kitᵣ             : Kit
  kitₛ             : Kit
  kitᵣ             = I.kitᵣ
  kitₛ             = I.kitₛ
  kitᵣᵣ            : ComposeKit ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄
  kitᵣₛ            : ComposeKit ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄
  kitₛᵣ            : ComposeKit ⦃ kitₛ ⦄ ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄
  kitₛₛ            : ComposeKit ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄
  wk-kitᵣ          : WkDistKit ⦃ kitᵣ ⦄ ⦃ kitᵣᵣ ⦄ ⦃ kitᵣᵣ ⦄
  wk-kitₛ          : WkDistKit ⦃ kitₛ ⦄ ⦃ kitₛᵣ ⦄ ⦃ kitᵣₛ ⦄

  open Kit {{...}} using (_∋/⊢_; id/m→M; `/id; VarMode/TermMode)

  -- _∋/⊢_    : ⦃ K : Kit ⦄ → List VarMode → Kit.VarMode/TermMode K → Set 
  _∋/⊢[_]_ : List VarMode → (K : Kit) → Kit.VarMode/TermMode K → Set
  µ ∋/⊢[ K ] m/M = Kit._∋/⊢_ K µ m/M

  _→ᵣ_    : List VarMode → List VarMode → Set _
  _→ₛ_    : List VarMode → List VarMode → Set _
  _–→_    : ⦃ K : Kit ⦄ → List VarMode → List VarMode → Set _
  _–[_]→_ : List VarMode → Kit → List VarMode → Set _
  µ₁ →ᵣ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋ m
  µ₁ →ₛ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ⊢ m→M m
  µ₁ –→ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m
  µ₁ –[ K ]→ µ₂ = µ₁ –→ µ₂ where instance _ = K

  wk  : ∀ ⦃ K : Kit ⦄ m/M → µ ∋/⊢ m/M → (µ ▷ m') ∋/⊢ m/M
  wkᵣ : ∀ m → µ ∋ m → (µ ▷ m') ∋ m
  wkₛ : ∀ M → µ ⊢ M → (µ ▷ m') ⊢ M

  wk*  : ∀ ⦃ K : Kit ⦄ m/M → µ ∋/⊢ m/M → (µ ▷▷ µ') ∋/⊢ m/M
  wkᵣ* : ∀ m → µ ∋ m → (µ ▷▷ µ') ∋ m
  wkₛ* : ∀ M → µ ⊢ M → (µ ▷▷ µ') ⊢ M

  id  : ⦃ K : Kit ⦄ → µ –→ µ
  idᵣ : µ →ᵣ µ
  idₛ : µ →ₛ µ

  _↑_  : ⦃ K : Kit ⦄ → µ₁ –[ K ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ K ]→ (µ₂ ▷ m)
  _↑ᵣ_ : µ₁ →ᵣ µ₂ → ∀ m → (µ₁ ▷ m) →ᵣ (µ₂ ▷ m)
  _↑ₛ_ : µ₁ →ₛ µ₂ → ∀ m → (µ₁ ▷ m) →ₛ (µ₂ ▷ m)

  _↑*_  : ⦃ K : Kit ⦄ → µ₁ –→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –→ (µ₂ ▷▷ µ')
  _↑ᵣ*_ : µ₁ →ᵣ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') →ᵣ (µ₂ ▷▷ µ')
  _↑ₛ*_ : µ₁ →ₛ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') →ₛ (µ₂ ▷▷ µ')

  id↑≡id  : ⦃ K : Kit ⦄ → ∀ m µ → id ↑ m ≡ id {µ = µ ▷ m}
  id↑≡idᵣ : ∀ m µ → idᵣ ↑ᵣ m ≡ idᵣ {µ = µ ▷ m}
  id↑≡idₛ : ∀ m µ → idₛ ↑ₛ m ≡ idₛ {µ = µ ▷ m}

  id↑*≡id : ⦃ K : Kit ⦄ → ∀ µ' µ → id ↑* µ' ≡ id {µ = µ ▷▷ µ'}
  id↑*≡idᵣ : ∀ µ' µ → idᵣ ↑ᵣ* µ' ≡ idᵣ {µ = µ ▷▷ µ'}
  id↑*≡idₛ : ∀ µ' µ → idₛ ↑ₛ* µ' ≡ idₛ {µ = µ ▷▷ µ'}

  _,ₖ_ : ⦃ K : Kit ⦄ → µ₁ –[ K ]→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –[ K ]→ µ₂
  _,ᵣ_ : µ₁ →ᵣ µ₂ → µ₂ ∋     m → (µ₁ ▷ m) →ᵣ µ₂
  _,ₛ_ : µ₁ →ₛ µ₂ → µ₂ ⊢ m→M m → (µ₁ ▷ m) →ₛ µ₂

  ⦅_⦆  : ⦃ K : Kit ⦄ → µ ∋/⊢ id/m→M m → (µ ▷ m) –→ µ
  ⦅_⦆ᵣ : µ ∋     m → (µ ▷ m) →ᵣ µ
  ⦅_⦆ₛ : µ ⊢ m→M m → (µ ▷ m) →ₛ µ

  ⦅_⦆₀  : ⦃ K : Kit ⦄ → µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
  ⦅_⦆₀ᵣ : µ ∋     m → ([] ▷ m) →ᵣ µ
  ⦅_⦆₀ₛ : µ ⊢ m→M m → ([] ▷ m) →ₛ µ

  0ₖ : ⦃ K : Kit ⦄ → [] –[ K ]→ µ
  0ᵣ : [] →ᵣ µ
  0ₛ : [] →ₛ µ

  wk'   : ⦃ K : Kit ⦄ → µ –→ (µ ▷ m)
  wkᵣ'  : µ →ᵣ (µ ▷ m)
  wkₛ'  : µ →ₛ (µ ▷ m)

  wk'*  : ⦃ K : Kit ⦄ → µ –→ (µ ▷▷ µ')
  wkᵣ'* : µ →ᵣ (µ ▷▷ µ')
  wkₛ'* : µ →ₛ (µ ▷▷ µ')

  _⋯_     : ⦃ K : Kit ⦄ → µ₁ ⊢ M → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ M
  _⋯ₛ_    : µ₁ ⊢ M → µ₁ →ₛ µ₂ → µ₂ ⊢ M
  _⋯ᵣ_    : µ₁ ⊢ M → µ₁ →ᵣ µ₂ → µ₂ ⊢ M

  ⟦_⟧ₖ : ⦃ K : Kit ⦄ → µ₁ –[ K ]→ µ₂ → (µ₁ ⊢ M → µ₂ ⊢ M)
  ⟦_⟧ₛ : µ₁ →ₛ µ₂ → (µ₁ ⊢ M → µ₂ ⊢ M)
  ⟦_⟧ᵣ : µ₁ →ᵣ µ₂ → (µ₁ ⊢ M → µ₂ ⊢ M)

  ⟦ ϕ ⟧ₖ e = e ⋯ ϕ
  ⟦ ϕ ⟧ₛ e = e ⋯ₛ ϕ
  ⟦ ϕ ⟧ᵣ e = e ⋯ᵣ ϕ

  _∘_     : ⦃ K₁ K₂ K : Kit ⦄ ⦃ _ : ComposeKit ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦄ → µ₂ –[ K₁ ]→ µ₃ → µ₁ –[ K₂ ]→ µ₂ → µ₁ –[ K ]→ µ₃
  _∘ᵣ_    : ⦃ K : Kit ⦄ → µ₂ –[ K ]→ µ₃ → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₃
  _∘ₛ_    : ⦃ K : Kit ⦄ → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ᵣ_   : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
  _ₛ∘ᵣ_   : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ₛ_   : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ₛ∘ₛ_   : µ₂ →ₛ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃

  dist-↑-∘ : ∀ ⦃ K₁ K₂ K : Kit ⦄ ⦃ _ : ComposeKit ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦄
               m (ϕ₁ : µ₂ –[ K₁ ]→ µ₃) (ϕ₂ : µ₁ –[ K₂ ]→ µ₂)
             → (ϕ₁ ∘ ϕ₂) ↑ m ≡ (ϕ₁ ↑ m) ∘ (ϕ₂ ↑ m)
  dist-↑-ᵣ∘ᵣ : ∀ m (ϕ₁ : µ₂ →ᵣ µ₃) (ϕ₂ : µ₁ →ᵣ µ₂)
               → (ϕ₁ ᵣ∘ᵣ ϕ₂) ↑ᵣ m ≡ (ϕ₁ ↑ᵣ m) ᵣ∘ᵣ (ϕ₂ ↑ᵣ m)
  dist-↑-ᵣ∘ₛ : ∀ m (ϕ₁ : µ₂ →ᵣ µ₃) (ϕ₂ : µ₁ →ₛ µ₂)
               → (ϕ₁ ᵣ∘ₛ ϕ₂) ↑ₛ m ≡ (ϕ₁ ↑ᵣ m) ᵣ∘ₛ (ϕ₂ ↑ₛ m)
  dist-↑-ₛ∘ᵣ : ∀ m (ϕ₁ : µ₂ →ₛ µ₃) (ϕ₂ : µ₁ →ᵣ µ₂)
               → (ϕ₁ ₛ∘ᵣ ϕ₂) ↑ₛ m ≡ (ϕ₁ ↑ₛ m) ₛ∘ᵣ (ϕ₂ ↑ᵣ m)
  dist-↑-ₛ∘ₛ : ∀ m (ϕ₁ : µ₂ →ₛ µ₃) (ϕ₂ : µ₁ →ₛ µ₂)
               → (ϕ₁ ₛ∘ₛ ϕ₂) ↑ₛ m ≡ (ϕ₁ ↑ₛ m) ₛ∘ₛ (ϕ₂ ↑ₛ m)

  dist-↑*-∘ : ∀ ⦃ K₁ K₂ K : Kit ⦄ ⦃ _ : ComposeKit ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦄
                µ (ϕ₁ : µ₂ –[ K₁ ]→ µ₃) (ϕ₂ : µ₁ –[ K₂ ]→ µ₂)
              → (ϕ₁ ∘ ϕ₂) ↑* µ ≡ (ϕ₁ ↑* µ) ∘ (ϕ₂ ↑* µ)
  dist-↑*-ᵣ∘ᵣ : ∀ µ (ϕ₁ : µ₂ →ᵣ µ₃) (ϕ₂ : µ₁ →ᵣ µ₂)
               → (ϕ₁ ᵣ∘ᵣ ϕ₂) ↑ᵣ* µ ≡ (ϕ₁ ↑ᵣ* µ) ᵣ∘ᵣ (ϕ₂ ↑ᵣ* µ)
  dist-↑*-ᵣ∘ₛ : ∀ µ (ϕ₁ : µ₂ →ᵣ µ₃) (ϕ₂ : µ₁ →ₛ µ₂)
               → (ϕ₁ ᵣ∘ₛ ϕ₂) ↑ₛ* µ ≡ (ϕ₁ ↑ᵣ* µ) ᵣ∘ₛ (ϕ₂ ↑ₛ* µ)
  dist-↑*-ₛ∘ᵣ : ∀ µ (ϕ₁ : µ₂ →ₛ µ₃) (ϕ₂ : µ₁ →ᵣ µ₂)
               → (ϕ₁ ₛ∘ᵣ ϕ₂) ↑ₛ* µ ≡ (ϕ₁ ↑ₛ* µ) ₛ∘ᵣ (ϕ₂ ↑ᵣ* µ)
  dist-↑*-ₛ∘ₛ : ∀ µ (ϕ₁ : µ₂ →ₛ µ₃) (ϕ₂ : µ₁ →ₛ µ₂)
               → (ϕ₁ ₛ∘ₛ ϕ₂) ↑ₛ* µ ≡ (ϕ₁ ↑ₛ* µ) ₛ∘ₛ (ϕ₂ ↑ₛ* µ)

  ⋯-assoc : ∀ ⦃ K₁ K₂ K : Kit ⦄ ⦃ _ : ComposeKit ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦄
              (v : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ K₂ ]→ µ₂) (ϕ₂ : µ₂ –[ K₁ ]→ µ₃) →
    (v ⋯ ϕ₁) ⋯ ϕ₂ ≡ v ⋯ (ϕ₂ ∘ ϕ₁)

  _∥_     : ⦃ K : Kit ⦄ → ∀ {µ₁ µ₂ µ} → (µ₁ –[ K ]→ µ) → (µ₂ –[ K ]→ µ) → ((µ₁ ▷▷ µ₂) –[ K ]→ µ)
  _∥ᵣ_    : ∀ {µ₁ µ₂ µ} → (µ₁ →ᵣ µ) → (µ₂ →ᵣ µ) → ((µ₁ ▷▷ µ₂) →ᵣ µ)
  _∥ₛ_    : ∀ {µ₁ µ₂ µ} → (µ₁ →ₛ µ) → (µ₂ →ₛ µ) → ((µ₁ ▷▷ µ₂) →ₛ µ)

  ⋯-var   : ⦃ K : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –[ K ]→ µ₂) →
            (` x) ⋯ ϕ ≡ `/id _ (ϕ _ x)

  comm-↑-wk :
    ∀ ⦃ 𝕂 : Kit ⦄
      ⦃ 𝔸₁ : ComposeKit ⦃ 𝕂 ⦄    ⦃ kitᵣ ⦄ ⦃ 𝕂 ⦄ ⦄
      ⦃ 𝔸₂ : ComposeKit ⦃ kitᵣ ⦄ ⦃ 𝕂 ⦄    ⦃ 𝕂 ⦄ ⦄
      ⦃ W : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦄
      (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
    → let instance _ = kitᵣ in
      (ϕ ↑ m) ∘ wkᵣ ≡ wkᵣ ∘ ϕ

  comm-↑ᵣ-wk : ∀ (ϕ : µ₁ →ᵣ µ₂) → (ϕ ↑ᵣ m) ᵣ∘ᵣ wkᵣ ≡ wkᵣ ᵣ∘ᵣ ϕ
  comm-↑ₛ-wk : ∀ (ϕ : µ₁ →ₛ µ₂) → (ϕ ↑ₛ m) ₛ∘ᵣ wkᵣ ≡ wkᵣ ᵣ∘ₛ ϕ

  wk-cancels-,ₖ-∘ :
    ∀ ⦃ 𝕂 : Kit ⦄
      ⦃ 𝔸₁ : ComposeKit ⦃ 𝕂 ⦄    ⦃ kitᵣ ⦄ ⦃ 𝕂 ⦄ ⦄
      ⦃ 𝔸₂ : ComposeKit ⦃ kitᵣ ⦄ ⦃ 𝕂 ⦄    ⦃ 𝕂 ⦄ ⦄
      ⦃ W : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄ ⦄
      (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
    → let instance _ = kitᵣ in
      (ϕ ,ₖ v) ∘ wkᵣ ≡ ϕ

  wk-cancels-,ᵣ-∘ : ∀ (ϕ : µ₁ →ᵣ µ₂) (v : µ₂ ∋     m) → (ϕ ,ᵣ v) ᵣ∘ᵣ wkᵣ ≡ ϕ
  wk-cancels-,ₛ-∘ : ∀ (ϕ : µ₁ →ₛ µ₂) (v : µ₂ ⊢ m→M m) → (ϕ ,ₛ v) ₛ∘ᵣ wkᵣ ≡ ϕ

  ⋯-id : ∀ ⦃ 𝕂 : Kit ⦄ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

  ⋯-idₛ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitₛ}} ≡ v
  ⋯-idₛ = ⋯-id

  ⋯-idᵣ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitᵣ}} ≡ v
  ⋯-idᵣ = ⋯-id


  module KIT = Kit {{...}}
  module CKIT = ComposeKit {{...}}
  module WKKIT = WkDistKit {{...}}

  terms            = I.terms
  kit-traversal    = I.kit-traversal
  kit-assoc        = I.kit-assoc
  kit-assoc-lemmas = I.kit-assoc-lemmas
  kitᵣᵣ            = I.kitᵣᵣ
  kitᵣₛ            = I.kitᵣₛ
  kitₛᵣ            = I.kitₛᵣ
  kitₛₛ            = I.kitₛₛ
  wk-kitᵣ          = I.wk-kitᵣ
  wk-kitₛ          = I.wk-kitₛ

  -- _∋/⊢_ = KIT._∋/⊢_

  wk  = KIT.wk
  wkᵣ = I.wkᵣ
  wkₛ = I.wkₛ

  wk*  = KIT.wk*
  wkᵣ* = Kit.wk* kitᵣ
  wkₛ* = Kit.wk* kitₛ

  id = KIT.idₖ
  idᵣ = I.idᵣ
  idₛ = I.idₛ

  _↑_ = KIT._↑_
  _↑ᵣ_ = I._↑ᵣ_
  _↑ₛ_ = I._↑ₛ_

  _↑*_  = KIT._↑*_
  _↑ᵣ*_ = Kit._↑*_ kitᵣ
  _↑ₛ*_ = Kit._↑*_ kitₛ

  id↑≡id  = KIT.id↑≡id
  id↑≡idᵣ = Kit.id↑≡id kitᵣ
  id↑≡idₛ = Kit.id↑≡id kitₛ

  id↑*≡id = KIT.id↑*≡id
  id↑*≡idᵣ = Kit.id↑*≡id kitᵣ
  id↑*≡idₛ = Kit.id↑*≡id kitₛ

  _,ₖ_ = KIT._,ₖ_
  _,ᵣ_ = I._,ᵣ_
  _,ₛ_ = I._,ₛ_

  ⦅_⦆  = KIT.⦅_⦆
  ⦅_⦆ᵣ = I.⦅_⦆ᵣ
  ⦅_⦆ₛ = I.⦅_⦆ₛ

  ⦅_⦆₀  = KIT.⦅_⦆₀
  ⦅_⦆₀ᵣ = Kit.⦅_⦆₀ kitᵣ
  ⦅_⦆₀ₛ = Kit.⦅_⦆₀ kitₛ

  0ₖ = KIT.emptyₖ
  0ᵣ = Kit.emptyₖ kitᵣ
  0ₛ = Kit.emptyₖ kitₛ

  wk'   = KIT.wk'
  wkᵣ'  = Kit.wk' kitᵣ
  wkₛ'  = Kit.wk' kitₛ

  wk'*  = KIT.wk'*
  wkᵣ'* = Kit.wk'* kitᵣ
  wkₛ'* = Kit.wk'* kitₛ

  _⋯_     = I._⋯_
  _⋯ₛ_    = I._⋯ₛ_
  _⋯ᵣ_    = I._⋯ᵣ_

  _∘_     = CKIT._∘ₖ_
  _∘ᵣ_    = I._∘ᵣ_
  _∘ₛ_    = I._∘ₛ_
  _ᵣ∘ᵣ_   = I._ᵣ∘ᵣ_
  _ₛ∘ᵣ_   = I._ₛ∘ᵣ_
  _ᵣ∘ₛ_   = I._ᵣ∘ₛ_
  _ₛ∘ₛ_   = I._ₛ∘ₛ_

  dist-↑-∘ = CKIT.dist-↑-∘
  dist-↑-ᵣ∘ᵣ = ComposeKit.dist-↑-∘ ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄ kitᵣᵣ
  dist-↑-ᵣ∘ₛ = ComposeKit.dist-↑-∘ ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ kitᵣₛ
  dist-↑-ₛ∘ᵣ = ComposeKit.dist-↑-∘ ⦃ kitₛ ⦄ ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄ kitₛᵣ
  dist-↑-ₛ∘ₛ = ComposeKit.dist-↑-∘ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ kitₛₛ

  dist-↑*-∘ = CKIT.dist-↑*-∘
  dist-↑*-ᵣ∘ᵣ = ComposeKit.dist-↑*-∘ ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄ ⦃ kitᵣ ⦄ kitᵣᵣ
  dist-↑*-ᵣ∘ₛ = ComposeKit.dist-↑*-∘ ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ kitᵣₛ
  dist-↑*-ₛ∘ᵣ = ComposeKit.dist-↑*-∘ ⦃ kitₛ ⦄ ⦃ kitᵣ ⦄ ⦃ kitₛ ⦄ kitₛᵣ
  dist-↑*-ₛ∘ₛ = ComposeKit.dist-↑*-∘ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ ⦃ kitₛ ⦄ kitₛₛ

  ⋯-assoc = I.⋯-assoc

  _∥_     = KIT._∥_
  _∥ᵣ_    = I._∥ᵣ_
  _∥ₛ_    = I._∥ₛ_

  ⋯-var   = I.⋯-var

  comm-↑-wk = WKKIT.comm-↑-wk
  comm-↑ᵣ-wk = WkDistKit.comm-↑-wk ⦃ kitᵣ ⦄ ⦃ kitᵣᵣ ⦄ ⦃ kitᵣᵣ ⦄ wk-kitᵣ
  comm-↑ₛ-wk = WkDistKit.comm-↑-wk ⦃ kitₛ ⦄ ⦃ kitₛᵣ ⦄ ⦃ kitᵣₛ ⦄ wk-kitₛ

  wk-cancels-,ₖ-∘ = WKKIT.wk-cancels-,ₖ-∘
  wk-cancels-,ᵣ-∘ = WkDistKit.wk-cancels-,ₖ-∘ ⦃ kitᵣ ⦄ ⦃ kitᵣᵣ ⦄ ⦃ kitᵣᵣ ⦄ wk-kitᵣ
  wk-cancels-,ₛ-∘ = WkDistKit.wk-cancels-,ₖ-∘ ⦃ kitₛ ⦄ ⦃ kitₛᵣ ⦄ ⦃ kitᵣₛ ⦄ wk-kitₛ

