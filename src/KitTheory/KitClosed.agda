open import KitTheory.Modes

module KitTheory.KitClosed {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import KitTheory.Prelude
open import KitTheory.Kit 𝕋 hiding (_∋/⊢[_]_; _–[_]→_)

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
  
module Test (KT : KitTraversal) where
  open KitTraversal KT using (kitᵣ; kitₛ) renaming (_⋯_ to _⋯'_)

  data Ren/Sub : Set where
    instance Ren : Ren/Sub
    instance Sub : Ren/Sub

  kit : Ren/Sub → Kit
  kit Ren = kitᵣ
  kit Sub = kitₛ

  module Kit' (K : Ren/Sub) where
    open Kit (kit K) public
  open Kit' ⦃ ... ⦄ public

  _⊔ₖ_ : Ren/Sub → Ren/Sub → Ren/Sub
  Ren ⊔ₖ K = K
  _   ⊔ₖ _ = Sub

  ⊔ₖ-sym : ∀ K₁ K₂ → K₁ ⊔ₖ K₂ ≡ K₂ ⊔ₖ K₁
  ⊔ₖ-sym Ren Ren = refl
  ⊔ₖ-sym Ren Sub = refl
  ⊔ₖ-sym Sub Ren = refl
  ⊔ₖ-sym Sub Sub = refl

  ⊔ₖ-assoc : ∀ K₁ K₂ K₃ → ((K₁ ⊔ₖ K₂) ⊔ₖ K₃)  ≡ (K₁ ⊔ₖ (K₂ ⊔ₖ K₃))
  ⊔ₖ-assoc Ren K₂ K₃ = refl
  ⊔ₖ-assoc Sub K₂ K₃ = refl

  data _⊑ₖ_ : Ren/Sub → Ren/Sub → Set where
    instance refl     : ∀ {K} → K ⊑ₖ K
    instance Ren⊑ₖSub : Ren ⊑ₖ Sub

  ⊑-⊥ : ∀ {K} → Ren ⊑ₖ K
  ⊑-⊤ : ∀ {K} → K ⊑ₖ Sub
  ⊑-⊥ {Ren} = refl
  ⊑-⊥ {Sub} = Ren⊑ₖSub
  ⊑-⊤ {Ren} = Ren⊑ₖSub
  ⊑-⊤ {Sub} = refl

  ⊑ₖ-⊔ₖ-l : ∀ K₁ K₂ → K₁ ⊑ₖ (K₁ ⊔ₖ K₂)
  ⊑ₖ-⊔ₖ-r : ∀ K₁ K₂ → K₂ ⊑ₖ (K₁ ⊔ₖ K₂)
  ⊑ₖ-⊔ₖ-l Ren K₂ = ⊑-⊥
  ⊑ₖ-⊔ₖ-l Sub K₂ = refl
  ⊑ₖ-⊔ₖ-r Ren K₂ = refl
  ⊑ₖ-⊔ₖ-r Sub K₂ = ⊑-⊤

  m/M→m/M : (K₁ K₂ : Ren/Sub) → Kit'.VarMode/TermMode K₁ → Kit'.VarMode/TermMode (K₁ ⊔ₖ K₂)
  m/M→m/M Ren K m = Kit'.id/m→M K m
  m/M→m/M Sub _ M = M
  -- m/M→m/M Ren Ren m = m
  -- m/M→m/M Ren Sub m = m→M m
  -- m/M→m/M Sub _   M = M

  _∋/⊢[_]_ : List VarMode → (K : Ren/Sub) → Kit'.VarMode/TermMode K → Set
  µ ∋/⊢[ 𝕂 ] sm = Kit'._∋/⊢_ 𝕂 µ sm

  _–[_]→_ : List VarMode → Ren/Sub → List VarMode → Set
  µ₁ –[ 𝕂 ]→ µ₂ = Kit'._–→_ 𝕂 µ₁ µ₂

  -- _⋯_ : ∀ ⦃ 𝕂 : Ren/Sub ⦄
  --       → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  -- _⋯_ ⦃ 𝕂 ⦄ = _⋯'_ ⦃ kit 𝕂 ⦄

  _⋯_ : ∀ ⦃ K₁ K₂ : Ren/Sub ⦄ {m/M}
        → µ₁ ∋/⊢[ K₁ ] m/M → µ₁ –[ K₂ ]→ µ₂ → µ₂ ∋/⊢[ K₁ ⊔ₖ K₂ ] m/M→m/M K₁ K₂ m/M
  _⋯_ ⦃ K₁ = Ren ⦄ ⦃ K₂ ⦄ x ϕ = ϕ _ x
  _⋯_ ⦃ K₁ = Sub ⦄ ⦃ K₂ ⦄ t ϕ = _⋯'_ ⦃ kit K₂ ⦄ t ϕ

  lem : ∀ ⦃ K₁ K₂ K₃ : Ren/Sub ⦄ {m/M} → 
    m/M→m/M (K₁ ⊔ₖ K₂) K₃ (m/M→m/M K₁ K₂ m/M) ≡ subst Kit'.VarMode/TermMode (sym (⊔ₖ-assoc K₁ K₂ K₃)) (m/M→m/M K₁ (K₂ ⊔ₖ K₃) m/M)
  lem ⦃ Ren ⦄ ⦃ Ren ⦄ ⦃ K₁ ⦄ = refl
  lem ⦃ Ren ⦄ ⦃ Sub ⦄ ⦃ K₁ ⦄ = refl
  lem ⦃ Sub ⦄ ⦃ K₂  ⦄ ⦃ K₁ ⦄ = refl

  _∘_ : ⦃ K₁ K₂ : Ren/Sub ⦄ → µ₂ –[ K₁ ]→ µ₃ → µ₁ –[ K₂ ]→ µ₂ → µ₁ –[ K₂ ⊔ₖ K₁ ]→ µ₃
  -- _∘_ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ϕ₁ ϕ₂ _ x = let s = subst (Kit'._∋/⊢_ (K₂ ⊔ₖ K₁) _) (lem ⦃ Ren ⦄ ⦃ K₂ ⦄ ⦃ K₁ ⦄)
  --                                in s (ϕ₂ _ x ⋯ ϕ₁)
  _∘_ ⦃ K₁ ⦄ ⦃ Ren ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁
  _∘_ ⦃ K₁ ⦄ ⦃ Sub ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁

  _∘'_ : ⦃ K₁ K₂ : Ren/Sub ⦄ → µ₂ –[ K₁ ]→ µ₃ → µ₁ –[ K₂ ]→ µ₂ → µ₁ –[ K₁ ⊔ₖ K₂ ]→ µ₃
  _∘'_  ⦃ Ren ⦄ ⦃ Ren ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁
  _∘'_  ⦃ Ren ⦄ ⦃ Sub ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁
  _∘'_  ⦃ Sub ⦄ ⦃ Ren ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁
  _∘'_  ⦃ Sub ⦄ ⦃ Sub ⦄ ϕ₁ ϕ₂ _ x = ϕ₂ _ x ⋯ ϕ₁

  -- `/id' : ∀ {K} m → Kit'._∋/⊢_ K µ (Kit'.id/m→M K m) → µ ⊢ m→M m
  -- `/id' {K = K} = `/id where instance _ = K

  -- tm-⋯-∘' : ⦃ K₁ K₂ : Ren/Sub ⦄ → (ϕ₁ : µ₁ –[ K₂ ]→ µ₂) (ϕ₂ : µ₂ –[ K₁ ]→ µ₃) (x : µ₁ ∋ m) →
  --   (`/id _ (ϕ₁ _ x) ⋯ ϕ₂) ≡ `/id' _ ((ϕ₂ ∘ ϕ₁) _ x)
  -- tm-⋯-∘' = {!!}

  tm-⋯-∘ : ⦃ K₁ K₂ : Ren/Sub ⦄ → (ϕ₁ : µ₁ –[ K₂ ]→ µ₂) (ϕ₂ : µ₂ –[ K₁ ]→ µ₃) (x : µ₁ ∋ m) →
    (`/id _ (ϕ₁ _ x) ⋯ ϕ₂) ≡ `/id ⦃ K₂ ⊔ₖ K₁ ⦄ _ ((ϕ₂ ∘ ϕ₁) _ x)
  tm-⋯-∘ = {!!}

  -- tm-⋯-∘'' : ⦃ K₁ K₂ : Ren/Sub ⦄ → (ϕ₁ : µ₁ –[ K₂ ]→ µ₂) (ϕ₂ : µ₂ –[ K₁ ]→ µ₃) (x : µ₁ ∋ m) →
  --   (`/id _ (ϕ₁ _ x) ⋯ ϕ₂) ≡ `/id ⦃ K₂ ⊔ₖ K₁ ⦄ _ ((ϕ₂ ∘ ϕ₁) _ x)
  -- tm-⋯-∘'' = {!!}



  -- dist-↑-∘ : ⦃ K₁ K₂ : Ren/Sub ⦄ → ∀ m (ϕ₁ : µ₂ –[ K₁ ]→ µ₃) (ϕ₂ : µ₁ –[ K₂ ]→ µ₂) →
  --   (ϕ₁ ∘ ϕ₂) ↑ m ≡ (ϕ₁ ↑ m) ∘ (ϕ₂ ↑ m)
  -- dist-↑-∘ = ?

  -- record CKit (K₁ K₂ : Ren/Sub) : Set where 
  --   field
  --     _∘_ : µ₂ –[ K₁ ]→ µ₃ → µ₁ –[ K₂ ]→ µ₂ → µ₁ –[ ∘-Res K₁ K₂ ]→ µ₃

  -- ckitᵣᵣ : CKit Ren Ren
  -- ckitᵣᵣ = record { _∘_ = λ ρ₁ ρ₂ m x → ρ₁ _ (ρ₂ _ x) }

  -- ckitₛᵣ : CKit Sub Ren
  -- -- ckitₛᵣ = record { _∘_ = λ σ₁ ρ₂ m x → σ₁ _ (ρ₂ _ x) }
  -- -- ckitₛᵣ = record { _∘_ = λ σ₁ ρ₂ m x → ρ₂ _ x ⋯ ρ₁ }

  -- ckitᵣₛ : CKit Ren Sub
  -- ckitᵣₛ = record { _∘_ = λ ρ₁ σ₂ m x → σ₂ _ x ⋯ ρ₁ }

  -- ckitₛₛ : CKit Sub Sub
  -- ckitₛₛ = record { _∘_ = λ σ₁ σ₂ m x → σ₂ _ x ⋯ σ₁ }

  -- -- open CKit ⦃ ... ⦄
