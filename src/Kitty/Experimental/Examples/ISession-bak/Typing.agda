module Kitty.Experimental.Examples.ISession.Typing where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax)

open import Kitty.Experimental.Examples.ISession.Definitions
open import Kitty.Experimental.Examples.ISession.Substitution

mutual

  -- ⊢_ : Ctx µ → Set
  -- ⊢_ {µ} Γ = ∀ m (x : m ∈ µ) → {!!}

  data ⊢_ : ∀ {µ} → Ctx µ → Set where
    τ-∅ :
      ⊢ ∅
    τ-ValVar : ∀ {Γ : Ctx µ} {t : µ ⊢ 𝕥} →
      ⊢ Γ →
      Γ ; ℂ ⊢ t ∶ Type →  -- FIXME: requires ℂ. not possible without weird mutual recursion.
      ⊢_ {µ , 𝕧} (Γ ,, t)
    τ-TypeVar : ∀ {Γ : Ctx µ} {k : µ ⊢ 𝕜} →
      ⊢ Γ →
      Γ ⊢ k ∶ Kind →
      ⊢_ {µ , 𝕥} (Γ ,, t)

  -- Kind Sorting
  data _⊢_∶_ : Ctx µ → µ ⊢ 𝕜 → µ ∶⊢ 𝕜 → Set where
    τ-Type :
      Γ ⊢ Type ∶ Kind
    τ-Session :
      Γ ⊢ Session ∶ Kind
    τ-State :
      Γ ⊢ State ∶ Kind
    τ-Shape :
      Γ ⊢ Shape ∶ Kind
    τ-Dom :
      Γ ; True ⊢ t ∶ Shape →
      Γ ⊢ Dom t ∶ Kind

  -- Type Kinding
  data _;_⊢_∶_ : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕜 → Set where
    κ-Var :
      wk-telescope Γ α ≡ k →
      Γ ; ℂ ⊢ ` α ∶ k
    κ-App :
      Γ ; ℂ ⊢ t₁ ∶ (k₁ ⇒ k₂) →
      Γ ; ℂ ⊢ t₂ ∶ k₁ →
      Γ ; ℂ ⊢ t₁ ·ᵗ t₂ ∶ k₂
    κ-Lam : ∀ {Γ : Ctx µ} →
      k ≡ Type ⊎ k ≡ State →
      Γ ; True ⊢ N ∶ Shape →
      (Γ ,, Dom N) ; (ℂ ⋯ wk) ⊢ t ∶ (k ⋯ wk) →
      Γ ; ℂ ⊢ λα→ t ∶ (Dom N ⇒ k)
    κ-All : ∀ {Γ : Ctx µ} →
      (Γ ,, k) ; ((ℂ ⋯ wk) ∧ ℂ') ⊢ t ∶ Type →
      Γ ; ℂ ⊢ ∀α→ t ∶ Type
    κ-Arr : ∀ {Γ : Ctx µ} {Γ' : Ctx'' µ µ'} →
      Γ ; ℂ ⊢ Σ₁ ∶ State →
      Γ ; ℂ ⊢ t₁ ∶ Type →
      (Γ' ++'' Γ) ; (ℂ ⋯ wk*) ⊢ Σ₂ ∶ State →
      (Γ' ++'' Γ) ; (ℂ ⋯ wk*) ⊢ t₂ ∶ Type →
      (∀ x → ∃[ N ] (Γ' x ≡ Dom N)) →
      -- TODO: Γ' wellformed
      Γ ; ℂ ⊢ ⟨ Σ₁ ; t₁ –→∃ Γ' ; Σ₂ ; t₂ ⟩ ∶ Type
    κ-Chan :
      Γ ; ℂ ⊢ t ∶ Dom [1] →
      Γ ; ℂ ⊢ Chan t ∶ Type
    κ-Unit :
      Γ ; ℂ ⊢ Unit ∶ Type
    κ-Pair :
      Γ ; ℂ ⊢ t₁ ∶ Type →
      Γ ; ℂ ⊢ t₂ ∶ Type →
      Γ ; ℂ ⊢ t₁ × t₂ ∶ Type
    κ-Send : ∀ {Γ : Ctx µ} →
      Γ ; ℂ ⊢ N ∶ Shape →
      -- TODO: restrict Γ to Non-Dom
      (Γ ,, Dom N) ; (ℂ ⋯ wk) ⊢ Σ₁ ∶ State →
      (Γ ,, Dom N) ; (ℂ ⋯ wk) ⊢ t₁ ∶ Type →
      Γ ; ℂ ⊢ t₂ ∶ Type →
      Γ ; ℂ ⊢ ![∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    κ-Recv : ∀ {Γ : Ctx µ} →
      Γ ; ℂ ⊢ N ∶ Shape →
      -- TODO: restrict Γ to Non-Dom
      (Γ ,, Dom N) ; (ℂ ⋯ wk) ⊢ Σ₁ ∶ State →
      (Γ ,, Dom N) ; (ℂ ⋯ wk) ⊢ t₁ ∶ Type →
      Γ ; ℂ ⊢ t₂ ∶ Type →
      Γ ; ℂ ⊢ ?[∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    κ-Branch :
      Γ ; ℂ ⊢ t₁ ∶ Session →
      Γ ; ℂ ⊢ t₂ ∶ Session →
      Γ ; ℂ ⊢ t₁ & t₂ ∶ Session
    κ-Choice :
      Γ ; ℂ ⊢ t₁ ∶ Session →
      Γ ; ℂ ⊢ t₂ ∶ Session →
      Γ ; ℂ ⊢ t₁ ⊕ t₂ ∶ Session
    κ-End :
      Γ ; ℂ ⊢ End ∶ Session
    κ-Dual :
      Γ ; ℂ ⊢ t ∶ Session →
      Γ ; ℂ ⊢ Dual t ∶ Session
    κ-DomMerge :
      Γ ; ℂ ⊢ t₁ ∶ Dom N₁ →
      Γ ; ℂ ⊢ t₂ ∶ Dom N₂ →
      Γ ; ℂ ⊢ t₁ ,ᵈ t₂ ∶ Dom (N₁ + N₂)
    κ-DomProj₁ :
      Γ ; ℂ ⊢ t ∶ Dom (N₁ + N₂) →
      Γ ; ℂ ⊢ πᵈ [0] t ∶ Dom N₁
    κ-DomProj₂ :
      Γ ; ℂ ⊢ t ∶ Dom (N₁ + N₂) →
      Γ ; ℂ ⊢ πᵈ [1] t ∶ Dom N₂
    κ-ShapeUnit :
      Γ ; ℂ ⊢ [1] ∶ Shape
    κ-ShapePair :
      Γ ; ℂ ⊢ t₁ ∶ Shape →
      Γ ; ℂ ⊢ t₂ ∶ Shape →
      Γ ; ℂ ⊢ t₁ + t₂ ∶ Shape
    κ-StEmpty :
      Γ ; ℂ ⊢ [] ∶ State
    κ-StChan :
      Γ ; ℂ ⊢ t₁ ∶ Dom [1] →
      Γ ; ℂ ⊢ t₂ ∶ Session →
      Γ ; ℂ ⊢ (t₁ ∶ t₂) ∶ State
    -- TODO: suspended StChan
    κ-StMerge :
      Γ ; ℂ ⊢ t₁ ∶ State →
      Γ ; ℂ ⊢ t₂ ∶ State →
      Γ ; ℂ ⊢ t₁ ,ˢ t₂ ∶ State

  wk-++ : (µ' ++ µ) →ᵣ (µ' ++ m ∷ µ)
  wk-++ {µ' = []}      m x         = there x
  wk-++ {µ' = µ' , m'} m (here px) = here px
  wk-++ {µ' = µ' , m'} m (there x) = there (wk-++ m x)

  -- Value Typing
  data _;_⊢ᵥ_∶_ : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕧 → µ ⊢ 𝕥 → Set where
    τ-Var :
      wk-telescope Γ x ≡ t →
      Γ ; ℂ ⊢ᵥ ` x ∶ t
    τ-Abs : ∀ {Γ : Ctx µ} {Γ₂ : Ctx'' µ µ'} →
      Γ ; ℂ ⊢ ⟨ Σ₁ ; t₁ –→∃ Γ₂ ; Σ₂ ; t₂ ⟩ ∶ Type →
      (Γ ,, t₁) ; (ℂ ⋯ wk) ; (Σ₁ ⋯ wk) ⊢ₑ e ∶∃ (Γ₂ ⋯Ctx'' wk) ; Σ₂ ⋯ wk-++ ; (t₂ ⋯ wk-++) →
      Γ ; ℂ ⊢ᵥ λx→ e ∶ ⟨ Σ₁ ; t₁ –→∃ Γ₂ ; Σ₂ ; t₂ ⟩
    τ-TAbs : ∀ {Γ : Ctx µ} {Γ₂ : Ctx'' µ µ'} →
      -- TODO: we need constraints and kind in the ∀-type for formation checking
      Γ ; ℂ ⊢  ∀α→ t ∶ Type →
      (Γ ,, k) ; (ℂ ⋯ wk) ⊢ᵥ v ∶ t →
      Γ ; ℂ ⊢ᵥ (Λα→ v) ∶ (∀α→ t)
    τ-Unit : ∀ {Γ : Ctx µ} →
      Γ ; ℂ ⊢ᵥ unit ∶ Unit
    τ-Pair : ∀ {Γ : Ctx µ} →
      Γ ; ℂ ⊢ᵥ v₁ ∶ t₁ →
      Γ ; ℂ ⊢ᵥ v₂ ∶ t₂ →
      Γ ; ℂ ⊢ᵥ (v₁ ,ᵉ v₂) ∶ (t₁ × t₂)

  -- Expression Typing
  data _;_;_⊢ₑ_∶∃_;_;_ : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕖 → Ctx'' µ µ' → (µ' ++ µ) ⊢ 𝕥 → (µ' ++ µ) ⊢ 𝕥 → Set where
    τ-Val : ∀ {Γ : Ctx µ} →
      Γ ; ℂ ⊢ᵥ v ∶ t →
      Γ ; ℂ ; [] ⊢ₑ ⟨ v ⟩ᵥ ∶∃ (∅'' {µ = µ}) ; [] ; t
    τ-Let : ∀ {Γ₁ : Ctx µ} {Γ₂ : Ctx'' µ µ'} {Γ₃ : Ctx'' (µ' ++ µ) µ''} {t₂ : Term (µ'' ++ (µ' ++ µ)) 𝕥} →
      Γ₁ ; ℂ ; Σ₁ ⊢ₑ e₁ ∶∃ Γ₂ ; Σ₂' ; t₁ →
      ((Γ₂ ++'' Γ₁) ,, t₁) ; (ℂ ⋯ wk*) ; ((Σ₂ ⋯ wk*) ,ˢ (Σ₂' ⋯ wk)) ⊢ₑ e₂ ∶∃ (Γ₃ ⋯Ctx'' wk) ; Σ₃ ⋯ᵣ wk-inner 𝕧 ; (t₂ ⋯ᵣ wk-inner 𝕧) →
      let assoc-µ = subst (_⊢ 𝕥) (sym (++-assoc µ'' µ' µ)) in
      Γ₁ ; ℂ ; (Σ₁ ,ˢ Σ₂) ⊢ₑ let[x= e₁ ]in e₂ ∶∃ (Γ₃ +''+ Γ₂) ; assoc-µ Σ₃ ; assoc-µ t₂

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
