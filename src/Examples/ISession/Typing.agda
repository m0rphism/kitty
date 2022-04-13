module Examples.ISession.Typing where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax)

open import Examples.ISession.Definitions
open import Examples.ISession.Substitution

mutual

  -- ⊢_ : Ctx µ → Set
  -- ⊢_ {µ} Γ = ∀ m (x : m ∈ µ) → {!!}

  -- Context Wellformedness
  data ⊢_ : ∀ {µ} → Ctx µ → Set where
    τ-∅ :
      ⊢ ∅
    τ-ValVar : ∀ {Γ : Ctx µ} {t : µ ⊢ 𝕥} →
      ⊢ Γ →
      Γ ⊢ₜ t ∶ Type →
      ⊢_ {µ , 𝕧} (Γ ,, t)
    τ-TypeVar : ∀ {Γ : Ctx µ} {k : µ ⊢ 𝕜} →
      ⊢ Γ →
      Γ ⊢ₖ k ∶ Kind →
      ⊢_ {µ , 𝕥} (Γ ,, t)
    τ-CstrVar : ∀ {Γ : Ctx µ} {t : µ ⊢ 𝕥} →
      ⊢ Γ →
      Γ ⊢ₜ ℂ ∶ Cstr →
      ⊢_ {µ , 𝕧} (Γ ,, t)

  -- Constraint Entailment
  data _⊧_ {µ} (Γ : Ctx µ) : µ ⊢ 𝕥 → Set where
    ⊧-Axiom :
      wk-telescope Γ x ≡ ℂ →
      Γ ⊧ ℂ
    ⊧-Sym :
      Γ ⊧ (t₁ # t₂) →
      Γ ⊧ (t₂ # t₁)
    ⊧-,ᵈ-Intro :
      Γ ⊧ (t₁ # t₂₁) →
      Γ ⊧ (t₁ # t₂₂) →
      Γ ⊧ (t₁ # (t₂₁ ,ᵈ t₂₂))
    ⊧-,ᵈ-Elimᵣ :
      Γ ⊧ (t₁ # (t₂₁ ,ᵈ t₂₂)) →
      Γ ⊧ (t₁ # t₂₂)
    ⊧-True-Intro :
      Γ ⊧ True
    ⊧-∧-Intro :
      Γ ⊧ ℂ₁ →
      Γ ⊧ ℂ₂ →
      Γ ⊧ (ℂ₁ ∧ ℂ₂)
    ⊧-∧-Elimₗ :
      Γ ⊧ (ℂ₁ ∧ ℂ₂) →
      Γ ⊧ ℂ₁
    ⊧-∧-Elimᵣ :
      Γ ⊧ (ℂ₁ ∧ ℂ₂) →
      Γ ⊧ ℂ₂

  -- Kind Sorting
  data _⊢ₖ_∶_ : Ctx µ → µ ⊢ 𝕜 → µ ∶⊢ 𝕜 → Set where
    τ-Type :
      Γ ⊢ₖ Type ∶ Kind
    τ-Session :
      Γ ⊢ₖ Session ∶ Kind
    τ-State :
      Γ ⊢ₖ State ∶ Kind
    τ-Shape :
      Γ ⊢ₖ Shape ∶ Kind
    τ-Dom :
      Γ ⊢ₜ t ∶ Shape →
      Γ ⊢ₖ Dom t ∶ Kind

  -- ∈-++-ᵣ : (µ' : List Modeᵥ) → (µ ++ 𝕥 ∷ []) ∋ m → (µ ++ 𝕥 ∷ µ') ∋ m
  -- ∈-++-ᵣ = {!!}

  ∈-++-ᵣ : (µ' : List Modeᵥ) → µ ∋ m → (µ ++ µ') ∋ m
  ∈-++-ᵣ = {!!}

  -- data Rstr : Ctx (µ' ++ 𝕥 ∷ µ) → (µ' ++ 𝕥 ∷ µ) ⊢ 𝕥 → Set where 
  --   Rstr-Var : {Γ : Ctx (µ' ++ 𝕥 ∷ µ)} {α : (µ' ++ 𝕥 ∷ []) ∋ 𝕥} →
  --     Rstr Γ (`ᵗ (∈-++-ᵣ µ α))

  -- Asserts that the variables used in the type which come from µ
  -- do not have domain kind. Variables from µ' are not restricted.
  data Rstr µ' (Γ : Ctx (µ' ++ µ)) : (µ' ++ µ) ⊢ 𝕥 → Set where 
    Rstr-Var-new : {α : µ' ∋ 𝕥} →
      Rstr µ' Γ (`ᵗ (∈-++-ᵣ µ α))
      -- Rstr Γ (`ᵗ {!wk* {µ' = µ} _ α!}) -- requires wk* from the other side...
    Rstr-Var-old : {α : (µ' ++ µ) ∋ 𝕥} →
      wk-telescope Γ α ≢ Dom N →
      Rstr µ' Γ (`ᵗ α)
    Rstr-App :
      Rstr µ' Γ t₁ →
      Rstr µ' Γ t₂ →
      Rstr µ' Γ (t₁ ·ᵗ t₂)
    Rstr-Lam :
      Rstr (µ' , 𝕥) (Γ ,, Dom N) t →
      Rstr µ' Γ (λα→ t)
    Rstr-All :
      Rstr (µ' , 𝕥) (Γ ,, k) ℂ →
      Rstr (µ' , 𝕥 , 𝕧) (Γ ,, k ,, ℂ) t →
      Rstr µ' Γ (∀α[ ℂ ]→ t)
    κ-Arr : ∀ {Γ' : Ctx'' (µ' ++ µ) µ''} →
      Rstr µ' Γ Σ₁ →
      Rstr µ' Γ t₁ →
      Rstr (µ'' ++ µ') (subst Ctx (sym (++-assoc µ'' µ' µ)) (Γ' ++'' Γ)) {!Σ₂!} →
      Rstr (µ'' ++ µ') (subst Ctx (sym (++-assoc µ'' µ' µ)) (Γ' ++'' Γ)) {!t₂!} →
      Rstr µ' Γ ⟨ Σ₁ ; t₁ –→∃ Γ' ; Σ₂ ; t₂ ⟩

  -- data Rstr' (x : µ ∋ 𝕥) (Γ : Ctx µ) : µ ⊢ 𝕥 → Set where 
  --   Rstr-Var-new : {α : µ' ∋ 𝕥} →
  --     α ≡ ∈-++-ᵣ µ' α →
  --     Rstr' x Γ (`ᵗ α)
  --   Rstr-Var-old : {α : (µ' ++ µ) ∋ 𝕥} →
  --     wk-telescope Γ α ≢ Dom N →
  --     Rstr' µ' Γ (`ᵗ α)

    -- κ-Chan :
    --   Γ ⊢ₜ t ∶ Dom [1] →
    --   Γ ⊢ₜ Chan t ∶ Type
    -- κ-Unit :
    --   Γ ⊢ₜ Unit ∶ Type
    -- κ-Pair :
    --   Γ ⊢ₜ t₁ ∶ Type →
    --   Γ ⊢ₜ t₂ ∶ Type →
    --   Γ ⊢ₜ t₁ × t₂ ∶ Type
    -- κ-Send : ∀ {Γ : Ctx µ} →
    --   Γ ⊢ₜ N ∶ Shape →
    --   -- Rstr {µ' = []} (Γ ,, Dom N) Σ₁ →
    --   Rstr {µ' = []} Γ (λα→ Σ₁) →
    --   Rstr {µ' = []} Γ (λα→ t₁) →
    --   (Γ ,, Dom N) ⊢ₜ Σ₁ ∶ State →
    --   (Γ ,, Dom N) ⊢ₜ t₁ ∶ Type →
    --   Γ ⊢ₜ t₂ ∶ Type →
    --   Γ ⊢ₜ ![∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    -- κ-Recv : ∀ {Γ : Ctx µ} →
    --   Γ ⊢ₜ N ∶ Shape →
    --   Rstr {µ' = []} Γ (λα→ Σ₁) →
    --   Rstr {µ' = []} Γ (λα→ t₁) →
    --   (Γ ,, Dom N) ⊢ₜ Σ₁ ∶ State →
    --   (Γ ,, Dom N) ⊢ₜ t₁ ∶ Type →
    --   Γ ⊢ₜ t₂ ∶ Type →
    --   Γ ⊢ₜ ?[∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    -- κ-Branch :
    --   Γ ⊢ₜ t₁ ∶ Session →
    --   Γ ⊢ₜ t₂ ∶ Session →
    --   Γ ⊢ₜ t₁ & t₂ ∶ Session
    -- κ-Choice :
    --   Γ ⊢ₜ t₁ ∶ Session →
    --   Γ ⊢ₜ t₂ ∶ Session →
    --   Γ ⊢ₜ t₁ ⊕ t₂ ∶ Session
    -- κ-End :
    --   Γ ⊢ₜ End ∶ Session
    -- κ-Dual :
    --   Γ ⊢ₜ t ∶ Session →
    --   Γ ⊢ₜ Dual t ∶ Session
    -- κ-DomMerge :
    --   Γ ⊢ₜ t₁ ∶ Dom N₁ →
    --   Γ ⊢ₜ t₂ ∶ Dom N₂ →
    --   Γ ⊢ₜ t₁ ,ᵈ t₂ ∶ Dom (N₁ + N₂)
    -- κ-DomProj₁ :
    --   Γ ⊢ₜ t ∶ Dom (N₁ + N₂) →
    --   Γ ⊢ₜ πᵈ [0] t ∶ Dom N₁
    -- κ-DomProj₂ :
    --   Γ ⊢ₜ t ∶ Dom (N₁ + N₂) →
    --   Γ ⊢ₜ πᵈ [1] t ∶ Dom N₂
    -- κ-ShapeUnit :
    --   Γ ⊢ₜ [1] ∶ Shape
    -- κ-ShapePair :
    --   Γ ⊢ₜ t₁ ∶ Shape →
    --   Γ ⊢ₜ t₂ ∶ Shape →
    --   Γ ⊢ₜ t₁ + t₂ ∶ Shape
    -- κ-StEmpty :
    --   Γ ⊢ₜ [] ∶ State
    -- κ-StChan :
    --   Γ ⊢ₜ t₁ ∶ Dom [1] →
    --   Γ ⊢ₜ t₂ ∶ Session →
    --   Γ ⊢ₜ (t₁ ∶ t₂) ∶ State
    -- κ-StChan♯ :
    --   Γ ⊢ₜ t₁ ∶ Dom [1] →
    --   Γ ⊢ₜ t₂ ∶ Session →
    --   Γ ⊢ₜ (t₁ ∶♯ t₂) ∶ State
    -- κ-StMerge :
    --   Γ ⊢ₜ t₁ ∶ State →
    --   Γ ⊢ₜ t₂ ∶ State →
    --   Γ ⊢ₜ t₁ ,ˢ t₂ ∶ State
      

  -- Type Kinding
  data _⊢ₜ_∶_ : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕜 → Set where
    κ-Var :
      wk-telescope Γ α ≡ k →
      Γ ⊢ₜ ` α ∶ k
    κ-App :
      Γ ⊢ₜ t₁ ∶ (k₁ ⇒ k₂) →
      Γ ⊢ₜ t₂ ∶ k₁ →
      Γ ⊢ₜ t₁ ·ᵗ t₂ ∶ k₂
    κ-Lam : ∀ {Γ : Ctx µ} →
      k ≡ Type ⊎ k ≡ State →
      Γ ⊢ₜ N ∶ Shape →
      (Γ ,, Dom N) ⊢ₜ t ∶ (k ⋯ wk) →
      Γ ⊢ₜ λα→ t ∶ (Dom N ⇒ k)
    κ-All : ∀ {Γ : Ctx µ} {t : (µ , 𝕥 , 𝕧) ⊢ 𝕥} {ℂ : (µ , 𝕥) ⊢ 𝕥} →
      -- (Γ ,, k ,, ℂ) ; ((ℂ ⋯ wk) ∧ ℂ') ⊢ t ∶ Type →
      (Γ ,, k) ⊢ₜ ℂ ∶ Cstr →
      (Γ ,, k ,, ℂ) ⊢ₜ t ∶ Type →
      Γ ⊢ₜ ∀α[ ℂ ]→ t ∶ Type
    κ-Arr : ∀ {Γ : Ctx µ} {Γ' : Ctx'' µ µ'} →
      Γ ⊢ₜ Σ₁ ∶ State →
      Γ ⊢ₜ t₁ ∶ Type →
      (Γ' ++'' Γ) ⊢ₜ Σ₂ ∶ State →
      (Γ' ++'' Γ) ⊢ₜ t₂ ∶ Type →
      (∀ x → ∃[ N ] (Γ' x ≡ Dom N)) →
      ⊢ (Γ' ++'' Γ) →
      Γ ⊢ₜ ⟨ Σ₁ ; t₁ –→∃ Γ' ; Σ₂ ; t₂ ⟩ ∶ Type
    κ-Chan :
      Γ ⊢ₜ t ∶ Dom [1] →
      Γ ⊢ₜ Chan t ∶ Type
    κ-Unit :
      Γ ⊢ₜ Unit ∶ Type
    κ-Pair :
      Γ ⊢ₜ t₁ ∶ Type →
      Γ ⊢ₜ t₂ ∶ Type →
      Γ ⊢ₜ t₁ × t₂ ∶ Type
    κ-Send : ∀ {Γ : Ctx µ} →
      Γ ⊢ₜ N ∶ Shape →
      -- Rstr {µ' = []} (Γ ,, Dom N) Σ₁ →
      Rstr [] Γ (λα→ Σ₁) →
      Rstr [] Γ (λα→ t₁) →
      (Γ ,, Dom N) ⊢ₜ Σ₁ ∶ State →
      (Γ ,, Dom N) ⊢ₜ t₁ ∶ Type →
      Γ ⊢ₜ t₂ ∶ Type →
      Γ ⊢ₜ ![∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    κ-Recv : ∀ {Γ : Ctx µ} →
      Γ ⊢ₜ N ∶ Shape →
      Rstr [] Γ (λα→ Σ₁) →
      Rstr [] Γ (λα→ t₁) →
      (Γ ,, Dom N) ⊢ₜ Σ₁ ∶ State →
      (Γ ,, Dom N) ⊢ₜ t₁ ∶ Type →
      Γ ⊢ₜ t₂ ∶ Type →
      Γ ⊢ₜ ?[∃α→ Σ₁ ; t₁ ] t₂ ∶ Session
    κ-Branch :
      Γ ⊢ₜ t₁ ∶ Session →
      Γ ⊢ₜ t₂ ∶ Session →
      Γ ⊢ₜ t₁ & t₂ ∶ Session
    κ-Choice :
      Γ ⊢ₜ t₁ ∶ Session →
      Γ ⊢ₜ t₂ ∶ Session →
      Γ ⊢ₜ t₁ ⊕ t₂ ∶ Session
    κ-End :
      Γ ⊢ₜ End ∶ Session
    κ-Dual :
      Γ ⊢ₜ t ∶ Session →
      Γ ⊢ₜ Dual t ∶ Session
    κ-DomMerge :
      Γ ⊢ₜ t₁ ∶ Dom N₁ →
      Γ ⊢ₜ t₂ ∶ Dom N₂ →
      Γ ⊢ₜ t₁ ,ᵈ t₂ ∶ Dom (N₁ + N₂)
    κ-DomProj₁ :
      Γ ⊢ₜ t ∶ Dom (N₁ + N₂) →
      Γ ⊢ₜ πᵈ [0] t ∶ Dom N₁
    κ-DomProj₂ :
      Γ ⊢ₜ t ∶ Dom (N₁ + N₂) →
      Γ ⊢ₜ πᵈ [1] t ∶ Dom N₂
    κ-ShapeUnit :
      Γ ⊢ₜ [1] ∶ Shape
    κ-ShapePair :
      Γ ⊢ₜ t₁ ∶ Shape →
      Γ ⊢ₜ t₂ ∶ Shape →
      Γ ⊢ₜ t₁ + t₂ ∶ Shape
    κ-StEmpty :
      Γ ⊢ₜ [] ∶ State
    κ-StChan :
      Γ ⊢ₜ t₁ ∶ Dom [1] →
      Γ ⊢ₜ t₂ ∶ Session →
      Γ ⊢ₜ (t₁ ∶ t₂) ∶ State
    κ-StChan♯ :
      Γ ⊢ₜ t₁ ∶ Dom [1] →
      Γ ⊢ₜ t₂ ∶ Session →
      Γ ⊢ₜ (t₁ ∶♯ t₂) ∶ State
    κ-StMerge :
      Γ ⊢ₜ t₁ ∶ State →
      Γ ⊢ₜ t₂ ∶ State →
      Γ ⊢ₜ t₁ ,ˢ t₂ ∶ State

  wk-++ : (µ' ++ µ) →ᵣ (µ' ++ m ∷ µ)
  wk-++ {µ' = []}      m x         = there x
  wk-++ {µ' = µ' , m'} m (here px) = here px
  wk-++ {µ' = µ' , m'} m (there x) = there (wk-++ m x)

  -- Value Typing
  data _⊢ᵥ_∶_ : Ctx µ → µ ⊢ 𝕧 → µ ⊢ 𝕥 → Set where
    τ-Var :
      wk-telescope Γ x ≡ t →
      Γ ⊢ᵥ ` x ∶ t
    τ-Abs : ∀ {Γ : Ctx µ} {Γ₂ : Ctx'' µ µ'} →
      Γ ⊢ₜ ⟨ Σ₁ ; t₁ –→∃ Γ₂ ; Σ₂ ; t₂ ⟩ ∶ Type →
      (Γ ,, t₁) ; (Σ₁ ⋯ wk) ⊢ₑ e ∶∃ (Γ₂ ⋯Ctx'' wk) ; Σ₂ ⋯ wk-++ ; (t₂ ⋯ wk-++) →
      Γ ⊢ᵥ λx→ e ∶ ⟨ Σ₁ ; t₁ –→∃ Γ₂ ; Σ₂ ; t₂ ⟩
    τ-TAbs : ∀ {Γ : Ctx µ} {Γ₂ : Ctx'' µ µ'} →
      Γ ⊢ₜ ∀α[ ℂ ]→ t ∶ Type →
      (Γ ,, k ,, ℂ) ⊢ᵥ v ∶ t →
      Γ ⊢ᵥ (Λα→ v) ∶ (∀α[ ℂ ]→ t)
    τ-Unit : ∀ {Γ : Ctx µ} →
      Γ ⊢ᵥ unit ∶ Unit
    τ-Pair : ∀ {Γ : Ctx µ} →
      Γ ⊢ᵥ v₁ ∶ t₁ →
      Γ ⊢ᵥ v₂ ∶ t₂ →
      Γ ⊢ᵥ (v₁ ,ᵉ v₂) ∶ (t₁ × t₂)

  -- Expression Typing
  data _;_⊢ₑ_∶∃_;_;_ : Ctx µ → µ ⊢ 𝕥 → µ ⊢ 𝕖 → Ctx'' µ µ' → (µ' ++ µ) ⊢ 𝕥 → (µ' ++ µ) ⊢ 𝕥 → Set where
    τ-Val : ∀ {Γ : Ctx µ} →
      Γ ⊢ᵥ v ∶ t →
      Γ ; [] ⊢ₑ ⟨ v ⟩ᵥ ∶∃ (∅'' {µ = µ}) ; [] ; t
    τ-Let : ∀ {Γ₁ : Ctx µ} {Γ₂ : Ctx'' µ µ'} {Γ₃ : Ctx'' (µ' ++ µ) µ''} {t₂ : Term (µ'' ++ (µ' ++ µ)) 𝕥} →
      Γ₁ ; Σ₁ ⊢ₑ e₁ ∶∃ Γ₂ ; Σ₂' ; t₁ →
      ((Γ₂ ++'' Γ₁) ,, t₁) ; ((Σ₂ ⋯ wk*) ,ˢ (Σ₂' ⋯ wk)) ⊢ₑ e₂ ∶∃ (Γ₃ ⋯Ctx'' wk) ; Σ₃ ⋯ᵣ wk-inner 𝕧 ; (t₂ ⋯ᵣ wk-inner 𝕧) →
      let assoc-µ = subst (_⊢ 𝕥) (sym (++-assoc µ'' µ' µ)) in
      Γ₁ ; (Σ₁ ,ˢ Σ₂) ⊢ₑ let[x= e₁ ]in e₂ ∶∃ (Γ₃ +''+ Γ₂) ; assoc-µ Σ₃ ; assoc-µ t₂

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
