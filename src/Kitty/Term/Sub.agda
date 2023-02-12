open import Kitty.Term.Modes

module Kitty.Term.Sub {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function using (_$_)

open Modes 𝕄
open Terms 𝕋

open import Kitty.Term.Kit 𝕋 using (Kit; _∋/⊢[_]_)

open Kit ⦃ … ⦄ hiding (_,ₖ_; _↑_; _↑*_; _–→_; ~-cong-↑; ~-cong-↑*; _∥_; ⦅_⦆; _↓)

record Sub : Set₁ where
  field
    _–[_]→_ : List VarMode → Kit → List VarMode → Set

    []ₖ  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→ []
    _,ₖ_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
    wkₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
    wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
    _↑_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
    _↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
    id   : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
    []*  : ∀ ⦃ 𝕂 ⦄ {µ₂} → [] –[ 𝕂 ]→ µ₂
    _↓   : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₂
    _∥_  : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
    ⦅_⦆  : ∀ ⦃ 𝕂 : Kit ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ

    apₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)

  -- Renaming/Substitution

  _–→_ : ⦃ 𝕂 : Kit ⦄ → List VarMode → List VarMode → Set
  _–→_ ⦃ 𝕂 ⦄ µ₁ µ₂ = µ₁ –[ 𝕂 ]→ µ₂

  -- Extensional Equality

  _~_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Set
  ϕ₁ ~ ϕ₂ = ∀ m x → apₖ ϕ₁ m x ≡ apₖ ϕ₂ m x

  ~-refl :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f : µ₁ –[ 𝕂 ]→ µ₂}
    → f ~ f
  ~-refl a b = refl

  ~-sym :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f g : µ₁ –[ 𝕂 ]→ µ₂}
    → f ~ g
    → g ~ f
  ~-sym f~g a b = sym (f~g a b)

  ~-trans :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f g h : µ₁ –[ 𝕂 ]→ µ₂} 
    → f ~ g
    → g ~ h
    → f ~ h
  ~-trans f~g g~h a b = trans (f~g a b) (g~h a b)

  data Invert-ϕ ⦃ 𝕂 ⦄ {µ₂} : {µ₁ : List VarMode} → µ₁ –[ 𝕂 ]→ µ₂ → Set where
    ϕ~[]* : ∀ {ϕ} →
      ϕ ~ []* →
      Invert-ϕ ϕ
    ϕ~,ₖ : ∀ {µ₁' m₁ ϕ} →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      ϕ ~ (ϕ' ,ₖ x/t) →
      Invert-ϕ ϕ

  data Invert-ϕ' ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) : Set where
    ϕ~[]* :
      (eq : µ₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ' ϕ
    ϕ~,ₖ : ∀ {µ₁' m₁} →
      (eq : µ₁ ≡ µ₁' ▷ m₁) →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      Invert-ϕ' ϕ

  invert-ϕ'→ϕ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  invert-ϕ'→ϕ (ϕ~[]* refl ϕ~) = ϕ~[]* ϕ~
  invert-ϕ'→ϕ (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

record SubWithLaws : Set₁ where
  open Sub ⦃ … ⦄
  field
    ⦃ SubWithLaws-Sub ⦄ : Sub

    apₖ-,ₖ-here : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
                  → apₖ (ϕ ,ₖ x/t) _ (here refl) ≡ x/t
    apₖ-,ₖ-there : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) {m'} (x : µ₁ ∋ m')
                   → apₖ (ϕ ,ₖ x/t) _ (there x) ≡ apₖ ϕ _ x

    apₖ-wkₖ-wk : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
                 → apₖ (wkₖ m ϕ) _ x ≡ wk _ (apₖ ϕ _ x)

    apₖ-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : (µ₁ ▷ m) –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
      → apₖ (ϕ ↓) _ x ≡ apₖ ϕ _ (there x)

    wkₖ*-[] : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → wkₖ* [] ϕ ~ ϕ
    wkₖ*-▷ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → wkₖ* (µ ▷ m) ϕ ~ wkₖ m (wkₖ* µ ϕ)

    ↑-,ₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) m
      → (ϕ ↑ m) ~ (wkₖ m ϕ ,ₖ id/` _ (here refl))

    ↑*-[]  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → (ϕ ↑* []) ~ ϕ

    ↑*-▷  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → (ϕ ↑* (µ ▷ m)) ~ ((ϕ ↑* µ) ↑ m)

    id-[] : ∀ ⦃ 𝕂 : Kit ⦄
      → id {[]} ~ []ₖ

    id-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
      → id {µ ▷ m} ~ (id {µ} ↑ m)

    []*-[]  : ∀ ⦃ 𝕂 : Kit ⦄
      → []* {[]} ~ []ₖ

    []*-▷  : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
      → []* {µ ▷ m} ~ wkₖ m ([]* {µ})

    ↓-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
      → ((ϕ ,ₖ x/t) ↓) ~ ϕ

    ∥-[] : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ} → (ϕ₁ : µ₁ –[ 𝕂 ]→ µ) → (ϕ₂ : [] –[ 𝕂 ]→ µ)
      → (ϕ₁ ∥ ϕ₂) ~ ϕ₁

    ∥-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ µ m} → (ϕ₁ : µ₁ –[ 𝕂 ]→ µ) → (ϕ₂ : (µ₂ ▷ m) –[ 𝕂 ]→ µ)
      → (ϕ₁ ∥ ϕ₂) ~ subst (_–[ 𝕂 ]→ µ) (sym (++-assoc ([] ▷ m) µ₂ µ₁)) ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ apₖ ϕ₂ _ (here refl))

    ⦅⦆-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m} (x/t : µ ∋/⊢ id/m→M m) →
      ⦅ x/t ⦆ ~ (id ,ₖ x/t)

    invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ

  invert : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ ϕ
  invert ϕ = invert-ϕ'→ϕ (invert' ϕ)

  -- id-↑* : ∀ ⦃ 𝕂 : Kit ⦄ {µ}
  --     → id {µ} ~ subst (λ ■ → ■ –[ 𝕂 ]→ ■) (++-identityʳ µ) ([]ₖ ↑* µ)
  -- id-↑* {µ = []} = ~-trans id-[] (~-sym (↑*-[] []ₖ))
  -- id-↑* {µ = µ ▷ x} = {!!}

  -- Weakening preserves Homotopy

  ~-cong-wk : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    wkₖ m ϕ ~ wkₖ m ϕ'
  ~-cong-wk {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
    apₖ (wkₖ _ ϕ) mx x  ≡⟨ apₖ-wkₖ-wk ϕ x ⟩
    wk _ (apₖ ϕ mx x)   ≡⟨ cong (wk _) (ϕ~ϕ' mx x) ⟩
    wk _ (apₖ ϕ' mx x)  ≡⟨ sym (apₖ-wkₖ-wk ϕ' x)⟩
    apₖ (wkₖ _ ϕ') mx x ∎

  -- ~-cong-wk* : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ ϕ' : µ₁ –→ µ₂} →
  --   ϕ ~ ϕ' →
  --   wkₖ* µ ϕ ~ wkₖ* µ ϕ'
  -- ~-cong-wk* {µ = []}    ϕ~ϕ' = ϕ~ϕ'
  -- ~-cong-wk* {µ = µ ▷ m} ϕ~ϕ' = ~-cong-wk (~-cong-wk* ϕ~ϕ')

  -- Lifting preserves Homotopy

  ~-cong-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –→ µ₂} (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
    ϕ ~ ϕ' →
    (ϕ ,ₖ x/t) ~ (ϕ' ,ₖ x/t)
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {.mx} {ϕ} {ϕ'} x/t ϕ~ϕ' mx (here refl) =
    apₖ (ϕ ,ₖ x/t) mx (here refl)  ≡⟨ apₖ-,ₖ-here ϕ x/t ⟩
    x/t                            ≡⟨ sym (apₖ-,ₖ-here ϕ' x/t) ⟩
    apₖ (ϕ' ,ₖ x/t) mx (here refl) ∎
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {m} {ϕ} {ϕ'} x/t ϕ~ϕ' mx (there x) =
    apₖ (ϕ ,ₖ x/t) mx (there x)  ≡⟨ apₖ-,ₖ-there ϕ x/t x ⟩
    apₖ ϕ mx x                   ≡⟨ ϕ~ϕ' mx x ⟩
    apₖ ϕ' mx x                  ≡⟨ sym (apₖ-,ₖ-there ϕ' x/t x) ⟩
    apₖ (ϕ' ,ₖ x/t) mx (there x) ∎

  -- ~-cong-↑ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –→ µ₂} →
  --   ϕ ~ ϕ' →
  --   (ϕ ↑ m) ~ (ϕ' ↑ m)
  -- ~-cong-↑ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' = ~-cong-,ₖ _ (~-cong-wk ϕ~ϕ')

  -- ~-cong-↑* : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ ϕ' : µ₁ –→ µ₂} →
  --   ϕ ~ ϕ' →
  --   (ϕ ↑* µ) ~ (ϕ' ↑* µ)
  -- ~-cong-↑* {µ = []}    ϕ~ϕ' = ϕ~ϕ'
  -- ~-cong-↑* {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' = ~-cong-↑ (~-cong-↑* ϕ~ϕ')

  -- Identity


  -- idₖ' : µ –→ (µ' ▷▷ µ )
  -- idₖ' _ x = id/` _ (∈-▷▷ₗ x)  where
  --   ∈-▷▷ₗ : µ ∋ m → (µ' ▷▷ µ) ∋ m
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- idₖ'' : ∀ {µ µ' µ''} → µ –→ (µ' ▷▷ µ ▷▷ µ'')
  -- idₖ'' {µ} {µ'} {µ''} _ x = wk* {µ' = µ''} _ (id/` _ (∈-▷▷ₗ x))  where
  --   ∈-▷▷ₗ :  ∀ {µ} {µ'} → µ ∋ m → (µ' ▷▷ µ) ∋ m
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- Lifted identity is identity

  -- TODO: However now this holds definitionally...

  -- id↑~id : ∀ m µ → idₖ {µ = µ} ↑ m ~ idₖ {µ = µ ▷ m}
  -- id↑~id m µ _ (here _)  = refl
  -- id↑~id m µ _ (there x) = wk-id/` m x

  -- id↑*~id : ∀ µ' µ → idₖ {µ = µ} ↑* µ' ~ idₖ {µ = µ ▷▷ µ'}
  -- id↑*~id []       µ = ~-refl
  -- id↑*~id (µ' ▷ m) µ =
  --   idₖ ↑* µ' ↑ m  ~⟨ ~-cong-↑ (id↑*~id µ' µ) ⟩
  --   idₖ ↑ m        ~⟨ id↑~id _ _ ⟩
  --   idₖ            ~∎

  -- Empty Substitution

  apₖ-[]ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {m} x → apₖ []ₖ m x ≡ id/` m x
  apₖ-[]ₖ ()

  apₖ-[]ₖ' : ∀ ⦃ 𝕂 : Kit ⦄ (ϕ : [] –[ 𝕂 ]→ []) → ϕ ~ []ₖ
  apₖ-[]ₖ' ϕ m ()

  -- -- Singleton renaming/substitution

  -- -- Singleton renaming/substitution for terms with 1 free variable.
  -- -- Allows the term to be substituted to have arbitrary free variables.
  -- -- This is useful for things like pattern inverting in combination with `_∥_`,
  -- -- where a inverting substitution needs to be built up piece by piece.
  -- ⦅_⦆₀ : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
  -- ⦅ v ⦆₀ = emptyₖ ,ₖ v

  -- -- ⦅_⦆' : (µ ▷▷ µ') ∋/⊢ m→[m/M] m → (µ ▷ m ▷▷ µ') –→ (µ ▷▷ µ')
  -- -- ⦅ v ⦆' = idₖ'' ∥ ⦅ v ⦆₀ ∥ idₖ''
  -- -- ⦅ v ⦆' = {!!} ∥ ⦅ v ⦆₀ ∥ {!!}
  -- -- -- ⦅ v ⦆' = (idₖ ∥ ⦅ v ⦆₀) ↑* _

-- Functions as Substitutions

module Functional where

  module Functional-Sub where
    _–[_]→_ : List VarMode → Kit → List VarMode → Set
    _–[_]→_ = λ µ₁ 𝕂 µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m)

    []ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ} → [] –[ 𝕂 ]→ µ
    []ₖ _ ()

    _,ₖ_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
    (ϕ ,ₖ t) _ (here refl) = t
    (ϕ ,ₖ t) _ (there x)   = ϕ _ x

    wkₖ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
    wkₖ m ϕ mx x = wk (id/m→M mx) (ϕ mx x)

    wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
    wkₖ* []      ϕ = ϕ
    wkₖ* (µ ▷ m) ϕ = wkₖ m (wkₖ* µ ϕ)

    _↑_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
    ϕ ↑ m = wkₖ m ϕ ,ₖ id/` _ (here refl)

    _↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
    ϕ ↑* []       = ϕ
    ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

    id : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
    id = id/`

    _↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → ((µ₁ ▷ m) –[ 𝕂 ]→ µ₂) → (µ₁ –[ 𝕂 ]→ µ₂)
    (ϕ ↓) _ x = ϕ _ (there x)

    _∥_ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
    _∥_            {µ₂ = []}    σ₁ σ₂ = σ₁
    _∥_ ⦃ 𝕂 ⦄ {µ₁} {µ₂ ▷ m} {µ} σ₁ σ₂ = subst (_–[ 𝕂 ]→ µ) (sym (++-assoc ([] ▷ m) µ₂ µ₁)) ((σ₁ ∥ (σ₂ ↓)) ,ₖ σ₂ _ (here refl))

    ⦅_⦆ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
    ⦅ v ⦆ = idₖ ,ₖ v

    apₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
    apₖ ϕ = ϕ

    instance
      Sub-→ : Sub
      Sub-→ = record
        { _–[_]→_      = _–[_]→_
        ; []ₖ          = []ₖ
        ; _,ₖ_         = _,ₖ_
        ; wkₖ          = wkₖ
        ; wkₖ*         = wkₖ*
        ; _↑_          = _↑_
        ; _↑*_         = _↑*_
        ; id           = id
        ; []*          = []ₖ
        ; _↓           = _↓
        ; _∥_          = _∥_
        ; ⦅_⦆          = ⦅_⦆
        ; apₖ          = apₖ
        }

  module Functional-Sub-With-Laws where
    open Sub Functional-Sub.Sub-→

    id-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
      → id {µ ▷ m} ~ (id {µ} ↑ m)
    id-▷ m (here refl) = refl
    id-▷ m (there x) = sym (wk-id/` _ x)

    invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ
    invert' {µ₁ = []}      ϕ = ϕ~[]* refl (λ m ())
    invert' {µ₁ = µ₁ ▷ m₁} ϕ = ϕ~,ₖ refl (ϕ ↓) (ϕ _ (here refl)) λ where
      m (here refl) → refl
      m (there x) → refl

    instance
      SubWithLaws-→ : SubWithLaws
      SubWithLaws-→ = record
        { apₖ-,ₖ-here  = λ ϕ x/t → refl
        ; apₖ-,ₖ-there = λ ϕ x/t x → refl
        ; apₖ-wkₖ-wk   = λ ϕ x → refl
        ; apₖ-↓        = λ ϕ x → refl
        ; wkₖ*-[]      = λ ϕ m x → refl
        ; wkₖ*-▷       = λ µ m ϕ mx x → refl
        ; ↑-,ₖ         = λ ϕ m mx x → refl
        ; ↑*-[]        = λ ϕ m x → refl
        ; ↑*-▷         = λ µ m ϕ m₁ x → refl
        ; id-[]        = λ m ()
        ; id-▷         = id-▷
        ; []*-[]       = λ m x → refl
        ; []*-▷        = λ m ()
        ; ↓-,ₖ         = λ ϕ x/t m x → refl
        ; ∥-[]         = λ ϕ₁ ϕ₂ m x → refl
        ; ∥-▷          = λ ϕ₁ ϕ₂ m x → refl
        ; ⦅⦆-,ₖ        = λ x/t m x → refl
        ; invert'      = invert'
        }

-- -- Lists as Substitutions

-- open import Data.List.Relation.Unary.All

-- ap-all : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
-- ap-all (x/t ∷ ϕ) m (here refl) = x/t
-- ap-all (x/t ∷ ϕ) m (there x) = ap-all ϕ m x

-- instance
--   Sub-All : Sub
--   Sub._–[_]→_      Sub-All = λ µ₁ 𝕂 µ₂ → All (λ m₁ → µ₂ ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m₁) µ₁
--   Sub.[]ₖ          Sub-All = []
--   Sub._,ₖ_         Sub-All = λ ϕ x/t → x/t ∷ ϕ
--   Sub.wkₖ          Sub-All = λ m ϕ → map (wk _) ϕ
--   Sub.apₖ          Sub-All = ap-all
--   Sub.apₖ-,ₖ-here  Sub-All = λ ϕ x/t → refl
--   Sub.apₖ-,ₖ-there Sub-All = λ ϕ x/t x → refl
--   Sub.apₖ-wkₖ-wk   Sub-All = λ ϕ x/t → {!!}

-- -- Syntax as Substitutions

-- data _–[_]→_ : List VarMode → Kit → List VarMode → Set where
--   []ₖ  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→ []
--   _,ₖ_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
--   wkₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)

-- ap : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → (∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m)
-- ap (ϕ ,ₖ x/t) m (here refl) = x/t
-- ap (ϕ ,ₖ x/t) m (there x) = ap ϕ m x
-- ap (wkₖ m' ϕ) m x = wk _ (ap ϕ m x)

-- instance
--   Sub-Sub : Sub
--   Sub._–[_]→_      Sub-Sub = _–[_]→_
--   Sub.[]ₖ          Sub-Sub = []ₖ
--   Sub._,ₖ_         Sub-Sub = _,ₖ_
--   Sub.wkₖ          Sub-Sub = wkₖ
--   Sub.apₖ          Sub-Sub = ap
--   Sub.apₖ-,ₖ-here  Sub-Sub = λ ϕ x/t → refl
--   Sub.apₖ-,ₖ-there Sub-Sub = λ ϕ x/t x → refl
--   Sub.apₖ-wkₖ-wk   Sub-Sub = λ ϕ x/t → refl
