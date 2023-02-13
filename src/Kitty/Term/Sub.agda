open import Kitty.Term.Modes

module Kitty.Term.Sub {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
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
    _∥_  : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
    ⦅_⦆  : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ

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

  ~-cong-subst-µ₁ :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₁'} {µ₂} {f g : µ₁ –[ 𝕂 ]→ µ₂} (eq : µ₁ ≡ µ₁')
    → f ~ g
    → subst (_–[ 𝕂 ]→ µ₂) eq f ~ subst (_–[ 𝕂 ]→ µ₂) eq g
  ~-cong-subst-µ₁ refl f~g = f~g

  ~-cong-subst-µ₂ :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₂'} {f g : µ₁ –[ 𝕂 ]→ µ₂} (eq : µ₂ ≡ µ₂')
    → f ~ g
    → subst (µ₁ –[ 𝕂 ]→_) eq f ~ subst (µ₁ –[ 𝕂 ]→_) eq g
  ~-cong-subst-µ₂ refl f~g = f~g

  module ~-Reasoning where

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      µ₁ µ₂ µ₃ : List VarMode
      ⦃ 𝕂 ⦄ : Kit
      f g h : µ₁ –[ 𝕂 ]→ µ₂

    begin~_ :
      ∀ ⦃ 𝕂 ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ 𝕂 ⦄ (f {g} : µ₁ –[ 𝕂 ]→ µ₂)
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~ h → f ~ g → f ~ h
    step-~ _ g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ 𝕂 ⦄ (f : µ₁ –[ 𝕂 ]→ µ₂)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

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

  data Invert-ϕ'-Rec ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) : µ₁ –[ 𝕂 ]→ µ₂ → Set where
    ϕ~[]* :
      (eq : µ₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ'-Rec ϕ (sub []*)
    ϕ~,ₖ : ∀ {µ₁' m₁} →
      (eq : µ₁ ≡ µ₁' ▷ m₁) →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      (ϕ'' : µ₁' –[ 𝕂 ]→ µ₂) →
      Invert-ϕ'-Rec ϕ' ϕ'' →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      ϕ ~ sub (ϕ'' ,ₖ x/t) →
      Invert-ϕ'-Rec ϕ (sub (ϕ'' ,ₖ x/t))

  invert-ϕ'→ϕ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  invert-ϕ'→ϕ (ϕ~[]* refl ϕ~) = ϕ~[]* ϕ~
  invert-ϕ'→ϕ (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

  -- requires dependent subst
  -- invert-ϕ'→ϕ' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  -- invert-ϕ'→ϕ' {µ₁} {µ₂} {ϕ} (ϕ~[]* µ₁≡[] ϕ~) = {!subst₂ (λ ■ ■' → Invert-ϕ {µ₁ = ■} ■') ? ? {!ϕ~[]* ϕ~!}!}
  -- invert-ϕ'→ϕ' (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

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

  open ~-Reasoning

  -- id-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ µ'}
  --   → id {µ ▷▷ µ'} ~ (id {µ} ↑* µ')
  -- id-▷▷ {µ' = []} = ~-sym (↑*-[] id)
  -- id-▷▷ {µ' = µ' ▷ m} = ~-trans {!id-▷▷!} (~-trans {!id-▷!} (~-sym (↑*-▷ µ' m id)))

  -- Weakening preserves Homotopy

  ~-cong-wk : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    wkₖ m ϕ ~ wkₖ m ϕ'
  ~-cong-wk {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
    apₖ (wkₖ _ ϕ) mx x  ≡⟨ apₖ-wkₖ-wk ϕ x ⟩
    wk _ (apₖ ϕ mx x)   ≡⟨ cong (wk _) (ϕ~ϕ' mx x) ⟩
    wk _ (apₖ ϕ' mx x)  ≡⟨ sym (apₖ-wkₖ-wk ϕ' x)⟩
    apₖ (wkₖ _ ϕ') mx x ∎

  ~-cong-wk* : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    wkₖ* µ ϕ ~ wkₖ* µ ϕ'
  ~-cong-wk* {µ = []} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
    wkₖ* [] ϕ' ~∎
  ~-cong-wk* {µ = µ ▷ m} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* (µ ▷ m) ϕ    ~⟨ wkₖ*-▷ µ m ϕ ⟩
    wkₖ m (wkₖ* µ ϕ)  ~⟨ ~-cong-wk (~-cong-wk* ϕ~ϕ') ⟩
    wkₖ m (wkₖ* µ ϕ') ~⟨ ~-sym (wkₖ*-▷ µ m ϕ') ⟩
    wkₖ* (µ ▷ m) ϕ' ~∎

  -- Lifting preserves Homotopy

  ~-cong-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂} {x/t x/t' : µ₂ ∋/⊢[ 𝕂 ] id/m→M m} →
    ϕ ~ ϕ' →
    x/t ≡ x/t' →
    (ϕ ,ₖ x/t) ~ (ϕ' ,ₖ x/t')
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {.mx} {ϕ} {ϕ'} {x/t} {x/t'} ϕ~ϕ' x/t≡x/t' mx (here refl) =
    apₖ (ϕ ,ₖ x/t) mx (here refl)  ≡⟨ apₖ-,ₖ-here ϕ x/t ⟩
    x/t                            ≡⟨ x/t≡x/t' ⟩
    x/t'                           ≡⟨ sym (apₖ-,ₖ-here ϕ' x/t') ⟩
    apₖ (ϕ' ,ₖ x/t') mx (here refl) ∎
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {m} {ϕ} {ϕ'} {x/t} {x/t'} ϕ~ϕ' x/t≡x/t' mx (there x) =
    apₖ (ϕ ,ₖ x/t) mx (there x)  ≡⟨ apₖ-,ₖ-there ϕ x/t x ⟩
    apₖ ϕ mx x                   ≡⟨ ϕ~ϕ' mx x ⟩
    apₖ ϕ' mx x                  ≡⟨ sym (apₖ-,ₖ-there ϕ' x/t' x) ⟩
    apₖ (ϕ' ,ₖ x/t') mx (there x) ∎

  ~-cong-↓ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : (µ₁ ▷ m) –[ 𝕂 ]→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↓) ~ (ϕ' ↓)
  ~-cong-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
    apₖ (ϕ  ↓) mx x     ≡⟨ apₖ-↓ ϕ x ⟩
    apₖ ϕ  mx (there x) ≡⟨ ϕ~ϕ' mx (there x) ⟩
    apₖ ϕ' mx (there x) ≡⟨ sym (apₖ-↓ ϕ' x) ⟩
    apₖ (ϕ' ↓) mx x     ∎

  ~-cong-∥ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁₁} {µ₁₂} {µ₂} {ϕ₁ ϕ₁' : µ₁₁ –[ 𝕂 ]→ µ₂} {ϕ₂ ϕ₂' : µ₁₂ –[ 𝕂 ]→ µ₂} →
    ϕ₁ ~ ϕ₁' →
    ϕ₂ ~ ϕ₂' →
    (ϕ₁ ∥ ϕ₂) ~ (ϕ₁' ∥ ϕ₂')
  ~-cong-∥ {µ₁₁ = µ₁₁} {[]}      {µ₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    (ϕ₁ ∥ ϕ₂)   ~⟨ ∥-[] ϕ₁ ϕ₂ ⟩
    ϕ₁          ~⟨ ϕ₁~ϕ₁' ⟩
    ϕ₁'         ~⟨ ~-sym (∥-[] ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎
  ~-cong-∥ ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂ ▷ m} {µ₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    let sub = subst (_–[ 𝕂 ]→ µ₂) (sym (++-assoc ([] ▷ m) µ₁₂ µ₁₁)) in
    (ϕ₁ ∥ ϕ₂)                                      ~⟨ ∥-▷ ϕ₁ ϕ₂ ⟩
    sub ((ϕ₁  ∥ (ϕ₂  ↓)) ,ₖ apₖ ϕ₂  _ (here refl)) ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m) µ₁₂ µ₁₁))
                                                      (~-cong-,ₖ (~-cong-∥ ϕ₁~ϕ₁' (~-cong-↓ ϕ₂~ϕ₂'))
                                                                 (ϕ₂~ϕ₂' _ (here refl))) ⟩
    sub ((ϕ₁' ∥ (ϕ₂' ↓)) ,ₖ apₖ ϕ₂' _ (here refl)) ~⟨ ~-sym (∥-▷ ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎

  invert : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ ϕ
  invert ϕ = invert-ϕ'→ϕ (invert' ϕ)

  invert'-rec : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Σ[ ϕ' ∈ µ₁ –[ 𝕂 ]→ µ₂ ] Invert-ϕ'-Rec ϕ ϕ' × ϕ ~ ϕ'
  invert'-rec ϕ with invert ϕ
  ... | ϕ~[]* ϕ~[] = []* , ϕ~[]* refl ϕ~[] , ϕ~[]
  ... | ϕ~,ₖ ϕ' x/t ϕ~ϕ',x/t with invert'-rec ϕ'
  ...   | ϕ'' , inv , ϕ'~ϕ'' = let ϕ~ϕ'',x/t = ~-trans ϕ~ϕ',x/t (~-cong-,ₖ ϕ'~ϕ'' refl) in
                               (ϕ'' ,ₖ x/t) , ϕ~,ₖ refl ϕ' x/t ϕ'' inv ϕ~ϕ',x/t ϕ~ϕ'',x/t , ϕ~ϕ'',x/t

  ~-cong-↑ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↑ m) ~ (ϕ' ↑ m)
  ~-cong-↑ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' =
    (ϕ ↑ m)                           ~⟨ ↑-,ₖ ϕ m ⟩
    (wkₖ _ ϕ ,ₖ id/` _ (here refl))   ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') refl ⟩
    (wkₖ _ ϕ' ,ₖ id/` _ (here refl))  ~⟨ ~-sym (↑-,ₖ ϕ' m) ⟩
    (ϕ' ↑ m)                          ~∎

  ~-cong-↑* : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↑* µ) ~ (ϕ' ↑* µ)
  ~-cong-↑* {µ = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
    (ϕ' ↑* []) ~∎
  ~-cong-↑* {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* (µ ▷ m))  ~⟨ ↑*-▷ µ m ϕ ⟩
    (ϕ ↑* µ) ↑ m    ~⟨ ~-cong-↑ (~-cong-↑* ϕ~ϕ') ⟩
    (ϕ' ↑* µ) ↑ m   ~⟨ ~-sym (↑*-▷ µ m ϕ') ⟩
    (ϕ' ↑* (µ ▷ m)) ~∎


  dist-wk-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} m {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m') →
    wkₖ m (ϕ ,ₖ x/t) ~ (wkₖ m ϕ ,ₖ Kit.wk 𝕂 _ x/t)
  dist-wk-,ₖ ⦃ 𝕂 ⦄ m ϕ x/t mx (here refl) =
    apₖ (wkₖ m (ϕ ,ₖ x/t)) _ (here refl)     ≡⟨ apₖ-wkₖ-wk (ϕ ,ₖ x/t) (here refl) ⟩
    wk _ (apₖ (ϕ ,ₖ x/t) _ (here refl))      ≡⟨ cong (wk _) (apₖ-,ₖ-here ϕ x/t) ⟩
    wk _ x/t                                 ≡⟨ sym (apₖ-,ₖ-here (wkₖ m ϕ) (wk _ x/t)) ⟩
    apₖ (wkₖ m ϕ ,ₖ wk _ x/t) _ (here refl) ∎
  dist-wk-,ₖ m ϕ x/t mx (there x) =
    apₖ (wkₖ _ (ϕ ,ₖ x/t)) _ (there x)    ≡⟨ apₖ-wkₖ-wk (ϕ ,ₖ x/t) (there x) ⟩
    wk _ (apₖ (ϕ ,ₖ x/t) _ (there x))     ≡⟨ cong (wk _) (apₖ-,ₖ-there ϕ x/t x) ⟩
    wk _ (apₖ ϕ _ x)                      ≡⟨ sym (apₖ-wkₖ-wk ϕ x) ⟩
    apₖ (wkₖ _ ϕ) _ x                     ≡⟨ sym (apₖ-,ₖ-there (wkₖ m ϕ) (wk _ x/t) x) ⟩
    apₖ (wkₖ _ ϕ ,ₖ wk _ x/t) _ (there x) ∎

  dist-wk*-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m') →
    wkₖ* µ (ϕ ,ₖ x/t) ~ (wkₖ* µ ϕ ,ₖ wk* _ x/t)
  dist-wk*-,ₖ []      ϕ x/t =
    wkₖ* [] (ϕ ,ₖ x/t)       ~⟨ wkₖ*-[] (ϕ ,ₖ x/t) ⟩
    ϕ ,ₖ x/t                 ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-[] ϕ)) refl ⟩
    (wkₖ* [] ϕ ,ₖ x/t)       ~⟨⟩
    (wkₖ* [] ϕ ,ₖ wk* _ x/t) ~∎
  dist-wk*-,ₖ (µ ▷ m) ϕ x/t =
    wkₖ* (µ ▷ m) (ϕ ,ₖ x/t)                ~⟨ wkₖ*-▷ µ m (ϕ ,ₖ x/t) ⟩
    wkₖ m (wkₖ* µ (ϕ ,ₖ x/t))              ~⟨ ~-cong-wk (dist-wk*-,ₖ µ ϕ x/t) ⟩
    wkₖ m (wkₖ* µ ϕ ,ₖ wk* _ x/t)          ~⟨ dist-wk-,ₖ m (wkₖ* µ ϕ) (wk* _ x/t) ⟩
    (wkₖ m (wkₖ* µ ϕ) ,ₖ wk _ (wk* _ x/t)) ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-▷ µ m ϕ)) refl ⟩
    (wkₖ* (µ ▷ m) ϕ ,ₖ wk* _ x/t)          ~∎

  open import Kitty.Util.SubstProperties

  wkₖ*-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ µ' (ϕ : µ₁ –[ 𝕂 ]→ µ₂)  →
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
    wkₖ* µ (wkₖ* µ' ϕ) ~ sub (wkₖ* (µ' ▷▷ µ) ϕ)
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} [] µ' ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc [] µ' µ₂) in
    wkₖ* [] (wkₖ* µ' ϕ)     ~⟨ wkₖ*-[] (wkₖ* µ' ϕ) ⟩
    wkₖ* µ' ϕ               ~⟨⟩
    sub (wkₖ* (µ' ▷▷ []) ϕ) ~∎
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (µ ▷ m) µ' ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc (µ ▷ m) µ' µ₂) in
    let sub' = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
    wkₖ* (µ ▷ m) (wkₖ* µ' ϕ)        ~⟨ wkₖ*-▷ µ m (wkₖ* µ' ϕ) ⟩
    wkₖ m (wkₖ* µ (wkₖ* µ' ϕ))      ~⟨ ~-cong-wk (wkₖ*-▷▷ µ µ' ϕ) ⟩
    wkₖ m (sub' (wkₖ* (µ' ▷▷ µ) ϕ)) ~≡⟨ dist-subst' (_▷ m) (wkₖ m) (++-assoc µ µ' µ₂) (++-assoc (µ ▷ m) µ' µ₂) (wkₖ* (µ' ▷▷ µ) ϕ) ⟩
    sub (wkₖ m (wkₖ* (µ' ▷▷ µ) ϕ))  ~⟨ ~-cong-subst-µ₂ (++-assoc (µ ▷ m) µ' µ₂) (~-sym (wkₖ*-▷ (µ' ▷▷ µ) m ϕ)) ⟩
    sub (wkₖ* (µ' ▷▷ (µ ▷ m)) ϕ)    ~∎

  wkₖ-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)  →
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ ([] ▷ m) µ₂) in
    wkₖ* µ (wkₖ m ϕ) ~ sub (wkₖ* (([] ▷ m) ▷▷ µ) ϕ)
  wkₖ-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ ([] ▷ m) µ₂) in
    wkₖ* µ (wkₖ m ϕ)             ~⟨ ~-cong-wk* (~-cong-wk (~-sym (wkₖ*-[] ϕ))) ⟩
    wkₖ* µ (wkₖ m (wkₖ* [] ϕ))   ~⟨ ~-cong-wk* (~-sym (wkₖ*-▷ [] m ϕ)) ⟩
    wkₖ* µ (wkₖ* ([] ▷ m) ϕ)     ~⟨ wkₖ*-▷▷ µ ([] ▷ m) ϕ ⟩
    sub (wkₖ* (([] ▷ m) ▷▷ µ) ϕ) ~∎

  dist-wk-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ m m'} → (ϕ : (µ₁ ▷ m') –[ 𝕂 ]→ µ₂) →
    wkₖ m (ϕ ↓) ~ (wkₖ m ϕ ↓)
  dist-wk-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} ϕ mx x =
    apₖ (wkₖ m (ϕ ↓)) mx x     ≡⟨ apₖ-wkₖ-wk (ϕ ↓) x ⟩
    wk _ (apₖ (ϕ ↓) mx x)      ≡⟨ cong (wk _) (apₖ-↓ ϕ x) ⟩
    wk _ (apₖ ϕ mx (there x))  ≡⟨ sym (apₖ-wkₖ-wk ϕ (there x)) ⟩
    apₖ (wkₖ m ϕ) mx (there x) ≡⟨ sym (apₖ-↓ (wkₖ m ϕ) x) ⟩
    apₖ (wkₖ m ϕ ↓) mx x       ∎

  dist-wk*-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ m'} → (ϕ : (µ₁ ▷ m') –[ 𝕂 ]→ µ₂) →
    wkₖ* µ (ϕ ↓) ~ (wkₖ* µ ϕ ↓)
  dist-wk*-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ = []}    {m'} ϕ =
    wkₖ* [] (ϕ ↓) ~⟨ wkₖ*-[] (ϕ ↓) ⟩
    (ϕ ↓)         ~⟨ ~-cong-↓ (~-sym (wkₖ*-[] ϕ)) ⟩
    (wkₖ* [] ϕ ↓) ~∎
  dist-wk*-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ = µ ▷ m} {m'} ϕ =
    wkₖ* (µ ▷ m) (ϕ ↓) ~⟨ wkₖ*-▷ µ m (ϕ ↓) ⟩
    wkₖ m (wkₖ* µ (ϕ ↓)) ~⟨ ~-cong-wk (dist-wk*-↓ ϕ) ⟩
    wkₖ m (wkₖ* µ ϕ ↓)   ~⟨ dist-wk-↓ (wkₖ* µ ϕ) ⟩
    (wkₖ m (wkₖ* µ ϕ) ↓) ~⟨ ~-cong-↓ (~-sym (wkₖ*-▷ µ m ϕ)) ⟩
    (wkₖ* (µ ▷ m) ϕ ↓) ~∎

  ∥-wk : ∀ ⦃ 𝕂 ⦄ {µ₁₁ µ₁₂ µ₂} m → (ϕ₁ : µ₁₁ –[ 𝕂 ]→ µ₂) → (ϕ₂ : µ₁₂ –[ 𝕂 ]→ µ₂) →
    wkₖ m (ϕ₁ ∥ ϕ₂) ~ (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂)
  ∥-wk ⦃ 𝕂 ⦄ {µ₁₁} {[]} {µ₂} m ϕ₁ ϕ₂ =
    wkₖ m (ϕ₁ ∥ ϕ₂)        ~⟨ ~-cong-wk (∥-[] ϕ₁ ϕ₂) ⟩
    wkₖ m ϕ₁               ~⟨ ~-sym (∥-[] (wkₖ m ϕ₁) (wkₖ m ϕ₂)) ⟩
    (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂)  ~∎
  ∥-wk ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂ ▷ m₂} {µ₂} m ϕ₁ ϕ₂ =
    let sub = subst (_–[ 𝕂 ]→ µ₂) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁)) in
    let sub' = subst (_–[ 𝕂 ]→ (µ₂ ▷ m)) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁)) in
    wkₖ m (ϕ₁ ∥ ϕ₂)                                                  ~⟨ ~-cong-wk (∥-▷ ϕ₁ ϕ₂) ⟩
    wkₖ m (sub ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ apₖ ϕ₂ _ (here refl)))              ~≡⟨ dist-subst {F = _–[ 𝕂 ]→ µ₂} {G = _–[ 𝕂 ]→ (µ₂ ▷ m)}
                                                                                    (wkₖ m) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                                    ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ apₖ ϕ₂ _ (here refl)) ⟩
    sub' (wkₖ m ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ apₖ ϕ₂ _ (here refl)))             ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (dist-wk-,ₖ m (ϕ₁ ∥ (ϕ₂ ↓)) (apₖ ϕ₂ _ (here refl))) ⟩
    sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ wk _ (apₖ ϕ₂ _ (here refl)))        ~≡⟨ cong (λ ■ → sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ ■))
                                                                         (sym (apₖ-wkₖ-wk ϕ₂ (here refl))) ⟩ 
    sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ apₖ (wkₖ m ϕ₂) _ (here refl))       ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (~-cong-,ₖ (∥-wk m ϕ₁ (ϕ₂ ↓)) refl) ⟩
    sub' ((wkₖ m ϕ₁ ∥ wkₖ m (ϕ₂ ↓)) ,ₖ apₖ (wkₖ m ϕ₂) _ (here refl)) ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (~-cong-,ₖ (~-cong-∥ ~-refl (dist-wk-↓ ϕ₂)) refl) ⟩
    sub' ((wkₖ m ϕ₁ ∥ (wkₖ m ϕ₂ ↓)) ,ₖ apₖ (wkₖ m ϕ₂) _ (here refl)) ~⟨ ~-sym (∥-▷ (wkₖ m ϕ₁) (wkₖ m ϕ₂)) ⟩
    (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂) ~∎

  ∥-wk* : ∀ ⦃ 𝕂 ⦄ {µ₁₁ µ₁₂ µ₂} µ → (ϕ₁ : µ₁₁ –[ 𝕂 ]→ µ₂) → (ϕ₂ : µ₁₂ –[ 𝕂 ]→ µ₂) →
    wkₖ* µ (ϕ₁ ∥ ϕ₂) ~ (wkₖ* µ ϕ₁ ∥ wkₖ* µ ϕ₂)
  ∥-wk* ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂} {µ₂} []      ϕ₁ ϕ₂ =
    wkₖ* [] (ϕ₁ ∥ ϕ₂)         ~⟨ wkₖ*-[] (ϕ₁ ∥ ϕ₂) ⟩
    (ϕ₁ ∥ ϕ₂)                 ~⟨ ~-sym (~-cong-∥ (wkₖ*-[] ϕ₁) (wkₖ*-[] ϕ₂)) ⟩
    (wkₖ* [] ϕ₁ ∥ wkₖ* [] ϕ₂) ~∎
  ∥-wk* ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂} {µ₂} (µ ▷ m) ϕ₁ ϕ₂ =
    wkₖ* (µ ▷ m) (ϕ₁ ∥ ϕ₂)                  ~⟨ wkₖ*-▷ µ m (ϕ₁ ∥ ϕ₂) ⟩
    wkₖ m (wkₖ* µ (ϕ₁ ∥ ϕ₂))                ~⟨ ~-cong-wk (∥-wk* µ ϕ₁ ϕ₂) ⟩
    wkₖ m (wkₖ* µ ϕ₁ ∥ wkₖ* µ ϕ₂)           ~⟨ ∥-wk m (wkₖ* µ ϕ₁) (wkₖ* µ ϕ₂) ⟩
    (wkₖ m (wkₖ* µ ϕ₁) ∥ wkₖ m (wkₖ* µ ϕ₂)) ~⟨ ~-sym (~-cong-∥ (wkₖ*-▷ µ m ϕ₁) (wkₖ*-▷ µ m ϕ₂)) ⟩
    (wkₖ* (µ ▷ m) ϕ₁ ∥ wkₖ* (µ ▷ m) ϕ₂)     ~∎

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
