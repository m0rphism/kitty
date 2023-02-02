open import Kitty.Modes

module Kitty.Types {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Prelude

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level

record KitType : Set₁ where
  field
    ↑ₜ : TermMode → TermMode

  infix  3  _∶⊢_

  _∶⊢_ : List VarMode → TermMode → Set
  µ ∶⊢ M = µ ⊢ ↑ₜ M

  depth : ∀ {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
  depth (here px) = zero
  depth (there x) = suc (depth x)

  -- We need to drop one extra using `suc`, because otherwise the types in a
  -- context are allowed to use themselves.
  drop-∈ : ∀ {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
  drop-∈ = drop ∘ suc ∘ depth

  Ctx' : List VarMode → List VarMode → Set
  Ctx' µ µ' = ∀ {m} → (x : µ' ∋ m) → drop-∈ x (µ ▷▷ µ') ∶⊢ m→M m

  Ctx'' : List VarMode → List VarMode → Set
  Ctx'' µ µ' = ∀ {m} → (x : µ' ∋ m) → µ ▷▷ drop-∈ x µ' ∶⊢ m→M m

  Ctx : List VarMode → Set
  Ctx µ = ∀ {m} → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m

  private
    variable
      Γ Γ₁ Γ₂    : Ctx µ

  infixl  5  _▶_  _▶[_]_

  _▶_ : Ctx µ → µ ∶⊢ m→M m → Ctx (µ ▷ m)
  (Γ ▶ t) (here refl) = t
  (Γ ▶ t) (there x) = Γ x

  _▶[_]_ : Ctx µ → ∀ m → µ ∶⊢ m→M m → Ctx (µ ▷ m)
  (Γ ▶[ _ ] t) = Γ ▶ t

  -- ∈-++ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {x : A} → (xs ++ ys) ∋ x → (xs ∋ x) ⊎ (ys ∋ x)
  -- ∈-++ {xs = []} x∈ys = inj₂ x∈ys
  -- ∈-++ {xs = xs , x'} (here px) = inj₁ (here px)
  -- ∈-++ {xs = xs , x'} (there x∈[xs++ys]) with ∈-++ x∈[xs++ys]
  -- ... | inj₁ x∈xs = inj₁ (there x∈xs)
  -- ... | inj₂ x∈ys = inj₂ x∈ys

  _▶▶_ : Ctx µ → Ctx' µ µ' → Ctx (µ ▷▷ µ')
  _▶▶_ {µ' = []} Γ Γ' x = Γ x
  _▶▶_ {µ' = µ' ▷ m} Γ Γ' (here px) = Γ' (here px)
  _▶▶_ {µ = µ} {µ' = µ' ▷ m} Γ Γ' (there x) =
    (Γ ▶▶ Γ'') x
    where
      Γ'' : Ctx' µ µ'
      Γ'' x = Γ' (there x)

  _▶▶'_ : Ctx µ → Ctx'' µ µ' → Ctx (µ ▷▷ µ')
  _▶▶'_ {µ' = []} Γ Γ' x = Γ x
  _▶▶'_ {µ' = µ' ▷ m} Γ Γ' (here px) = Γ' (here px)
  _▶▶'_ {µ = µ} {µ' = µ' ▷ m} Γ Γ' (there x) =
    (Γ ▶▶' Γ'') x
    where
      Γ'' : Ctx'' µ µ'
      Γ'' x =  Γ' (there x) 

  -- postulate
    -- _++''_ : Ctx' µ₂ µ₃ → Ctx' µ₁ µ₂ → Ctx' µ₁ (µ₂ ++ µ₁)
  -- _++''_ = {!!}

  _▶'▶_ : Ctx'' µ₁ µ₂ → Ctx'' (µ₁ ▷▷ µ₂) µ₃ → Ctx'' µ₁ (µ₂ ▷▷ µ₃)
  _▶'▶_ {µ₁ = µ₁} {µ₂ = µ₂} {µ₃ = []} Γ'₁ Γ'₂ x = Γ'₁ x
  _▶'▶_ {µ₁ = µ₁} {µ₂ = µ₂} {µ₃ = µ₃ ▷ x₁} Γ'₁ Γ'₂ (here px) rewrite ++-assoc µ₃ µ₂ µ₁ = Γ'₂ (here px)
  _▶'▶_ {µ₁ = µ₁} {µ₂ = µ₂} {µ₃ = µ₃ ▷ x₁} Γ'₁ Γ'₂ (there x) = (Γ'₁ ▶'▶ Γ'₃) x 
    where
      Γ'₃ : Ctx'' (µ₁ ▷▷ µ₂) µ₃
      Γ'₃ x =  Γ'₂ (there x) 

  ∅ : Ctx []
  ∅ ()

  ∅' : Ctx' µ []
  ∅' ()

  ∅'' : Ctx'' µ []
  ∅'' ()

open import Kitty.Kit 𝕋

record KitTypeSubst (KT : KitType) (T : KitTraversal) : Set where
  open KitType KT
  open KitTraversal T
  open Kit {{...}}

  drop-∈-▷▷₁ : (x : µ' ∋ m) → drop-∈ x (µ ▷▷ µ') ≡ µ ▷▷ drop-∈ x µ'
  drop-∈-▷▷₁ (here px) = refl
  drop-∈-▷▷₁ {µ' = µ' ▷ m'} {m = m} {µ = µ} (there x) = drop-∈-▷▷₁ x
    -- drop-∈ (there x) (m' ∷ (µ' ++ µ)) ≡⟨ refl ⟩
    -- drop-∈ x (µ' ++ µ) ≡⟨  ⟩
    -- drop-∈ x µ' ++ µ   ≡⟨ refl ⟩
    -- drop-∈ (there x) (m' ∷ µ') ++ µ   ∎

  infixl  5  _⋯Ctx'_
  _⋯Ctx'_ : ∀ {{𝕂 : Kit}} → Ctx' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx' µ₂ µ'
  _⋯Ctx'_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ f' where
    f' = subst₂
           (λ x y → x –[ 𝕂 ]→ y)
           (sym (drop-∈-▷▷₁ x))
           (sym (drop-∈-▷▷₁ x))
           (f ↑* drop-∈ x µ')

  infixl  5  _⋯Ctx''_
  _⋯Ctx''_ : ∀ {{𝕂 : Kit}} → Ctx'' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx'' µ₂ µ'
  _⋯Ctx''_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ (f ↑* drop-∈ x µ')
