open import Kitty.Term.Modes
open import Kitty.Typing.Types

module Kitty.Typing.CtxRepr {𝕄 : Modes} {𝕋 : Terms 𝕄} (KT : KitType 𝕋) where

open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Term.Prelude

open Modes 𝕄
open Terms 𝕋
open KitType KT using (_∶⊢_)

record CtxRepr : Set₁ where
  field
    Ctx' : List VarMode → List VarMode → Set

    _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)

    lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m

    lookup-▶'-here : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) →
      lookup' (Γ ▶' t) (here refl) ≡ t

    lookup-▶'-there : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) (x : µ₂ ∋ m) →
      lookup' (Γ ▶' t) (there x) ≡ lookup' Γ x

    _~_ : ∀ {µ₁ µ₂} → (Γ₁ Γ₂ : Ctx' µ₁ µ₂) → Set 

    ~-lookup : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
      Γ₁ ~ Γ₂ →
      ∀ {m} (x : µ₂ ∋ m) → lookup' Γ₁ x ≡ lookup' Γ₂ x

    _↓' : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
      
    ↓'-▶' : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) →
      ((Γ ▶' t) ↓') ~ Γ

    map-Ctx' :
      ∀ {µ₁ µ₁' µ₂} →
      (f : ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m → drop-∈ x (µ₁' ▷▷ µ₂) ∶⊢ m→M m) →
      Ctx' µ₁ µ₂ →
      Ctx' µ₁' µ₂
    -- map-Ctx' :
    --   ∀ {µ₁ µ₁' µ₂} →
    --   (f : ∀ {m} → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m → µ₁' ▷▷ drop-∈ x µ₂ ∶⊢ m→M m) →
    --   Ctx' µ₁ µ₂ →
    --   Ctx' µ₁' µ₂

  Ctx : List VarMode → Set
  Ctx µ = Ctx' [] µ

  _▶▶'_ : ∀ {µ₁ µ₂ µ₃} → Ctx' µ₁ µ₂ → Ctx' (µ₁ ▷▷ µ₂) µ₃ → Ctx' µ₁ (µ₂ ▷▷ µ₃)
  _▶▶'_ {µ₁} {µ₂} {[]}     Γ₁ Γ₂ = Γ₁
  _▶▶'_ {µ₁} {µ₂} {µ₃ ▷ m} Γ₁ Γ₂ = (Γ₁ ▶▶' (Γ₂ ↓')) ▶' subst (_∶⊢ m→M m) (sym (++-assoc µ₃ µ₂ µ₁)) (lookup' Γ₂ (here refl))

  _▶_ : ∀ {µ m} → Ctx µ → µ ∶⊢ m→M m → Ctx (µ ▷ m)
  _▶_ {µ} {m} Γ t = Γ ▶' subst (_∶⊢ m→M m) (sym (++-identityʳ µ)) t

  _▶▶_ : ∀ {µ₁ µ₂} → Ctx µ₁ → Ctx' µ₁ µ₂ → Ctx (µ₁ ▷▷ µ₂)
  _▶▶_ {µ₁} {µ₂} Γ₁ Γ₂ = Γ₁ ▶▶' subst (λ ■ → Ctx' ■ µ₂) (sym (++-identityʳ µ₁)) Γ₂

  lookup'' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m
  lookup'' {µ₁} {µ₂} Γ {m} x = subst (_∶⊢ m→M m) (drop-∈-▷▷ x) (lookup' Γ x)

  lookup : ∀ {µ} → Ctx' [] µ → ∀ {m} → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m
  lookup {µ} Γ {m} x = subst (_∶⊢ m→M m) (++-identityʳ (drop-∈ x µ)) (lookup'' Γ x)

  -- lookup-wk : ∀ {µ} → Ctx' [] µ → ∀ {m} → (x : µ ∋ m) → µ ∶⊢ m→M m

module FunctionalCtx where
  Ctx' : List VarMode → List VarMode → Set
  Ctx' µ₁ µ₂ = ∀ m → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m

  _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)
  (Γ ▶' t) _ (here refl) = t
  (Γ ▶' t) _ (there x)   = Γ _ x

  lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m
  lookup' Γ x = Γ _ x

  _~_ : ∀ {µ₁ µ₂} → (Γ₁ Γ₂ : Ctx' µ₁ µ₂) → Set 
  Γ₁ ~ Γ₂ = ∀ m (x : _ ∋ m) → Γ₁ _ x ≡ Γ₂ _ x 

  _↓' : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
  Γ ↓' = λ m x → Γ m (there x)

  map-Ctx' :
    ∀ {µ₁ µ₁' µ₂} →
    (f : ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m → drop-∈ x (µ₁' ▷▷ µ₂) ∶⊢ m→M m) →
    Ctx' µ₁ µ₂ →
    Ctx' µ₁' µ₂
  map-Ctx' f Γ m x = f x (Γ m x)

  Functional-CtxRepr : CtxRepr
  Functional-CtxRepr = record
    { Ctx'            = Ctx'
    ; _▶'_            = _▶'_
    ; lookup'         = lookup'
    ; lookup-▶'-here  = λ Γ t → refl
    ; lookup-▶'-there = λ Γ t x → refl
    ; _~_             = _~_
    ; ~-lookup        = λ Γ₁~Γ₂ x → Γ₁~Γ₂ _ x
    ; _↓'             = _↓'
    ; ↓'-▶'           = λ Γ t m x → refl
    ; map-Ctx'        = map-Ctx'
    }

module ListCtx where
  data Ctx' : List VarMode → List VarMode → Set where
    []   : ∀ {µ₁} → Ctx' µ₁ []
    _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)

  lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m
  lookup' (Γ ▶' t) (here refl) = t
  lookup' (Γ ▶' t) (there x)   = lookup' Γ x

  _↓' : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
  (Γ ▶' t) ↓' = Γ

  map-Ctx' :
    ∀ {µ₁ µ₁' µ₂} →
    (f : ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m → drop-∈ x (µ₁' ▷▷ µ₂) ∶⊢ m→M m) →
    Ctx' µ₁ µ₂ →
    Ctx' µ₁' µ₂
  map-Ctx' f []       = []
  map-Ctx' f (Γ ▶' t) = map-Ctx' (λ x t' → f (there x) t') Γ ▶' f (here refl) t

  List-CtxRepr : CtxRepr
  List-CtxRepr = record
    { Ctx'            = Ctx'
    ; _▶'_            = _▶'_
    ; lookup'         = lookup'
    ; lookup-▶'-here  = λ Γ t → refl
    ; lookup-▶'-there = λ Γ t x → refl
    ; _~_             = _≡_
    ; ~-lookup        = λ { refl x → refl }
    ; _↓'             = _↓'
    ; ↓'-▶'           = λ Γ t → refl
    ; map-Ctx'        = map-Ctx'
    }
