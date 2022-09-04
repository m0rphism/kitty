open import KitTheory.Modes
open import KitTheory.Kit using (KitTraversal)

module KitTheory.ComposeCat {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import KitTheory.Prelude

open Modes 𝕄
open Terms 𝕋
open KitTheory.Kit 𝕋
open KitTheory.Kit.KitTraversal T

open Kit {{...}} hiding (_–→_)

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

postulate
  ⋯-id : ∀ {{𝕂 : Kit}} (t : µ ⊢ M) → t ⋯ idₖ ≡ t

private instance _ = kitᵣ
private instance _ = kitₛ

-- Renamings and Substitutions (and their typings) form categories.
-- There's a faithful (injective) functor from renamings to substitutions.
-- Unit is isomorphic to every µ with exactly one mode.
-- Variables and terms are represented as arrows with domain unit (yoneda), which also captures ⋯ as by simple composition.
-- Void is the empty list.
-- Do we have Products? Probably only if the terms / variables have products.
-- All of the above categories are subcategories of the Set categories.

record Category (Obj : Set) : Set₁ where
  field
    Arr     : Obj → Obj → Set
    _∘_     : ∀ {A B C} → Arr B C → Arr A B → Arr A C
    id      : ∀ {A} → Arr A A
    ∘-idₗ   : ∀ {A B} (f : Arr A B) → f ∘ id ≡ f
    ∘-idᵣ   : ∀ {A B} (f : Arr A B) → id ∘ f ≡ f
    ∘-assoc : ∀ {A B C D} (f : Arr C D) (g : Arr B C) (h : Arr A B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  _–→_ : Obj → Obj → Set
  _–→_ = Arr

open Category {{...}}

_–⟨_⟩→_ : ∀ {Obj} → Obj → Category Obj → Obj → Set
A –⟨ ℂ ⟩→ B = Category.Arr ℂ A B

catᵣ : Category (List VarMode)
Category.Arr     catᵣ = _→ᵣ_
Category._∘_     catᵣ = _ᵣ∘ᵣ_
Category.id      catᵣ = idᵣ
Category.∘-idₗ   catᵣ f = refl
Category.∘-idᵣ   catᵣ f = refl
Category.∘-assoc catᵣ f g h = refl

private instance _ = catᵣ

record Faithful {Obj-ℂ Obj-𝔻} (ℂ : Category Obj-ℂ) (𝔻 : Category Obj-𝔻) : Set₁ where
  module ℂ = Category ℂ
  module 𝔻 = Category 𝔻
  field
    Map : Obj-ℂ → Obj-𝔻
    map : ∀ {A B} → A –⟨ ℂ ⟩→ B → Map A –⟨ 𝔻 ⟩→ Map B
    map-hom : ∀ {A B C} (f : B –⟨ ℂ ⟩→ C) (g : A –⟨ ℂ ⟩→ B) → map (f ℂ.∘ g) ≡ map f 𝔻.∘ map g
    map-inj : ∀ {A B} (f g : A –⟨ ℂ ⟩→ B) → map f ≡ map g → f ≡ g

open Faithful {{...}}

postulate
  `-inj : ∀ {x y : µ ∋ m} → ` x ≡ ` y → x ≡ y

lem : ∀ {µ₁ µ₂} {f g : ∀ m → µ₁ ∋ m → µ₂ ⊢ m→M m} {m} {x : µ₁ ∋ m} → f ≡ g → f m x ≡ g m x
lem refl = refl

mutual
  catₛ : Category (List VarMode)
  Category.Arr     catₛ = _→ₛ_
  Category._∘_     catₛ = _ₛ∘ₛ_
  Category.id      catₛ = idₛ
  Category.∘-idₗ   catₛ f = fun-ext₂ λ _ x → ⋯-var x f
  Category.∘-idᵣ   catₛ f = fun-ext₂ λ _ x → ⋯-id (f _ x)
  Category.∘-assoc catₛ f g h = {!!} -- ⋯-assoc

  -- private instance _ = catₛ

  Fᵣₛ : Faithful catᵣ catₛ
  Faithful.Map     Fᵣₛ = λ µ → µ
  Faithful.map     Fᵣₛ = λ f _ x →  ` f _ x
  Faithful.map-hom Fᵣₛ f g = fun-ext₂ λ _ x → sym (⋯-var (g _ x) λ _ x → ` f _ x)
  Faithful.map-inj Fᵣₛ f g p = fun-ext₂ λ _ _ → `-inj (lem p)
