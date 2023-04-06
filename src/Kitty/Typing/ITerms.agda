open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)

module Kitty.Typing.ITerms {𝕄 : Modes} {𝕋 : Terms 𝕄} {ℓ} {𝕊 : SubWithLaws 𝕋 ℓ} {T : Traversal 𝕋 𝕊} {H : KitHomotopy 𝕋 𝕊 T}
                           {𝕊C : SubCompose 𝕋 𝕊 T H} (C : ComposeTraversal 𝕋 𝕊 T H 𝕊C) (KT : KitType 𝕋) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude

open import Kitty.Term.Kit 𝕋
open Modes 𝕄
open Terms 𝕋
open Kitty.Typing.Types.KitType KT
open import Kitty.Typing.OPE C KT

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m

open Traversal T
open SubWithLaws 𝕊
open import Kitty.Term.Sub 𝕋
open Sub SubWithLaws-Sub
open Kit ⦃ … ⦄
private instance _ = kitᵣ; _ = kitₛ

_∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
_∋*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
  ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
  → Γ₂ ∋ (x & ϕ) ∶ t ⋯ ϕ

_~₁_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
        → (f g : (a : A) → B a) → Set (ℓ₁ ⊔ ℓ₂)
f ~₁ g = ∀ a → f a ≡ g a

_~₂_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
        → (f g : (a : A) → (b : B a) → C a b) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ~₂ g = ∀ a b → f a b ≡ g a b

~₂-refl : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
            {f : (a : A) → (b : B a) → C a b}
          → f ~₂ f
~₂-refl a b = refl

_~₂ᵢ_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
        → (f g : {a : A} → (b : B a) → C a b) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ~₂ᵢ g = ∀ a b → f {a} b ≡ g {a} b

record ITerms : Set₁ where
  infix   4  _⊢_∶_
  field
    _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set

    ⊢` : ∀ {Γ : Ctx µ} {x : µ ∋ m} {t} →
         Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

    ~₂-cong-⊢ : ∀ {µ M} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} → 
      (λ m → Γ₁ {m})  ~₂ (λ m → Γ₂ {m}) →
      Γ₁ ⊢ e ∶ t →
      Γ₂ ⊢ e ∶ t

  _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
  _⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
    ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
    → Γ₂ ⊢ (x & ϕ) ∶ t ⋯ ϕ
