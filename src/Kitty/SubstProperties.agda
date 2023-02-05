module Kitty.SubstProperties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

dist-subst :
  ∀ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : A → Set ℓ₂}
  → (f : ∀ {a} → F a → G a)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G a₁≡a₂ (f {a₁} x)
dist-subst _ refl _ = refl

dist-subst₂ :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Set ℓ₁} {a₁ a₂ : A}
    {B : Set ℓ₂} {b₁ b₂ : B}
    {F : A → B → Set ℓ₃} {G : A → B → Set ℓ₄}
  → (f : ∀ {a} {b} → F a b → G a b)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁) 
  → f {a₂} {b₂} (subst₂ F a₁≡a₂ b₁≡b₂ x) ≡ subst₂ G a₁≡a₂ b₁≡b₂ (f {a₁} {b₁} x)
dist-subst₂ _ refl refl  _ = refl

comm-subst₂ :
  ∀ {ℓ₁ ℓ₂ ℓ₁' ℓ₂' ℓ₃}
    {A : Set ℓ₁} {a₁ a₂ : A}
    {B : Set ℓ₂} {b₁ b₂ : B}
    {A' : Set ℓ₁'}
    {B' : Set ℓ₂'}
    {F : A' → B' → Set ℓ₃}
  → (f : A → A')
  → (g : B → B')
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : b₁ ≡ b₂)
  → (x : F (f a₁) (g b₁)) 
  → subst₂ (λ a b → F (f a) (g b)) a₁≡a₂ b₁≡b₂ x ≡ subst₂ F (cong f a₁≡a₂) (cong g b₁≡b₂) x
comm-subst₂ f g refl refl x = refl

cancel-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F (sym a₁≡a₂) (subst F a₁≡a₂ x) ≡ x
cancel-subst _ refl _ = refl

cancel-subst₂ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F (sym a₁≡a₂) x) ≡ x
cancel-subst₂ _ refl _ = refl
