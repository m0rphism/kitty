module Kitty.Util.SubstProperties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

subst-irrelevant : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq eq' : a₁ ≡ a₂)
    (x : F a₁) 
  → subst F eq x ≡ subst F eq' x
subst-irrelevant refl refl x = refl

subst-sym : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq : a₁ ≡ a₂)
    (x : F a₁) 
    (y : F a₂) 
  → x ≡ subst F (sym eq) y
  → subst F eq x ≡ y
subst-sym refl x y eq = eq

subst-sym' : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq : a₁ ≡ a₂)
    (x : F a₂) 
    (y : F a₁) 
  → x ≡ subst F eq y
  → subst F (sym eq) x ≡ y
subst-sym' refl x y eq = eq

dist-subst :
  ∀ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : A → Set ℓ₂}
  → (f : ∀ {a} → F a → G a)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G a₁≡a₂ (f {a₁} x)
dist-subst _ refl _ = refl

dist-subst-arg :
  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : A → Set ℓ₂} {H : Set ℓ₃}
  → (f : ∀ {a} → (x : F a) → G a → H)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (x : F a₁) 
  → (y : G a₂) 
  → f (subst F a₁≡a₂ x) y ≡ f x (subst G a₂≡a₁ y)
dist-subst-arg _ refl refl _ _ = refl

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

dist-subst' :
  ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : A → B)
  → (f : ∀ {a} → F a → G (a→b a))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst' _ _ refl refl _ = refl

dist-subst₂' :
  ∀ {ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {D : Set ℓ'''} {a₁ a₂ : A} {c₁ c₂ : C}
    {F : A → C → Set ℓ₁} {G : B → D → Set ℓ₂}
  → (a→b : A → B)
  → (c→d : C → D)
  → (f : ∀ {a} {c} → F a c → G (a→b a) (c→d c))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (c₁≡c₂ : c₁ ≡ c₂)
  → (d₁≡d₂ : c→d c₁ ≡ c→d c₂)
  → (x : F a₁ c₁) 
  → f {a₂} {c₂} (subst₂ F a₁≡a₂ c₁≡c₂ x) ≡ subst₂ G b₁≡b₂ d₁≡d₂ (f {a₁} {c₁} x)
dist-subst₂' _ _ _ refl refl refl refl _ = refl

comm-subst :
  ∀ {ℓ₁ ℓ₁' ℓ₃}
    {A : Set ℓ₁} {a₁ a₂ : A}
    {A' : Set ℓ₁'}
    {F : A' → Set ℓ₃}
  → (f : A → A')
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F (f a₁)) 
  → subst (λ a → F (f a)) a₁≡a₂ x ≡ subst F (cong f a₁≡a₂) x
comm-subst f refl x = refl

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

cancel-subst' :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F (sym a₂≡a₁) x) ≡ x
cancel-subst' _ refl _ = refl

cancel-subst₂ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F (sym a₁≡a₂) x) ≡ x
cancel-subst₂ _ refl _ = refl

-- TODO: Should replace all cancel-subst
elim-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F a₁≡a₂ x) ≡ x
elim-subst _ refl refl _ = refl

elim-subst₃ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ : A}
  → (F : A → Set ℓ₁)
  → (a₃≡a₁ : a₃ ≡ a₁)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₃≡a₁ (subst F a₂≡a₃ (subst F a₁≡a₂ x)) ≡ x
elim-subst₃ _ refl refl refl _ = refl

subst-merge :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (x : F a₁)
  → subst F a₂≡a₃ (subst F a₁≡a₂ x) ≡ subst F (trans a₁≡a₂ a₂≡a₃) x
subst-merge F refl refl x = refl

subst₂₁ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Set ℓ₁} {a₁ a₂ : A}
    {B : Set ℓ₂} {b₁ b₂ : B}
  → (F : A → B → Set ℓ₃)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁) 
  → subst₂ F a₁≡a₂ b₁≡b₂ x ≡ subst (F a₂) b₁≡b₂ (subst (λ a → F a b₁) a₁≡a₂ x)
subst₂₁ _ refl refl _ = refl

subst₁₂ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Set ℓ₁} {a₁ a₂ : A}
    {B : Set ℓ₂} {b₁ b₂ : B}
  → (F : A → B → Set ℓ₃)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁) 
  → subst₂ F a₁≡a₂ b₁≡b₂ x ≡ subst (λ a → F a b₂) a₁≡a₂ (subst (F a₁) b₁≡b₂ x)
subst₁₂ _ refl refl _ = refl
