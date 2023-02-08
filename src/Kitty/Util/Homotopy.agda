module Kitty.Util.Homotopy where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

infix 4 _~_

_~_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → (f g : (a : A) → (b : B a) → C a b)
  → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ~ g = ∀ a b → f a b ≡ g a b

~-refl :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f : (a : A) → (b : B a) → C a b}
  → f ~ f
~-refl a b = refl

~-sym :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f g : (a : A) → (b : B a) → C a b}
  → f ~ g
  → g ~ f
~-sym f~g a b = sym (f~g a b)

~-trans :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f g h : (a : A) → (b : B a) → C a b}
  → f ~ g
  → g ~ h
  → f ~ h
~-trans f~g g~h a b = trans (f~g a b) (g~h a b)

module ~-Reasoning where

  infix  3 _~∎
  infixr 2 _~⟨⟩_ step-~ step-~˘
  infix  1 begin~_

  private variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : A → Set ℓ₂
    C : (a : A) → B a → Set ℓ₃
    f g h : (a : A) → (b : B a) → C a b

  begin~_ : f ~ g → f ~ g
  begin~_ x≡y = x≡y

  _~⟨⟩_ :
    ∀ (f {g} : (a : A) → (b : B a) → C a b)
    → f ~ g → f ~ g
  _ ~⟨⟩ x~y = x~y

  step-~ :
    ∀ (f {g h} : (a : A) → (b : B a) → C a b)
    → g ~ h → f ~ g → f ~ h
  step-~ _ g~h f~g = ~-trans f~g g~h

  step-~˘ :
    ∀ (f {g h} : (a : A) → (b : B a) → C a b)
    → g ~ h → g ~ f → f ~ h
  step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

  _~∎ :
    ∀ (f : (a : A) → (b : B a) → C a b)
    → f ~ f
  _~∎ _ = ~-refl

  syntax step-~  f g~h f~g = f ~⟨  f~g ⟩ g~h
  syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h
