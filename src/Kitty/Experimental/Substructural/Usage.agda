-- Usage policies are instances of two important structures:
--
-- - They form a semiring where u = u₁ + u₂ describes how a resource with usage
--   policy u can be split into two parts.
--
-- - They form a bounded lattice where u₁ ⊑ u₂ describes that u₂ can also be
--   used like u₁. This is required for polymorphism with usage constraints.
--
-- Any semiring or lattice can be lifted pointwise over dependent function
-- types. If we take functions from variables to usage, then we get notions for
-- usage environments.
--
-- - ρ = ρ₁ + ρ₂ describes that ρ can be split into ρ₁ and ρ₂
--
-- - ρ ⊑ const u describes that ρ has to use every variable at least according
--   to u, which can be used to describe that unrestricted lambdas are only
--   allowed to capture unrestricted variables.
--
-- This module provides type classes for semirings and lattices, and instances
-- which automatically lift other instances over dependent function types.
--
-- Fun fact: Agda comes with a semiring solver, so this framework is already
-- quite powerful.
--
-- Fun fact: Implementing those structures is trivial for finite usages, because
-- you can prove all lemmas automatically with case-split-auto.

-- TODO: For completeness, we could also define lifting over lists and indexed
-- lists to account for locally nameless representations or environments of
-- lists of usages (whatever purpose this might serve).

module Kitty.Experimental.Substructural.Usage where

open import Level using (Level) renaming (suc to lsuc)
open import Data.Product using (∃-syntax; _×_; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Axiom.Extensionality.Propositional using (Extensionality)

private variable ℓ ℓ₁ ℓ₂ : Level

-- Distributive Bounded Lattice
record Lattice (A : Set ℓ) : Set ℓ where
  infix  6  _⊑_  _⊑'_  _⊒_  _⊒'_
  infixl 7  _⊔_
  infixl 8  _⊓_
  field
    `⊥ `⊤     : A
    _⊔_ _⊓_   : A → A → A
    ⊔-idˡ     : ∀ x → `⊥ ⊔ x ≡ x
    ⊓-idˡ     : ∀ x → `⊤ ⊓ x ≡ x
    ⊔-comm    : ∀ x y → x ⊔ y ≡ y ⊔ x
    ⊓-comm    : ∀ x y → x ⊓ y ≡ y ⊓ x
    ⊔-assoc   : ∀ x y z → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)
    ⊓-assoc   : ∀ x y z → (x ⊓ y) ⊓ z ≡ x ⊓ (y ⊓ z)
    ⊔-absorb  : ∀ x y → x ⊔ (x ⊓ y) ≡ x
    ⊓-absorb  : ∀ x y → x ⊓ (x ⊔ y) ≡ x
    ⊓-distˡ-⊔ : ∀ x y z → x ⊓ (y ⊔ z) ≡ (x ⊓ y) ⊔ (x ⊓ z)

  ⊔-idʳ : ∀ x → x ⊔ `⊥ ≡ x
  ⊓-idʳ : ∀ x → x ⊓ `⊤ ≡ x
  ⊔-idʳ x = trans (⊔-comm x `⊥) (⊔-idˡ x)
  ⊓-idʳ x = trans (⊓-comm x `⊤) (⊓-idˡ x)

  ⊓-distʳ-⊔ : ∀ x y z → (x ⊔ y) ⊓ z ≡ (x ⊓ z) ⊔ (y ⊓ z)
  ⊓-distʳ-⊔ x y z =
    (x ⊔ y) ⊓ z       ≡⟨ ⊓-comm (x ⊔ y) z ⟩
    z ⊓ (x ⊔ y)       ≡⟨ ⊓-distˡ-⊔ z x y ⟩
    (z ⊓ x) ⊔ (z ⊓ y) ≡⟨ cong₂ _⊔_ (⊓-comm z x) (⊓-comm z y) ⟩
    (x ⊓ z) ⊔ (y ⊓ z) ∎

  ⊔-idem : ∀ x → x ⊔ x ≡ x
  ⊓-idem : ∀ x → x ⊓ x ≡ x
  ⊔-idem x =
    x ⊔ x         ≡⟨ cong (x ⊔_) (sym (⊓-idʳ x)) ⟩
    x ⊔ (x ⊓ `⊤)  ≡⟨ ⊔-absorb x `⊤ ⟩
    x             ∎
  ⊓-idem x =
    x ⊓ x         ≡⟨ cong (x ⊓_) (sym (⊔-idʳ x)) ⟩
    x ⊓ (x ⊔ `⊥)  ≡⟨ ⊓-absorb x `⊥ ⟩
    x             ∎

  _⊑_ _⊑'_ _⊒_ _⊒'_ : A → A → Set ℓ
  x ⊑  y = ∃[ z ] (x ⊔ z ≡ y)
  x ⊑' y = ∃[ z ] (y ⊓ z ≡ x)
  x ⊒  y = y ⊑  x
  x ⊒' y = y ⊑' x

  -- We could also define  x ⊑ y  as  x ⊔ y ≡ y  or  x ⊓ y ≡ x.
  -- This would make it easier to use but harder prove x ⊑ y.
  -- The below lemmas intermediate between the two representations.
  ⊑-weaken-⊔ : ∀ {x y} → x ⊑ y → x ⊔ y ≡ y
  ⊑-weaken-⊓ : ∀ {x y} → x ⊑ y → x ⊓ y ≡ x
  ⊑-weaken-⊔ {x} {_} (z , refl) =
    x ⊔ (x ⊔ z) ≡⟨ sym (⊔-assoc x x z) ⟩
    (x ⊔ x) ⊔ z ≡⟨ cong (_⊔ z) (⊔-idem x) ⟩
    x ⊔ z       ∎
  ⊑-weaken-⊓ {x} {_} (z , refl) = ⊓-absorb x z

  ⊑→⊑' : ∀ {x y} → x ⊑  y → x ⊑' y
  ⊑'→⊑ : ∀ {x y} → x ⊑' y → x ⊑  y
  ⊑→⊑' {x} {_} (z , refl) = x , trans (⊓-comm (x ⊔ z) x) (⊓-absorb x z)
  ⊑'→⊑ {_} {y} (z , refl) = y , trans (⊔-comm (y ⊓ z) y) (⊔-absorb y z)

  ⊑-refl  : ∀ {x} → x ⊑  x
  ⊑'-refl : ∀ {x} → x ⊑' x
  ⊑-refl  {x} = x , ⊔-idem x
  ⊑'-refl {x} = x , ⊓-idem x

  ⊑-trans  : ∀ {x y z} → x ⊑  y → y ⊑  z → x ⊑  z
  ⊑'-trans : ∀ {x y z} → x ⊑' y → y ⊑' z → x ⊑' z
  ⊑-trans  (z₁ , refl) (z₂ , refl) = (z₁ ⊔ z₂) , sym (⊔-assoc _ z₁ z₂)
  ⊑'-trans (z₁ , refl) (z₂ , refl) = (z₂ ⊓ z₁) , sym (⊓-assoc _ z₂ z₁)

  ⊑-anti-sym  : ∀ {x y} → x ⊑  y → y ⊑  x → x ≡ y
  ⊑'-anti-sym : ∀ {x y} → x ⊑' y → y ⊑' x → x ≡ y
  ⊑-anti-sym {x} {_} (z₁ , refl) (z₂ , q) rewrite (sym q) =
    (x ⊔ z₁) ⊔ z₂        ≡⟨ cong (λ ● → (x ⊔ ●) ⊔ z₂) (sym (⊔-idem z₁)) ⟩
    (x ⊔ (z₁ ⊔ z₁)) ⊔ z₂ ≡⟨ cong (_⊔ z₂) (sym (⊔-assoc x z₁ z₁)) ⟩
    ((x ⊔ z₁) ⊔ z₁) ⊔ z₂ ≡⟨ ⊔-assoc (x ⊔ z₁) z₁ z₂ ⟩
    (x ⊔ z₁) ⊔ (z₁ ⊔ z₂) ≡⟨ cong ((x ⊔ z₁) ⊔_) (⊔-comm z₁ z₂) ⟩
    (x ⊔ z₁) ⊔ (z₂ ⊔ z₁) ≡⟨ sym (⊔-assoc (x ⊔ z₁) z₂ z₁) ⟩
    ((x ⊔ z₁) ⊔ z₂) ⊔ z₁ ∎
  ⊑'-anti-sym p q = ⊑-anti-sym (⊑'→⊑ p) (⊑'→⊑ q)

  -- TODO
  ⊔-lub₁ : ∀ x y → x ⊑ x ⊔ y
  ⊔-lub₁ x y = y , refl

record Semiring (A : Set ℓ) : Set (lsuc ℓ) where
  infixl 7 _+_
  infixl 8 _*_
  field
    `0        : A
    `1        : A
    _+_       : A → A → A
    _*_       : A → A → A
    +-assoc   : ∀ x y z → (x + y) + z ≡ x + (y + z)
    *-assoc   : ∀ x y z → (x * y) * z ≡ x * (y * z)
    +-idˡ     : ∀ x → `0 + x ≡ x
    *-idˡ     : ∀ x → `1 * x ≡ x
    *-idʳ     : ∀ x → x * `1 ≡ x
    +-comm    : ∀ x y → x + y ≡ y + x
    *-zeroˡ   : ∀ x → `0 * x ≡ `0
    *-zeroʳ   : ∀ x → x * `0 ≡ `0
    +-distˡ-* : ∀ x y z → x * (y + z) ≡ x * y + x * z
    +-distʳ-* : ∀ x y z → (x + y) * z ≡ x * z + y * z

  +-idʳ : ∀ x → x + `0 ≡ x
  +-idʳ x = trans (+-comm x `0) (+-idˡ x)

data Usage : Set where
  [∞] : Usage  -- Unrestricted
  [1] : Usage  -- Linear
  [0] : Usage  -- Forbidden

Lattice-Usage : Lattice Usage
Lattice-Usage = record
  { `⊥        = `⊥
  ; `⊤        = `⊤
  ; _⊔_       = _⊔_
  ; _⊓_       = _⊓_
  ; ⊔-idˡ     = ⊔-idˡ
  ; ⊓-idˡ     = ⊓-idˡ
  ; ⊔-comm    = ⊔-comm
  ; ⊓-comm    = ⊓-comm
  ; ⊔-assoc   = ⊔-assoc
  ; ⊓-assoc   = ⊓-assoc
  ; ⊔-absorb  = ⊔-absorb
  ; ⊓-absorb  = ⊓-absorb
  ; ⊓-distˡ-⊔ = ⊓-distˡ-⊔
  } where

    `⊥ `⊤ : Usage
    `⊥ = [0]
    `⊤ = [∞]

    _⊔_ : Usage → Usage → Usage
    [∞] ⊔ y   = [∞]
    x   ⊔ [∞] = [∞]
    [1] ⊔ y   = [1]
    x   ⊔ [1] = [1]
    [0] ⊔ [0] = [0]

    _⊓_ : Usage → Usage → Usage
    [0] ⊓ y   = [0]
    x   ⊓ [0] = [0]
    [1] ⊓ y   = [1]
    x   ⊓ [1] = [1]
    [∞] ⊓ [∞] = [∞]

    ⊔-idˡ : ∀ x → `⊥ ⊔ x ≡ x
    ⊔-idˡ [∞] = refl
    ⊔-idˡ [1] = refl
    ⊔-idˡ [0] = refl

    ⊓-idˡ : ∀ x → `⊤ ⊓ x ≡ x
    ⊓-idˡ [∞] = refl
    ⊓-idˡ [1] = refl
    ⊓-idˡ [0] = refl

    ⊔-comm : ∀ x y → x ⊔ y ≡ y ⊔ x
    ⊔-comm [∞] [∞] = refl
    ⊔-comm [∞] [1] = refl
    ⊔-comm [∞] [0] = refl
    ⊔-comm [1] [∞] = refl
    ⊔-comm [1] [1] = refl
    ⊔-comm [1] [0] = refl
    ⊔-comm [0] [∞] = refl
    ⊔-comm [0] [1] = refl
    ⊔-comm [0] [0] = refl

    ⊓-comm : ∀ x y → x ⊓ y ≡ y ⊓ x
    ⊓-comm [∞] [∞] = refl
    ⊓-comm [∞] [1] = refl
    ⊓-comm [∞] [0] = refl
    ⊓-comm [1] [∞] = refl
    ⊓-comm [1] [1] = refl
    ⊓-comm [1] [0] = refl
    ⊓-comm [0] [∞] = refl
    ⊓-comm [0] [1] = refl
    ⊓-comm [0] [0] = refl

    ⊔-assoc : ∀ x y z → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)
    ⊔-assoc [∞] y z = refl
    ⊔-assoc [1] [∞] z = refl
    ⊔-assoc [1] [1] [∞] = refl
    ⊔-assoc [1] [1] [1] = refl
    ⊔-assoc [1] [1] [0] = refl
    ⊔-assoc [1] [0] [∞] = refl
    ⊔-assoc [1] [0] [1] = refl
    ⊔-assoc [1] [0] [0] = refl
    ⊔-assoc [0] [∞] z = refl
    ⊔-assoc [0] [1] [∞] = refl
    ⊔-assoc [0] [1] [1] = refl
    ⊔-assoc [0] [1] [0] = refl
    ⊔-assoc [0] [0] [∞] = refl
    ⊔-assoc [0] [0] [1] = refl
    ⊔-assoc [0] [0] [0] = refl

    ⊓-assoc : ∀ x y z → (x ⊓ y) ⊓ z ≡ x ⊓ (y ⊓ z)
    ⊓-assoc [∞] [∞] [∞] = refl
    ⊓-assoc [∞] [∞] [1] = refl
    ⊓-assoc [∞] [∞] [0] = refl
    ⊓-assoc [∞] [1] [∞] = refl
    ⊓-assoc [∞] [1] [1] = refl
    ⊓-assoc [∞] [1] [0] = refl
    ⊓-assoc [∞] [0] z = refl
    ⊓-assoc [1] [∞] [∞] = refl
    ⊓-assoc [1] [∞] [1] = refl
    ⊓-assoc [1] [∞] [0] = refl
    ⊓-assoc [1] [1] [∞] = refl
    ⊓-assoc [1] [1] [1] = refl
    ⊓-assoc [1] [1] [0] = refl
    ⊓-assoc [1] [0] z = refl
    ⊓-assoc [0] y z = refl

    ⊔-absorb : ∀ x y → x ⊔ (x ⊓ y) ≡ x
    ⊔-absorb [∞] y = refl
    ⊔-absorb [1] [∞] = refl
    ⊔-absorb [1] [1] = refl
    ⊔-absorb [1] [0] = refl
    ⊔-absorb [0] y = refl

    ⊓-absorb : ∀ x y → x ⊓ (x ⊔ y) ≡ x
    ⊓-absorb [∞] y = refl
    ⊓-absorb [1] [∞] = refl
    ⊓-absorb [1] [1] = refl
    ⊓-absorb [1] [0] = refl
    ⊓-absorb [0] y = refl

    ⊓-distˡ-⊔ : ∀ x y z → x ⊓ (y ⊔ z) ≡ (x ⊓ y) ⊔ (x ⊓ z)
    ⊓-distˡ-⊔ [∞] [∞] z = refl
    ⊓-distˡ-⊔ [∞] [1] [∞] = refl
    ⊓-distˡ-⊔ [∞] [1] [1] = refl
    ⊓-distˡ-⊔ [∞] [1] [0] = refl
    ⊓-distˡ-⊔ [∞] [0] [∞] = refl
    ⊓-distˡ-⊔ [∞] [0] [1] = refl
    ⊓-distˡ-⊔ [∞] [0] [0] = refl
    ⊓-distˡ-⊔ [1] [∞] [∞] = refl
    ⊓-distˡ-⊔ [1] [∞] [1] = refl
    ⊓-distˡ-⊔ [1] [∞] [0] = refl
    ⊓-distˡ-⊔ [1] [1] [∞] = refl
    ⊓-distˡ-⊔ [1] [1] [1] = refl
    ⊓-distˡ-⊔ [1] [1] [0] = refl
    ⊓-distˡ-⊔ [1] [0] [∞] = refl
    ⊓-distˡ-⊔ [1] [0] [1] = refl
    ⊓-distˡ-⊔ [1] [0] [0] = refl
    ⊓-distˡ-⊔ [0] y z = refl

Semiring-Usage : Semiring Usage
Semiring-Usage = record
  { `0        =  [0]
  ; `1        =  [1]
  ; _+_       =  _+_
  ; _*_       =  _*_
  ; +-assoc   =  +-assoc
  ; *-assoc   =  *-assoc
  ; +-idˡ     =  +-idˡ
  ; *-idˡ     =  *-idˡ
  ; *-idʳ     =  *-idʳ
  ; +-comm    =  +-comm
  ; *-zeroˡ   =  *-zeroˡ
  ; *-zeroʳ   =  *-zeroʳ
  ; +-distˡ-* =  +-distˡ-*
  ; +-distʳ-* =  +-distʳ-*
  } where

    infix 7 _+_
    infix 8 _*_

    _+_ : Usage → Usage → Usage
    [∞] + y   = [∞]
    x   + [∞] = [∞]
    [1] + [1] = [∞]
    [1] + [0] = [1]
    [0] + [1] = [1]
    [0] + [0] = [0]

    _*_ : Usage → Usage → Usage
    [∞] * [∞] = [∞]
    [0] * y   = [0]
    x   * [0] = [0]
    [1] * y   = y
    x   * [1] = x

    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-assoc [∞] y z = refl
    +-assoc [1] [∞] z = refl
    +-assoc [1] [1] [∞] = refl
    +-assoc [1] [1] [1] = refl
    +-assoc [1] [1] [0] = refl
    +-assoc [1] [0] [∞] = refl
    +-assoc [1] [0] [1] = refl
    +-assoc [1] [0] [0] = refl
    +-assoc [0] [∞] z = refl
    +-assoc [0] [1] [∞] = refl
    +-assoc [0] [1] [1] = refl
    +-assoc [0] [1] [0] = refl
    +-assoc [0] [0] [∞] = refl
    +-assoc [0] [0] [1] = refl
    +-assoc [0] [0] [0] = refl

    *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-assoc [∞] [∞] [∞] = refl
    *-assoc [∞] [∞] [1] = refl
    *-assoc [∞] [∞] [0] = refl
    *-assoc [∞] [1] [∞] = refl
    *-assoc [∞] [1] [1] = refl
    *-assoc [∞] [1] [0] = refl
    *-assoc [∞] [0] z = refl
    *-assoc [1] [∞] [∞] = refl
    *-assoc [1] [∞] [1] = refl
    *-assoc [1] [∞] [0] = refl
    *-assoc [1] [1] [∞] = refl
    *-assoc [1] [1] [1] = refl
    *-assoc [1] [1] [0] = refl
    *-assoc [1] [0] z = refl
    *-assoc [0] y z = refl

    +-idˡ : ∀ x → [0] + x ≡ x
    +-idˡ [∞] = refl
    +-idˡ [1] = refl
    +-idˡ [0] = refl

    *-idˡ : ∀ x → [1] * x ≡ x
    *-idˡ [∞] = refl
    *-idˡ [1] = refl
    *-idˡ [0] = refl

    *-idʳ : ∀ x → x * [1] ≡ x
    *-idʳ [∞] = refl
    *-idʳ [1] = refl
    *-idʳ [0] = refl

    +-comm : ∀ x y → x + y ≡ y + x
    +-comm [∞] [∞] = refl
    +-comm [∞] [1] = refl
    +-comm [∞] [0] = refl
    +-comm [1] [∞] = refl
    +-comm [1] [1] = refl
    +-comm [1] [0] = refl
    +-comm [0] [∞] = refl
    +-comm [0] [1] = refl
    +-comm [0] [0] = refl

    *-zeroˡ : ∀ x → [0] * x ≡ [0]
    *-zeroˡ _ = refl

    *-zeroʳ : ∀ x → x * [0] ≡ [0]
    *-zeroʳ [∞] = refl
    *-zeroʳ [1] = refl
    *-zeroʳ [0] = refl

    +-distˡ-* : ∀ x y z → x * (y + z) ≡ x * y + x * z
    +-distˡ-* [∞] [∞] z = refl
    +-distˡ-* [∞] [1] [∞] = refl
    +-distˡ-* [∞] [1] [1] = refl
    +-distˡ-* [∞] [1] [0] = refl
    +-distˡ-* [∞] [0] [∞] = refl
    +-distˡ-* [∞] [0] [1] = refl
    +-distˡ-* [∞] [0] [0] = refl
    +-distˡ-* [1] [∞] z = refl
    +-distˡ-* [1] [1] [∞] = refl
    +-distˡ-* [1] [1] [1] = refl
    +-distˡ-* [1] [1] [0] = refl
    +-distˡ-* [1] [0] [∞] = refl
    +-distˡ-* [1] [0] [1] = refl
    +-distˡ-* [1] [0] [0] = refl
    +-distˡ-* [0] y z = refl

    +-distʳ-* : ∀ x y z → (x + y) * z ≡ x * z + y * z
    +-distʳ-* [∞] y [∞] = refl
    +-distʳ-* [∞] y [1] = refl
    +-distʳ-* [∞] [∞] [0] = refl
    +-distʳ-* [∞] [1] [0] = refl
    +-distʳ-* [∞] [0] [0] = refl
    +-distʳ-* [1] [∞] [∞] = refl
    +-distʳ-* [1] [∞] [1] = refl
    +-distʳ-* [1] [∞] [0] = refl
    +-distʳ-* [1] [1] [∞] = refl
    +-distʳ-* [1] [1] [1] = refl
    +-distʳ-* [1] [1] [0] = refl
    +-distʳ-* [1] [0] [∞] = refl
    +-distʳ-* [1] [0] [1] = refl
    +-distʳ-* [1] [0] [0] = refl
    +-distʳ-* [0] [∞] [∞] = refl
    +-distʳ-* [0] [∞] [1] = refl
    +-distʳ-* [0] [∞] [0] = refl
    +-distʳ-* [0] [1] [∞] = refl
    +-distʳ-* [0] [1] [1] = refl
    +-distʳ-* [0] [1] [0] = refl
    +-distʳ-* [0] [0] z = refl

module Instances-∀ (fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where
  Semiring-∀ : {A : Set ℓ₁} {B : A → Set ℓ₂} {{_ : ∀ {x : A} → Semiring (B x)}} → Semiring (∀ (x : A) → B x)
  Semiring-∀ = record
    { `0        =           λ _ → `0
    ; `1        =           λ _ → `1
    ; _+_       = λ f g   → λ x → f x + g x
    ; _*_       = λ f g   → λ x → f x * g x
    ; +-assoc   = λ f g h → fun-ext (λ x → +-assoc (f x) (g x) (h x))
    ; *-assoc   = λ f g h → fun-ext (λ x → *-assoc (f x) (g x) (h x))
    ; +-idˡ     = λ f     → fun-ext (λ x → +-idˡ (f x))
    ; *-idˡ     = λ f     → fun-ext (λ x → *-idˡ (f x))
    ; *-idʳ     = λ f     → fun-ext (λ x → *-idʳ (f x))
    ; +-comm    = λ f g   → fun-ext (λ x → +-comm (f x) (g x))
    ; *-zeroˡ   = λ f     → fun-ext (λ x → *-zeroˡ (f x))
    ; *-zeroʳ   = λ f     → fun-ext (λ x → *-zeroʳ (f x))
    ; +-distˡ-* = λ f g h → fun-ext (λ x → +-distˡ-* (f x) (g x) (h x))
    ; +-distʳ-* = λ f g h → fun-ext (λ x → +-distʳ-* (f x) (g x) (h x))
    }
    where open Semiring {{...}}

  Lattice-∀ : {A : Set ℓ₁} {B : A → Set ℓ₂} {{_ : ∀ {x : A} → Lattice (B x)}} → Lattice (∀ (x : A) → B x)
  Lattice-∀ = record
    { `⊥        =           λ _ → `⊥
    ; `⊤        =           λ _ → `⊤
    ; _⊔_       = λ f g   → λ x → f x ⊔ g x
    ; _⊓_       = λ f g   → λ x → f x ⊓ g x
    ; ⊔-idˡ     = λ f     → fun-ext (λ x → ⊔-idˡ (f x))
    ; ⊓-idˡ     = λ f     → fun-ext (λ x → ⊓-idˡ (f x))
    ; ⊔-comm    = λ f g   → fun-ext (λ x → ⊔-comm (f x) (g x))
    ; ⊓-comm    = λ f g   → fun-ext (λ x → ⊓-comm (f x) (g x))
    ; ⊔-assoc   = λ f g h → fun-ext (λ x → ⊔-assoc (f x) (g x) (h x))
    ; ⊓-assoc   = λ f g h → fun-ext (λ x → ⊓-assoc (f x) (g x) (h x))
    ; ⊔-absorb  = λ f g   → fun-ext (λ x → ⊔-absorb (f x) (g x))
    ; ⊓-absorb  = λ f g   → fun-ext (λ x → ⊓-absorb (f x) (g x))
    ; ⊓-distˡ-⊔ = λ f g h → fun-ext (λ x → ⊓-distˡ-⊔ (f x) (g x) (h x))
    }
    where open Lattice {{...}}

module Example where
  open import Data.List using (List; []; _∷_)
  open import Data.List.Membership.Propositional using (_∈_)

  open Semiring {{...}}
  open Lattice {{...}}

  postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  open Instances-∀ fun-ext using (Semiring-∀; Lattice-∀)

  private
    instance
      _ = Semiring-Usage
      _ = Semiring-∀
      _ = Lattice-Usage
      _ = Lattice-∀

  data Kind : Set where
    ★ : Kind

  Env : List Kind → Set
  Env ks = ∀ k → k ∈ ks → Usage

  ⟦0⟧ ⟦1⟧ ⟦∞⟧ : ∀ {ks} → Env ks
  -- ⟦0⟧ _ _ = [0]
  -- ⟦1⟧ _ _ = [1]
  -- ⟦∞⟧ _ _ = [∞]
  ⟦0⟧ = `0
  ⟦1⟧ = `1
  ⟦∞⟧ = `⊤

  foo : [0] + [0] ≡ [0]
  foo = refl

  bar : ∀ {ks} → ⟦0⟧ + ⟦0⟧ ≡ ⟦0⟧ {ks}
  bar = refl

  baz : [0] ⊔ [1] ≡ [1]
  baz = refl

  boo : ∀ {ks} → ⟦0⟧ ⊔ ⟦1⟧ ≡ ⟦1⟧ {ks}
  boo = refl
