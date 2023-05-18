{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive.MultiTraversalTest where

open import Kitty.Derive.MultiTraversal
import Kitty.Term.MultiTraversalDerived as Derived

module Example where
  open import Kitty.Term.Prelude
  open import Kitty.Term.Modes
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open ≡-Reasoning
  open import ReflectionLib.Categorical

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  open Modes 𝕄 using (Scoped)

  infix  30 `_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `_    : ∀ {µ m}  →  µ ∋ m  →  µ ⊢ m→M m
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  module Manual where
    terms : Terms 𝕄
    terms = record { _⊢_ = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }

    open import Kitty.Term.Sub terms
    open import Kitty.Term.MultiSub terms
    open import Kitty.Term.MultiTraversal terms
    open import Kitty.Term.Kit terms
    open import Kitty.Util.Star
    open Kit ⦃ ... ⦄
    open Sub ⦃ ... ⦄
    open SubWithLaws ⦃ ... ⦄

    _⋯_ : ∀ {ℓ} {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ 𝕊 : Sub ℓ ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    (` x)     ⋯ f = `/id (x & f)
    (λx t)    ⋯ f = λx (t ⋯ (f ↑*' _))
    (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
    (foo t)   ⋯ f = foo (t ⋯ (f ↑*' _))

    ⋯-var : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var x f = refl

    open TraversalOps _⋯_

    ⋯-↑-· : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t₁ t₂ : (µ₁ ▷▷ µ₁') ⊢ 𝕖)
            → ((t₁ · t₂) ⋯* (f ↑** µ₁')) ≡ (t₁ ⋯* (f ↑** µ₁' ↑** [])) · (t₂ ⋯* (f ↑** µ₁' ↑** []))
    ⋯-↑-· {ℓ} {.[]}     []       t₁ t₂ = refl
    ⋯-↑-· {ℓ} {𝕂 ∷ 𝕂s} (f ∷ fs) t₁ t₂ = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-· fs t₁ t₂) refl

    ⋯-↑-λ : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t : (µ₁ ▷▷ µ₁' ▷ 𝕖) ⊢ 𝕖)
            → ((λx t) ⋯* (f ↑** µ₁')) ≡ λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ]))
    ⋯-↑-λ               []       t = refl
    ⋯-↑-λ {ℓ} {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-λ fs t) refl

    ⋯-↑-foo : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ µ₁' µ} (f : µ₁ –[ 𝕂s ]→* µ₂)
             → (t : (µ₁ ▷▷ µ₁' ▷▷ µ) ⊢ 𝕖)
             → (foo {µ' = µ} t) ⋯* (f ↑** µ₁')
             ≡ foo {µ' = µ} (t ⋯* ((f ↑** µ₁') ↑** µ))
    ⋯-↑-foo {ℓ} {.[]}     []       t = refl
    ⋯-↑-foo {ℓ} {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-foo fs t) refl

    -- TODO: does it still work if we pull out the µ₁'?
    ⋯-↑ : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {µ₁ µ₂ } (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → f ≈ₓ g → f ≈ₜ g
    ⋯-↑ f g f≈g (` x) = f≈g x
    ⋯-↑ f g f≈g {µ₁' = µ₁'} (λx t) =
      (λx t) ⋯* (f ↑** µ₁')           ≡⟨ ⋯-↑-λ f t ⟩
      λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ])) ≡⟨ cong λx_ (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t) ⟩
      λx (t ⋯* (g ↑** µ₁' ↑** [ 𝕖 ])) ≡⟨ sym (⋯-↑-λ g t) ⟩
      (λx t) ⋯* (g ↑** µ₁')           ∎
    ⋯-↑ f g f≈g {µ₁' = µ₁'} (t₁ · t₂) =
      (t₁ · t₂) ⋯* (f ↑** µ₁')                                ≡⟨ ⋯-↑-· f t₁ t₂ ⟩
      (t₁ ⋯* (f ↑** µ₁' ↑** [])) · (t₂ ⋯* (f ↑** µ₁' ↑** [])) ≡⟨ cong₂ _·_ (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t₁)
                                                                           (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t₂) ⟩
      (t₁ ⋯* (g ↑** µ₁' ↑** [])) · (t₂ ⋯* (g ↑** µ₁' ↑** [])) ≡⟨ sym (⋯-↑-· g t₁ t₂) ⟩
      (t₁ · t₂) ⋯* (g ↑** µ₁')                                ∎
    ⋯-↑ f g f≈g {µ₁' = µ₁'} (foo {µ' = µ} t) =
      foo t ⋯* (f ↑** µ₁')                  ≡⟨ ⋯-↑-foo f t ⟩
      foo {µ' = µ} (t ⋯* (f ↑** µ₁' ↑** µ)) ≡⟨ cong foo (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t) ⟩
      foo {µ' = µ} (t ⋯* (g ↑** µ₁' ↑** µ)) ≡⟨ sym (⋯-↑-foo g t) ⟩
      foo t ⋯* (g ↑** µ₁')                  ∎

    multi-traversal : MultiTraversal
    multi-traversal = mkMultiTraversal _⋯_ ⋯-var ⋯-↑

    open import Kitty.Term.MultiTraversalDerived multi-traversal

  module Half-Derived where
    unquoteDecl terms = derive-Terms 𝕄 _⊢_ terms
    unquoteDecl _⋯_   = derive-⋯ terms _⋯_
    unquoteDecl ⋯-var = derive-⋯-var terms (quote _⋯_) ⋯-var
    unquoteDecl ⋯-↑   = derive-⋯-↑ terms (quote _⋯_) ⋯-↑

    -- Tests
    open import Data.List.Relation.Unary.Any using (here; there)
    open import Kitty.Term.MultiTraversal terms
    open import Kitty.Term.Kit terms
    open import Kitty.Term.Sub terms
    open import Kitty.Term.MultiSub terms
    open Kit ⦃ … ⦄
    open Sub ⦃ … ⦄
    open SubWithLaws ⦃ … ⦄
    open TraversalOps _⋯_

    _⋯'_ : ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    _⋯'_ = _⋯_

    ⋯-var' : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var' = ⋯-var

    ⋯-↑' : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {µ₁ µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → f ≈ₓ g → f ≈ₜ g
    ⋯-↑' = ⋯-↑

    multi-traversal : MultiTraversal
    multi-traversal = mkMultiTraversal _⋯_ ⋯-var ⋯-↑

    open Derived.Functional multi-traversal hiding (terms; _⋯_; ⋯-var; ⋯-↑) public

    `id : [] ⊢ 𝕖
    `id = λx (# 0)

    `f : [ 𝕖 ] ⊢ 𝕖
    `f = λx (# 0) · (# 1)

    `f' : [] ⊢ 𝕖
    `f' = `f ⋯ ⦅ `id ⦆ₛ

    test-`f' : `f' ≡ λx (# 0) · (λx (# 0))
    test-`f' = refl

  module Derived' where
    unquoteDecl traversal = derive-MultiTraversal 𝕄 _⊢_ traversal
    open Derived.Functional traversal public

    open import Data.List.Relation.Unary.Any using (here; there)

    `id : [] ⊢ 𝕖
    `id = λx (# 0)

    `f : [ 𝕖 ] ⊢ 𝕖
    `f = λx (# 0) · (# 1)

    `f' : [] ⊢ 𝕖
    `f' = `f ⋯ ⦅ `id ⦆ₛ

    test-`f' : `f' ≡ λx (# 0) · (λx (# 0))
    test-`f' = refl

module ExampleVarEq where
  open import Kitty.Term.Prelude
  open import Kitty.Term.Modes
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open ≡-Reasoning
  open import ReflectionLib.Categorical

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  infix  30 `[_]_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `[_]_ : ∀ {µ m M}  →  m→M m ≡ M  →  µ ∋ m  →  µ ⊢ M
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  module Derived' where
    unquoteDecl traversal = derive-MultiTraversal 𝕄 _⊢_ traversal
    open Derived traversal

