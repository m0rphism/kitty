{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Term.Reflection.MultiTraversalTest where

open import Kitty.Term.Reflection.MultiTraversal
import Kitty.Term.MultiTraversalDerived as Derived

module Example where
  open import Kitty.Term.Prelude
  open import Kitty.Term.Terms
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open ≡-Reasoning
  open import ReflectionLib.Categorical

  data Sort : SortTy → Set where 𝕖 : Sort Var

  infix  30 `_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : ∀ {st} → List (Sort Var) → Sort st → Set where
    `_    : ∀ {S s}  →  S ∋ s  →  S ⊢ s
    λx_   : ∀ {S}  →  (S ▷ 𝕖) ⊢ 𝕖  →  S ⊢ 𝕖
    _·_   : ∀ {S}  →  S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
    foo   : ∀ {S S'}  →  (S ▷▷ S') ⊢ 𝕖  →  S ⊢ 𝕖

  module Manual where
    terms : Terms
    terms = record { Sort = Sort; _⊢_ = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }

    open Terms terms hiding (Sort; _⊢_; `_)

    open import Kitty.Term.Sub terms
    open import Kitty.Term.MultiSub terms
    open import Kitty.Term.MultiTraversal terms
    open import Kitty.Term.Kit terms
    open import Kitty.Util.Star
    open Kit ⦃ ... ⦄
    open Sub ⦃ ... ⦄
    open SubWithLaws ⦃ ... ⦄

    _⋯_ : ∀ {ℓ} {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ 𝕊 : Sub ℓ ⦄ {S₁} {S₂} {st} {s : Sort st} → S₁ ⊢ s → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ s
    (` x)     ⋯ f = `/id (x & f)
    (λx t)    ⋯ f = λx (t ⋯ (f ↑*' _))
    (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
    (foo t)   ⋯ f = foo (t ⋯ (f ↑*' _))

    ⋯-var : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {m} (x : S₁ ∋ m) (f : S₁ –→ S₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var x f = refl

    open TraversalOps _⋯_

    ⋯-↑-· : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂ S₁'} (f : S₁ –[ 𝕂s ]→* S₂)
            → (t₁ t₂ : (S₁ ▷▷ S₁') ⊢ 𝕖)
            → ((t₁ · t₂) ⋯* (f ↑** S₁')) ≡ (t₁ ⋯* (f ↑** S₁' ↑** [])) · (t₂ ⋯* (f ↑** S₁' ↑** []))
    ⋯-↑-· {ℓ} {.[]}     []       t₁ t₂ = refl
    ⋯-↑-· {ℓ} {𝕂 ∷ 𝕂s} (f ∷ fs) t₁ t₂ = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-· fs t₁ t₂) refl

    ⋯-↑-λ : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂ S₁'} (f : S₁ –[ 𝕂s ]→* S₂)
            → (t : (S₁ ▷▷ S₁' ▷ 𝕖) ⊢ 𝕖)
            → ((λx t) ⋯* (f ↑** S₁')) ≡ λx (t ⋯* (f ↑** S₁' ↑** [ 𝕖 ]))
    ⋯-↑-λ               []       t = refl
    ⋯-↑-λ {ℓ} {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-λ fs t) refl

    ⋯-↑-foo : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂ S₁' S} (f : S₁ –[ 𝕂s ]→* S₂)
             → (t : (S₁ ▷▷ S₁' ▷▷ S) ⊢ 𝕖)
             → (foo {S' = S} t) ⋯* (f ↑** S₁')
             ≡ foo {S' = S} (t ⋯* ((f ↑** S₁') ↑** S))
    ⋯-↑-foo {ℓ} {.[]}     []       t = refl
    ⋯-↑-foo {ℓ} {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ unpack-kit 𝕂 ⦄) (⋯-↑-foo fs t) refl

    -- TODO: does it still work if we pull out the S₁'?
    ⋯-↑ : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {S₁ S₂} (f : S₁ –[ 𝕂s₁ ]→* S₂) (g : S₁ –[ 𝕂s₂ ]→* S₂)
          → f ≈ₓ g → f ≈ₜ g
    ⋯-↑ f g f≈g (` x) = f≈g x
    ⋯-↑ f g f≈g {S₁' = S₁'} (λx t) =
      (λx t) ⋯* (f ↑** S₁')           ≡⟨ ⋯-↑-λ f t ⟩
      λx (t ⋯* (f ↑** S₁' ↑** [ 𝕖 ])) ≡⟨ cong λx_ (⋯-↑ (f ↑** S₁') (g ↑** S₁') (≈↑** f g f≈g) t) ⟩
      λx (t ⋯* (g ↑** S₁' ↑** [ 𝕖 ])) ≡⟨ sym (⋯-↑-λ g t) ⟩
      (λx t) ⋯* (g ↑** S₁')           ∎
    ⋯-↑ f g f≈g {S₁' = S₁'} (t₁ · t₂) =
      (t₁ · t₂) ⋯* (f ↑** S₁')                                ≡⟨ ⋯-↑-· f t₁ t₂ ⟩
      (t₁ ⋯* (f ↑** S₁' ↑** [])) · (t₂ ⋯* (f ↑** S₁' ↑** [])) ≡⟨ cong₂ _·_ (⋯-↑ (f ↑** S₁') (g ↑** S₁') (≈↑** f g f≈g) t₁)
                                                                           (⋯-↑ (f ↑** S₁') (g ↑** S₁') (≈↑** f g f≈g) t₂) ⟩
      (t₁ ⋯* (g ↑** S₁' ↑** [])) · (t₂ ⋯* (g ↑** S₁' ↑** [])) ≡⟨ sym (⋯-↑-· g t₁ t₂) ⟩
      (t₁ · t₂) ⋯* (g ↑** S₁')                                ∎
    ⋯-↑ f g f≈g {S₁' = S₁'} (foo {S' = S} t) =
      foo t ⋯* (f ↑** S₁')                  ≡⟨ ⋯-↑-foo f t ⟩
      foo {S' = S} (t ⋯* (f ↑** S₁' ↑** S)) ≡⟨ cong foo (⋯-↑ (f ↑** S₁') (g ↑** S₁') (≈↑** f g f≈g) t) ⟩
      foo {S' = S} (t ⋯* (g ↑** S₁' ↑** S)) ≡⟨ sym (⋯-↑-foo g t) ⟩
      foo t ⋯* (g ↑** S₁')                  ∎

    multi-traversal : MultiTraversal
    multi-traversal = mkMultiTraversal _⋯_ ⋯-var ⋯-↑

    open import Kitty.Term.MultiTraversalDerived multi-traversal

  module Half-Derived where
    unquoteDecl terms = derive-Terms Sort _⊢_ terms
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
    open Terms terms using (VarScoped)

    _⋯'_ : ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {st} {s : Sort st} → S₁ ⊢ s → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ s
    _⋯'_ = _⋯_

    ⋯-var' : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {m} (x : S₁ ∋ m) (f : S₁ –→ S₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var' = ⋯-var

    ⋯-↑' : ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {S₁ S₂} (f : S₁ –[ 𝕂s₁ ]→* S₂) (g : S₁ –[ 𝕂s₂ ]→* S₂)
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
    unquoteDecl traversal = derive-MultiTraversal Sort _⊢_ traversal
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

-- module ExampleVarEq where
--   open import Kitty.Term.Prelude
--   open import Kitty.Term.Sorts
--   open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
--   open ≡-Reasoning
--   open import ReflectionLib.Categorical

--   data Sortᵥ : Set where 𝕖 : Sortᵥ
--   data Sortₜ : Set where 𝕖 : Sortₜ

--   m→M : Sortᵥ → Sortₜ
--   m→M 𝕖 = 𝕖

--   𝕄 : Sorts
--   𝕄 = record { VarSort = Sortᵥ ; TermSort = Sortₜ ; m→M = m→M }

--   infix  30 `[_]_
--   infixl 20 _·_
--   infixr 10 λx_

--   data _⊢_ : List Sortᵥ → Sortₜ → Set where
--     `[_]_ : ∀ {S m M}  →  m→M m ≡ M  →  S ∋ m  →  S ⊢ M
--     λx_   : ∀ {S}  →  (S ▷ 𝕖) ⊢ 𝕖  →  S ⊢ 𝕖
--     _·_   : ∀ {S}  →  S ⊢ 𝕖  →  S ⊢ 𝕖  →  S ⊢ 𝕖
--     foo   : ∀ {S S'}  →  (S ▷▷ S') ⊢ 𝕖  →  S ⊢ 𝕖

--   module Derived' where
--     unquoteDecl traversal = derive-MultiTraversal 𝕄 _⊢_ traversal
--     open Derived traversal


