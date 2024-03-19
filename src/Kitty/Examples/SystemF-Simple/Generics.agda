-- This file defines a generic multi-sorted syntax and instantiates
-- the kit infrastructure for it.
--
-- The generic programming technique is closely oriented on the work
-- by Allais et al.[1] and at the end of the file an example is shown
-- of how to use it to model a simply typed lambda calculus.
--
-- The purpose of this file is to formally describe the syntaxes
-- supported by the reflection algorithm of our full framework.
--
-- In short: we support the same class of object languages as in the
-- work bai Allais et al.[1], but also polymorphism as we use the
-- intrinsic typing to describe the syntactic categories of our
-- untyped terms.
--
-- References:
-- [1] Guillaume Allais, Robert Atkey, James Chapman, Conor McBride,
--     and James McKinna. A type and scope safe universe of syntaxes
--     with binding: their semantics and proofs.
--     Proc. ACM Program. Lang., 2(ICFP):90:1--90:30, 2018.
--     doi:10.1145/3236785.

module Kitty.Examples.SystemF-Simple.Generics where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Examples.SystemF-Simple.Kits

module WithSort (Sort : SortTy → Set) where
  private variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : List (Sort Var)

  ScopedT : Set₁
  ScopedT = ∀ {st} → List (Sort Var) → Sort st → Set

  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : ∀ {st} → List (Sort Var) → Sort st → Desc → Desc
    `■ : ∀ {st} → Sort st → Desc

  ⟦_⟧ : Desc → ScopedT → ScopedT
  ⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
  ⟦ `X S' s' d  ⟧ X S s = X (S' ++ S) s' × ⟦ d ⟧ X S s
  ⟦ `■ {st'} s' ⟧ X {st} S s = Σ[ eq ∈ st' ≡ st ] s ≡ subst Sort eq s'

  data Tm (d : Desc) : ScopedT where
    `var : ∀ {S s} → S ∋ s → Tm d S s
    `con : ∀ {st S} {s : Sort st} → ⟦ d ⟧ (Tm d) S s → Tm d S s

  module WithDesc (d : Desc) where

    syn : Syntax
    syn = record
      { Sort        = Sort
      ; _⊢_         = Tm d
      ; `_          = `var
      ; `-injective = λ { refl → refl }
      }

    open Syntax syn hiding (Sort; `_; `-injective) public

    mutual
      _⋯_ :
        ∀ {S₁ : List (Sort Var)} {M : Sort st} {S₂ : List (Sort Var)}
          {_∋/⊢_ : Scoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ →
        Tm d S₁ M → S₁ –[ 𝕂 ]→ S₂ → Tm d S₂ M
      _⋯_ (`var x)  f = `/id (f _ x)
      _⋯_ (`con e') f = `con (e' ⋯' f)

      _⋯'_ :
        ∀ {d'} {S₁ : List (Sort Var)} {M : Sort st} {S₂ : List (Sort Var)}
          {_∋/⊢_ : Scoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ →
        ⟦ d' ⟧ (Tm d) S₁ M → S₁ –[ 𝕂 ]→ S₂ → ⟦ d' ⟧ (Tm d) S₂ M
      _⋯'_ {d' = `σ A d'}     (a , D') f = a , D' ⋯' f
      _⋯'_ {d' = `X S' M' d'} (e , e') f = e ⋯ (f ↑* S') , e' ⋯' f
      _⋯'_ {d' = `■ M'}       e        f = e

    ⋯-var :
      ∀ {S₁ : List (Sort Var)} {m : Sort Var} {S₂ : List (Sort Var)}
        {_∋/⊢_ : Scoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        (x : S₁ ∋ m) (ϕ : S₁ –[ 𝕂 ]→ S₂) →
      `/id (ϕ m x) ≡ `/id (ϕ m x)
    ⋯-var x ϕ = refl

    mutual
      ⋯-id :
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄
          {S st} {s : Sort st} (t : Tm d S s) →
        (t ⋯ id) ≡ t
      ⋯-id (`var x) = `/`-is-` x
      ⋯-id (`con e) = cong `con (⋯-id' e)

      ⋯-id' :
        ∀ {d'} {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄
          {S st} {s : Sort st} (t : ⟦ d' ⟧ (Tm d) S s) →
        (t ⋯' id) ≡ t
      ⋯-id' {d' = `σ A d'}     (a , D')  = cong (a ,_) (⋯-id' D')
      ⋯-id' {d' = `X S' M' d'} (e₁ , e₂) = cong₂ _,_ (trans (cong (e₁ ⋯_) (~-ext (id↑*~id S'))) (⋯-id e₁)) (⋯-id' e₂)
      ⋯-id' {d' = `■ M'}       (refl , refl) = refl

    KT : Traversal
    KT = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var ; ⋯-id  = ⋯-id }

    open Traversal KT hiding (_⋯_; ⋯-id; ⋯-var) public

    mutual
      fusion :
        ∀ {_∋/⊢₁_ _∋/⊢₂_ _∋/⊢_ : Scoped}
          ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
          ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
          (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
        → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
      fusion (`var x)  ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
      fusion (`con e') ϕ₁ ϕ₂ = cong `con (fusion' e' ϕ₁ ϕ₂)

      fusion' :
        ∀ {d'} {_∋/⊢₁_ _∋/⊢₂_ _∋/⊢_ : Scoped}
          ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
          ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
          (t : ⟦ d' ⟧ (Tm d) S₁ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
        → (t ⋯' ϕ₁) ⋯' ϕ₂ ≡ t ⋯' (ϕ₁ ·ₖ ϕ₂)
      fusion' {d' = `σ A d'}     (a , D')  ϕ₁ ϕ₂ = cong (a ,_) (fusion' D' ϕ₁ ϕ₂)
      fusion' {d' = `X S' M' d'} (e₁ , e₂) ϕ₁ ϕ₂ = cong₂ _,_ (trans (fusion e₁ (ϕ₁ ↑* S') (ϕ₂ ↑* S'))
                                                                    (cong (e₁ ⋯_) (sym (~-ext (dist-↑*-· S' ϕ₁ ϕ₂)))) )
                                                              (fusion' e₂ ϕ₁ ϕ₂)
      fusion' {d' = `■ M'}       (refl , refl) ϕ₁ ϕ₂ = refl

    CT : CTraversal
    CT = record { fusion = fusion }

    open CTraversal CT public hiding (fusion)

module Example-STLC where
  data Sort : SortTy → Set where
    𝕖 : Sort Var

  open WithSort Sort

  data Label : Set where
    [λ] [·] : Label

  desc : Desc
  desc = `σ Label λ where
    [λ] → `X (𝕖 ∷ []) 𝕖 (`■ 𝕖)
    [·] → `X [] 𝕖 (`X [] 𝕖 (`■ 𝕖))

  open WithDesc desc

  pattern `λ_ e     = `con ([λ] , e , (refl , refl))
  pattern _·_ e₁ e₂ = `con ([·] , e₁ , e₂ , (refl , refl))
  pattern `_ x      = `var x

  `id : [] ⊢ 𝕖
  `id = `λ (` zero)

  test : (` zero) ⋯ ⦅ `id ⦆ ≡ `id
  test = refl

  
