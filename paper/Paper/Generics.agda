module Paper.Generics where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Function using (_$_)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Paper.Kits

module WithSort(Sort : SortTy → Set) where
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

  module WithDesc {d : Desc} where

    terms : Terms
    terms = record
      { Sort        = Sort
      ; _⊢_         = Tm d
      ; `_          = `var
      ; `-injective = λ { refl → refl }
      }

    open Terms terms hiding (Sort; `_; `-injective) public

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
      ⋯-id (`var x) = id/`/id x
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
      ⋯-assoc :
        ∀ {_∋/⊢₁_ _∋/⊢₂_ _∋/⊢_ : Scoped}
          ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
          ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
          (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
        → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₘ ϕ₂)
      ⋯-assoc (`var x)  ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
      ⋯-assoc (`con e') ϕ₁ ϕ₂ = cong `con (⋯-assoc' e' ϕ₁ ϕ₂)

      ⋯-assoc' :
        ∀ {d'} {_∋/⊢₁_ _∋/⊢₂_ _∋/⊢_ : Scoped}
          ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
          ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
          (t : ⟦ d' ⟧ (Tm d) S₁ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
        → (t ⋯' ϕ₁) ⋯' ϕ₂ ≡ t ⋯' (ϕ₁ ·ₘ ϕ₂)
      ⋯-assoc' {d' = `σ A d'}     (a , D')  ϕ₁ ϕ₂ = cong (a ,_) (⋯-assoc' D' ϕ₁ ϕ₂)
      ⋯-assoc' {d' = `X S' M' d'} (e₁ , e₂) ϕ₁ ϕ₂ = cong₂ _,_ (trans (⋯-assoc e₁ (ϕ₁ ↑* S') (ϕ₂ ↑* S'))
                                                                    (cong (e₁ ⋯_) (sym (~-ext (dist-↑*-· S' ϕ₁ ϕ₂)))) )
                                                              (⋯-assoc' e₂ ϕ₁ ϕ₂)
      ⋯-assoc' {d' = `■ M'}       (refl , refl) ϕ₁ ϕ₂ = refl

    CT : ComposeTraversal
    CT = record { ⋯-assoc = ⋯-assoc }

    open ComposeTraversal CT public hiding (⋯-assoc)

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

  open WithDesc {desc}

  pattern `λ_ e     = `con ([λ] , e , (refl , refl))
  pattern _·_ e₁ e₂ = `con ([·] , e₁ , e₂ , (refl , refl))
  pattern `_ x      = `var x

  `id : [] ⊢ 𝕖
  `id = `λ (` zero)

  test : (` zero) ⋯ ⦅ `id ⦆ ≡ `id
  test = refl

  
