open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Generics
    (VarMode  : Set)
    (TermMode : Set)
    (m→M      : VarMode → TermMode)
    (_⊢_      : List VarMode → TermMode → Set)
    (`_       : ∀ {µ m} → m ∈ µ → µ ⊢ m→M m)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Size

private
  variable
    m m' m₁ m₂    : VarMode
    µ µ' µ₁ µ₂ µ₃ : List VarMode
    M M' M₁ M₂    : TermMode
    x y z         : m ∈ µ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

data Desc (I : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I) → Desc I
  `X : List I → I → Desc I → Desc I
  `■ : I → Desc I

_−Scoped : Set → Set₁
I −Scoped = I → List I → Set

⟦_⟧ : ∀ {I : Set} → Desc I → (List I → I −Scoped) → I −Scoped
⟦ `σ A d   ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ `X ∆ j d ⟧ X i Γ = X ∆ j Γ × ⟦ d ⟧ X i Γ
⟦ `■ j     ⟧ X i Γ = i ≡ j

data Tm {I : Set} (d : Desc I) : Size → I −Scoped where
  `var : ∀ {Γ i s} → i ∈ Γ → Tm d (↑ s) i Γ
  `con : ∀ {Γ i s} → ⟦ d ⟧ (λ Δ i Γ → Tm d s i (Δ ++ Γ)) i Γ → Tm d (↑ s) i Γ

module DescKit (I : Set) (d : Desc I) where
  VarMode' = I

  TermMode' = I

  m→M' : VarMode' → TermMode'
  m→M' x = x

  _⊢'_ : List VarMode' → TermMode' → Set
  μ ⊢' m = Tm d ∞ m μ

  `'_ : ∀ {µ m} → m ∈ µ → µ ⊢' m→M' m
  `' x = `var x

  open import KitTheory.Kit           VarMode' TermMode' m→M' _⊢'_ `'_
  open import KitTheory.Compose       VarMode' TermMode' m→M' _⊢'_ `'_
  open import KitTheory.ComposeLemmas VarMode' TermMode' m→M' _⊢'_ `'_
  open import KitTheory.Types         VarMode' TermMode' m→M' _⊢'_ `'_ public

  open Kit {{...}} public
  open KitTraversal {{...}} public

  kit-traversal : KitTraversal
  KitTraversal._⋯_ kit-traversal (`var x) f = tm' (f _ x)
  KitTraversal._⋯_ kit-traversal (`con x) f = {!!}
  KitTraversal.⋯-var kit-traversal x f = refl

module Example where
  open import Data.Unit
  open import Data.Bool

  data `UTLC : Set where
    `app `abs : `UTLC

  UTLC : Desc ⊤
  UTLC = `σ `UTLC λ where
    `app → `X [] tt (`X [] tt (`■ tt))
    `abs → `X (tt ∷ []) tt (`■ tt)

  UTLC-id : Tm UTLC ∞ tt []
  UTLC-id = `con (`abs , `var (here refl) , refl)
