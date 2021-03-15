open import KitTheory.Modes

module KitTheory.Generics (𝕄 : Modes) where
-- module KitTheory.Generics where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Size

open Modes 𝕄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

module SizeExample where
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Nat using (ℕ; zero; suc)

  data Desc : Set₁ where
    `ℕ     : Desc
    `Const : Set → Desc
    `Id    : Desc
    _`+_   : Desc → Desc → Desc
    _`*_   : Desc → Desc → Desc

  SSet = Size → Set

  ⟦_⟧ : Desc → SSet → SSet
  ⟦ `ℕ       ⟧ A = λ _ → ℕ
  ⟦ `Const B ⟧ A = λ _ → B
  ⟦ `Id      ⟧ A = A
  ⟦ d₁ `+ d₂ ⟧ A = λ s → ⟦ d₁ ⟧ A s × ⟦ d₂ ⟧ A s
  ⟦ d₁ `* d₂ ⟧ A = λ s → ⟦ d₁ ⟧ A s ⊎ ⟦ d₂ ⟧ A s

  data µD (d : Desc) (s : Size) : Set where
    µd : ∀ {s' : Size< s} → ⟦ d ⟧ (µD d) s' → µD d s

  private variable A B : Set

  mapD : ∀ {A B : SSet} {s s'} d → (A s → B s') → ⟦ d ⟧ A s → ⟦ d ⟧ B s'
  mapD `ℕ         f t         = t
  mapD (`Const x) f t         = t
  mapD `Id        f t         = f t
  mapD (d₁ `+ d₂) f (t₁ , t₂) = mapD d₁ f t₁ , mapD d₂ f t₂
  mapD (d₁ `* d₂) f (inj₁ t₁) = inj₁ (mapD d₁ f t₁)
  mapD (d₁ `* d₂) f (inj₂ t₂) = inj₂ (mapD d₂ f t₂)

  incℕ : ∀ d s → µD d s → µD d s
  incℕ d s (µd {s'} x) = µd (mapD d (incℕ d s') x )

-- data Desc : Set₁ where
--   `σ : (A : Set) → (A → Desc) → Desc
--   `X : List VarMode → TermMode → Desc → Desc
--   `■ : TermMode → Desc

-- Scoped : Set₁
-- Scoped = List VarMode → TermMode → Set

-- ⟦_⟧ : Desc → Scoped → Scoped
-- ⟦ `σ A d     ⟧ X µ M = Σ[ a ∈ A ] (⟦ d a ⟧ X µ M)
-- ⟦ `X µ' M' d ⟧ X µ M = X (µ' ++ µ) M' × ⟦ d ⟧ X µ M
-- ⟦ `■ M'      ⟧ X µ M = M ≡ M'

-- data Tm (d : Desc) : Size → Scoped where
--   `var : ∀ {µ m s} → µ ∋ m → Tm d (↑ s) µ (m→M m)
--   `con : ∀ {µ M s} → ⟦ d ⟧ (Tm d s) µ M → Tm d (↑ s) µ M

-- -- module TerminationTest where
-- --   map⟦⟧ : (d : Desc) → (_⊢_ _⊢'_ : Scoped) → (f : ∀ µ µ' M → µ ⊢ M → µ' ⊢' M) → ⟦ d ⟧ _⊢_ µ M → ⟦ d ⟧ _⊢'_ µ' M
-- --   map⟦⟧ (`σ A dA)  _⊢_ _⊢'_ f (a , t) = a , map⟦⟧ (dA a) _⊢_ _⊢'_ f t
-- --   map⟦⟧ (`X µ M d) _⊢_ _⊢'_ f (x , t) = f _ _ _ x , map⟦⟧ d _⊢_ _⊢'_ f t
-- --   map⟦⟧ (`■ x)     _⊢_ _⊢'_ f t       = t

-- --   mapTm : (d : Desc) → (f : ∀ µ µ' M → Tm d ∞ µ M → Tm d ∞ µ' M) → ∀ µ µ' M → Tm d ∞ µ M → Tm d ∞ µ' M
-- --   mapTm d f µ µ' M (`var x) = f _ _ _ (`var x)
-- --   mapTm d f µ µ' M (`con x) = `con (map⟦⟧ d (Tm d ∞) (Tm d ∞) (mapTm d f) x)

-- _⊢[_]_ : List VarMode → Desc → TermMode → Set
-- µ ⊢[ d ] M = Tm d _ µ M

-- -- -- module DescKit (d : Desc) where
-- -- module DescKit where

-- --   -- TODO: we would need to move the `_ constructor out of Terms as ⟦ d ⟧ doesn't have variables.
-- --   𝕋⟦⟧ : Desc → Terms 𝕄 → Terms 𝕄
-- --   𝕋⟦⟧ d t = record { _⊢_ = ⟦ d ⟧ (Terms._⊢_ t)
-- --                    ; `_ = {!!}
-- --                    }

-- --   𝕋 : Desc → Size → Terms 𝕄
-- --   𝕋 d s = record { _⊢_ = Tm d (↑ s)
-- --                ; `_ = `var
-- --                }

-- --   import KitTheory.Kit
-- --   -- open import KitTheory.Kit
-- --   -- open Kit {{...}}

-- --   private

-- --     Traversal : Terms 𝕄 → (Size → Scoped) → Set₁
-- --     Traversal 𝕋 _⊢_ = let open KitTheory.Kit 𝕋 in
-- --                       ∀ {{𝕂 : Kit}} {µ₁ µ₂ M} {s} → _⊢_ s µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → _⊢_ s µ₂ M

-- --     trav : (d : Desc) → (_⊢_ : Size → Scoped) → ∀ 𝕋 → Traversal 𝕋 _⊢_ → Traversal 𝕋 (λ s → ⟦ d ⟧ (_⊢_ s))
-- --     trav (`σ A dA)   _⊢_ 𝕋 T (a , t) f = a , trav (dA a) _⊢_ 𝕋 T t f
-- --     trav (`X µ' M d) _⊢_ 𝕋 T (x , t) f = T x (f ↑* µ') , trav d _⊢_ 𝕋 T t f where open KitTheory.Kit.Kit {{...}}
-- --     trav (`■ x)      _⊢_ 𝕋 T t       f = t

-- --     trav' : (d : Desc) {s : Size} → Traversal (𝕋 d s) (Tm d)
-- --     trav' d {s} (`var x) f = {!!}
-- --     trav' d {s} (`con x) f = `con (trav d (Tm d) (𝕋 d s) (trav' d {s} ) x f)
-- --     -- trav' d {s} (`var x) f = tm' (f _ x) where open KitTheory.Kit.Kit {{...}}
-- --     -- trav' d {s} (`con x) f = `con (trav d (Tm d (↑ s)) (𝕋 d s) (trav' d s) x f)

-- --     -- trav : (d : Desc) → (_⊢'_ : Scoped) → KitTraversal 𝕋' → KitTraversal (𝕋⟦⟧ d 𝕋')

-- --     -- kit-traversal' : (d : Desc) → (𝕋' : Terms 𝕄) → KitTraversal 𝕋' → KitTraversal (𝕋⟦⟧ d 𝕋')
-- --     -- KitTraversal._⋯_ (kit-traversal' (`σ A dA)   𝕋' T') (a , t)  f = a , {!KitTraversal._⋯_ (kit-traversal' (dA a) 𝕋' T') t f!}
-- --     -- KitTraversal._⋯_ (kit-traversal' (`X µ' M d) 𝕋' T') (t' , t) f = {!KitTraversal._⋯_ T' t' (f ↑* µ')!}
-- --     -- KitTraversal._⋯_ (kit-traversal' (`■ x₁)     𝕋' T') refl     f = refl
-- --     -- KitTraversal.⋯-var (kit-traversal' d 𝕋' T') = {!!}

-- -- --     kit-traversal : (d : Desc) → KitTraversal (𝕋 d)
-- -- --     KitTraversal._⋯_ (kit-traversal d)            (`var x) f = {!x!}
-- -- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f with dA a
-- -- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , a₁ , x)) f    | `σ A₁ x₁    = {!x!}
-- -- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f    | `X x₁ x₂ xx = {!!}
-- -- --     KitTraversal._⋯_ (kit-traversal (`σ A dA))    (`con (a , x)) f    | `■ x₁       = {!!}
-- -- --     KitTraversal._⋯_ (kit-traversal (`X x₁ x₂ d)) (`con x) f = {!x!}
-- -- --     KitTraversal._⋯_ (kit-traversal (`■ x₁))      (`con x) f = {!x!}
-- -- --     KitTraversal.⋯-var (kit-traversal d) = {!!}
-- -- --     -- KitTraversal._⋯_ kit-traversal (`var x) f = tm' (f _ x)
-- -- --     -- KitTraversal._⋯_ kit-traversal (`con x) f = {!!}
-- -- --     -- KitTraversal.⋯-var kit-traversal x f = refl

-- -- -- --   -- kit-traversal : KitTraversal
-- -- -- --   -- KitTraversal._⋯_ kit-traversal (`var x) f = tm' (f _ x)
-- -- -- --   -- KitTraversal._⋯_ kit-traversal (`con x) f = {!!}
-- -- -- --   -- KitTraversal.⋯-var kit-traversal x f = refl

-- -- -- --   -- open import KitTheory.Kit           VarMode' TermMode' m→M' _⊢'_ `'_
-- -- -- --   -- open import KitTheory.Compose       VarMode' TermMode' m→M' _⊢'_ `'_
-- -- -- --   -- open import KitTheory.ComposeLemmas VarMode' TermMode' m→M' _⊢'_ `'_
-- -- -- --   -- open import KitTheory.Types         VarMode' TermMode' m→M' _⊢'_ `'_ public

-- -- -- --   -- open Kit {{...}} public
-- -- -- --   -- open KitTraversal {{...}} public

-- -- -- -- data Desc (I : Set) : Set₁ where
-- -- -- --   `σ : (A : Set) → (A → Desc I) → Desc I
-- -- -- --   `X : List I → I → Desc I → Desc I
-- -- -- --   `■ : I → Desc I

-- -- -- -- _−Scoped : Set → Set₁
-- -- -- -- I −Scoped = I → List I → Set

-- -- -- -- ⟦_⟧ : ∀ {I : Set} → Desc I → (List I → I −Scoped) → I −Scoped
-- -- -- -- ⟦ `σ A d   ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
-- -- -- -- ⟦ `X ∆ j d ⟧ X i Γ = X ∆ j Γ × ⟦ d ⟧ X i Γ
-- -- -- -- ⟦ `■ j     ⟧ X i Γ = i ≡ j

-- -- -- -- data Tm {I : Set} (d : Desc I) : Size → I −Scoped where
-- -- -- --   `var : ∀ {Γ i s} → Γ ∋ i → Tm d (↑ s) i Γ
-- -- -- --   `con : ∀ {Γ i s} → ⟦ d ⟧ (λ Δ i Γ → Tm d s i (Δ ++ Γ)) i Γ → Tm d (↑ s) i Γ

-- -- -- -- module Example where
-- -- -- --   open import Data.Unit
-- -- -- --   open import Data.Bool

-- -- -- --   data `UTLC : Set where
-- -- -- --     `app `abs : `UTLC

-- -- -- --   UTLC : Desc ⊤
-- -- -- --   UTLC = `σ `UTLC λ where
-- -- -- --     `app → `X [] tt (`X [] tt (`■ tt))
-- -- -- --     `abs → `X (tt ∷ []) tt (`■ tt)

-- -- -- --   UTLC-id : Tm UTLC ∞ tt []
-- -- -- --   UTLC-id = `con (`abs , `var (here refl) , refl)
