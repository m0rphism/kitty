open import KitTheory.Modes

module KitTheory.Generics (𝕄 : Modes) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Size

open Modes 𝕄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Size

Scoped : Set₁
Scoped = List VarMode → TermMode → Set

SScoped : Set₁
SScoped = Size → Scoped

data Desc : Set₁ where
  `σ : (A : Set) → (A → Desc) → Desc
  `X : List VarMode → TermMode → Desc → Desc
  `■ : TermMode → Desc

⟦_⟧ : Desc → Scoped → Scoped
⟦ `σ A d     ⟧ X µ M = Σ[ a ∈ A ] (⟦ d a ⟧ X µ M)
⟦ `X µ' M' d ⟧ X µ M = X (µ' ++ µ) M' × ⟦ d ⟧ X µ M
⟦ `■ M'      ⟧ X µ M = M ≡ M'

data Tm (d : Desc) (s : Size) : Scoped where
  `var : ∀ {µ m} → µ ∋ m → Tm d s µ (m→M m)
  `con : ∀ {µ M} {s' : Size< s} → ⟦ d ⟧ (Tm d s') µ M → Tm d s µ M

module KitCopy (_;_⊢_ : SScoped) (`_ : ∀ {µ m s} → µ ∋ m → s ; µ ⊢ m→M m)  where

  record Kit : Set₁ where
    infix   4  _;_◆_
    infixl  6  _↑_  _↑*_

    field
      StuffMode : Set
      _;_◆_     : Size → List VarMode → StuffMode → Set
      m→SM      : VarMode → StuffMode
      SM→M      : StuffMode → TermMode
      vr        : ∀ m → µ ∋ m → s ; µ ◆ m→SM m
      tm        : ∀ SM → s ; µ ◆ SM → s ; µ ⊢ SM→M SM
      wk        : ∀ SM → s ; µ ◆ SM → s ; (m' ∷ µ) ◆ SM
      m→SM→M    : ∀ m → SM→M (m→SM m) ≡ m→M m
      wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
      tm-vr     : ∀ x → subst (s ; µ ⊢_) (m→SM→M m) (tm _ (vr _ x)) ≡ ` x

    _–→_;_ : List VarMode → Size → List VarMode → Set
    _–→_;_ µ₁ s₂ µ₂ = ∀ m → µ₁ ∋ m → s₂ ; µ₂ ◆ m→SM m

    tm' : s ; µ ◆ m→SM m → s ; µ ⊢ m→M m
    tm' {s} {µ} {m} t = subst (s ; µ ⊢_) (m→SM→M m) (tm _ t)

    _↑_ : µ₁ –→ s ; µ₂ → ∀ m → (m ∷ µ₁) –→ s ; (m ∷ µ₂)
    (f ↑ m) _ (here p)  = vr _ (here p)
    (f ↑ m) _ (there x) = wk _ (f _ x)

    _↑*_ : µ₁ –→ s ; µ₂ → ∀ µ' → (µ' ++ µ₁) –→ s ; (µ' ++ µ₂)
    f ↑* []       = f
    f ↑* (m ∷ µ') = (f ↑* µ') ↑ m

  open Kit {{...}}

  _–[_]→_;_ : List VarMode → (_ : Kit) → Size → List VarMode → Set _
  µ₁ –[ 𝕂 ]→ s₂ ; µ₂ = Kit._–→_;_ 𝕂 µ₁ s₂ µ₂

  record KitTraversal : Set₁ where
    infixl  5  _⋯_

    field
      _⋯_   : ∀ {{𝕂 : Kit}} →
              s₁ ; µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ s₂ ; µ₂ → (s₁ ⊔ˢ s₂) ; µ₂ ⊢ M
      ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ ∞ ; µ₂) →
              (` x) ⋯ f ≡ subst (∞ ; µ₂ ⊢_) (m→SM→M m) (tm _ (f _ x))

    kitᵣ : Kit
    Kit.StuffMode kitᵣ = VarMode
    Kit._;_◆_     kitᵣ = λ _ → _∋_
    Kit.m→SM      kitᵣ = λ x → x
    Kit.SM→M      kitᵣ = m→M
    Kit.vr        kitᵣ = λ _ x → x
    Kit.tm        kitᵣ = λ _ → `_
    Kit.wk        kitᵣ = λ _ → there
    Kit.m→SM→M    kitᵣ = λ _ → refl
    Kit.wk-vr     kitᵣ = λ _ _ → refl
    Kit.tm-vr     kitᵣ = λ _ → refl

    private instance _ = kitᵣ

    kitₛ : Kit
    Kit.StuffMode kitₛ = TermMode
    Kit._;_◆_     kitₛ = _;_⊢_
    Kit.m→SM      kitₛ = m→M
    Kit.SM→M      kitₛ = λ x → x
    Kit.vr        kitₛ = λ _ → `_
    Kit.tm        kitₛ = λ _ x → x
    Kit.wk        kitₛ = λ _ x → x ⋯ wk
    Kit.m→SM→M    kitₛ = λ _ → refl
    Kit.wk-vr     kitₛ = λ _ x → ⋯-var x wk
    Kit.tm-vr     kitₛ = λ x → refl

module Mapping (_;_⊢₁_ _;_⊢₂_ : SScoped) where
  _;_–→_;_ : Size → List VarMode → Size → List VarMode → Set
  s₁ ; µ₁ –→ s₂ ; µ₂ = ∀ M → s₁ ; µ₁ ⊢₁ M → s₂ ; µ₂ ⊢₂ M

  Lift : Set
  Lift = ∀ {s₁ s₂ µ₁ µ₂} µ → (s₁ ; µ₁ –→ s₂ ; µ₂) → (s₁ ; (µ ++ µ₁) –→ s₂ ; (µ ++ µ₂))

  map⟦⟧ : ∀ {µ₁ µ₂} s₁ s₂ (d : Desc) →
    (∀ µ → s₁ ; (µ ++ µ₁) –→ s₂ ; (µ ++ µ₂)) →
    ⟦ d ⟧ (s₁ ;_⊢₁_) µ₁ M →
    ⟦ d ⟧ (s₂ ;_⊢₂_) µ₂ M
  map⟦⟧ s₁ s₂ (`σ A dA)  f (a , t) = a , map⟦⟧ s₁ s₂ (dA a) f t
  map⟦⟧ s₁ s₂ (`X µ M d) f (x , t) = f µ _ x , map⟦⟧ s₁ s₂ d f t
  map⟦⟧ s₁ s₂ (`■ x)     f t       = t

module GenKit (d : Desc) where
  open KitCopy (Tm d) (λ x → `var x)
  open Kit {{...}}
  open Mapping

  -- instance trav : KitTraversal
  -- KitTraversal._⋯_ trav (`var x) f = tm' (f _ x)
  -- KitTraversal._⋯_ trav {s₁ = s₁} {s₂ = s₂} (`con {s' = s'} t) f = `con {s' = s' ⊔ˢ s₂} {!!}

  -- -- KitTraversal._⋯_ trav {s₁ = s₁} {s₂ = s₂} (`con {s' = s'} t) f = `con (map⟦⟧ (Tm d) (Tm d) _ _ d (λ µ _ t → KitTraversal._⋯_ trav t (f ↑* µ)) t)

  -- -- KitTraversal._⋯_ trav {s₁ = s₁} {s₂ = s₂} (`con {s' = s'} t) f = {!`con {s' = s' ⊔ˢ s₂} (trav⟦⟧ {s₁ = s₁} {s' = s'} t f)!} where
  -- --     trav⟦⟧ : ∀ {d µ₁ µ₂ s₁ s₂ M} {s' : Size< s₁} {{𝕂 : Kit}} → ⟦ d ⟧ (Tm d s') µ₁ M → µ₁ –[ 𝕂 ]→ s₂ ; µ₂ → ⟦ d ⟧ (Tm d (s' ⊔ˢ s₂)) µ₂ M
  -- --     trav⟦⟧ {`σ A dA}  (a , t')  f = a , {!trav⟦⟧ {dA a} t' !} -- doesn't work because we have Tm inside the ⟦⟧ of t'
  -- --     trav⟦⟧ {`X µ M d} (t' , t) f = {!!}
  -- --     trav⟦⟧ {`■ _}     t        f = t

  -- KitTraversal.⋯-var trav t f = refl
