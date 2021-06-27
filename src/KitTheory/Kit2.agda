open import KitTheory.Modes

module KitTheory.Kit2 {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import KitTheory.Prelude
open import Level using (_⊔_)

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

fun-ext₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

data Star {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) : List B → A → A → Set (ℓ₁ ⊔ ℓ₂) where
  [] : ∀ {x} → Star R [] x x
  _∷_ : ∀ {x y z b bs} → R b x y → Star R bs y z → Star R (b ∷ bs) x z

infixr 5 _∷[_]_
pattern _∷[_]_  f b fs = _∷_ {b = b} f fs

fold-star : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b x y → T y) →
  T a → Star R bs a b → T b
fold-star f ta [] = ta
fold-star f ta (rab ∷ rbc) = fold-star f (f _ _ _ ta rab) rbc

fold-star' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b y x → T y) →
  T a → Star R bs b a → T b
fold-star' f ta [] = ta
fold-star' f ta (rab ∷ rbc) = f _ _ _ (fold-star' f ta rbc) rab


record Kit : Set₁ where
  infix   4  _◆_
  infixl  5  _,ₖ_
  infixl  6  _↑_  _↑*_

  field
    StuffMode : Set
    _◆_       : Stuff StuffMode
    m→SM      : VarMode → StuffMode
    SM→M      : StuffMode → TermMode
    vr        : ∀ m → µ ∋ m → µ ◆ m→SM m
    tm        : ∀ m → µ ◆ m→SM m → µ ⊢ m→M m
    wk        : ∀ SM → µ ◆ SM → (m' ∷ µ) ◆ SM
    m→SM→M    : ∀ m → SM→M (m→SM m) ≡ m→M m
    wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
    tm-vr     : ∀ x → tm {µ = µ} m (vr _ x) ≡ ` x

  _–→_ : List VarMode → List VarMode → Set
  _–→_ µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ◆ m→SM m

  idₖ : µ –→ µ
  idₖ = vr

  _↑_ : µ₁ –→ µ₂ → ∀ m → (m ∷ µ₁) –→ (m ∷ µ₂)
  (f ↑ m) _ (here p)  = vr _ (here p)
  (f ↑ m) _ (there x) = wk _ (f _ x)

  _↑*_ : µ₁ –→ µ₂ → ∀ µ' → (µ' ++ µ₁) –→ (µ' ++ µ₂)
  f ↑* []       = f
  f ↑* (m ∷ µ') = (f ↑* µ') ↑ m

  id↑≡id : ∀ m µ → idₖ {µ = µ} ↑ m ≡ idₖ {µ = m ∷ µ}
  id↑≡id m µ = fun-ext₂ λ where
    _ (here _)  → refl
    _ (there x) → wk-vr m x

  id↑*≡id : ∀ µ' µ → idₖ {µ = µ} ↑* µ' ≡ idₖ {µ = µ' ++ µ}
  id↑*≡id [] µ = refl
  id↑*≡id (µ' , m) µ rewrite id↑*≡id µ' µ = id↑≡id m (µ' ++ µ)

  _,ₖ_ : µ₁ –→ µ₂ → µ₂ ◆ m→SM m → (m ∷ µ₁) –→ µ₂
  (f ,ₖ t) _ (here refl) = t
  (f ,ₖ t) _ (there x)   = f _ x

  ⦅_⦆ : µ ◆ m→SM m → (m ∷ µ) –→ µ
  ⦅ v ⦆ = idₖ ,ₖ v

open Kit {{...}}

_◆[_]_ : List VarMode → (𝕂 : Kit) → Kit.StuffMode 𝕂 → Set
µ ◆[ 𝕂 ] sm = Kit._◆_ 𝕂 µ sm

_–[_]→_ : List VarMode → (_ : Kit) → List VarMode → Set _
µ₁ –[ 𝕂 ]→ µ₂ = Kit._–→_ 𝕂 µ₁ µ₂

_–[_]→*_ : List VarMode → (_ : List Kit) → List VarMode → Set _
µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

_↑**_ : {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
[] ↑** µ' = []
(_∷_ {b = 𝕂} f fs) ↑** µ' = (Kit._↑*_ 𝕂 f µ') ∷ (fs ↑** µ')

record KitTraversal : Set₁ where
  infixl  5  _⋯_  _⋯*_  _⋯ᵣ_  _⋯ₛ_

  field
    _⋯_   : ∀ {{𝕂 : Kit}} →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

  _⋯*_ : ∀ {𝕂s : List Kit} →
          µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

  field
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ tm _ (f _ x)
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
          (∀ µ m (x : (µ ++ µ₁) ∋ m) → ` x ⋯* (f ↑** µ) ≡ ` x ⋯* (g ↑** µ)) →
          (t : (µ ++ µ₁) ⊢ M) → t ⋯* (f ↑** µ) ≡ t ⋯* (g ↑** µ)

  -- TODO: This could also be defined outside of KitTraversal.
  kitᵣ : Kit
  Kit.StuffMode kitᵣ = VarMode
  Kit._◆_       kitᵣ = _∋_
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
  Kit._◆_       kitₛ = _⊢_
  Kit.m→SM      kitₛ = m→M
  Kit.SM→M      kitₛ = λ x → x
  Kit.vr        kitₛ = λ _ → `_
  Kit.tm        kitₛ = λ _ x → x
  Kit.wk        kitₛ = λ _ x → x ⋯ wk
  Kit.m→SM→M    kitₛ = λ _ → refl
  Kit.wk-vr     kitₛ = λ _ x → ⋯-var x wk
  Kit.tm-vr     kitₛ = λ x → refl

  private instance _ = kitₛ

  open Kit kitᵣ using () renaming (wk to wkᵣ; _–→_ to _→ᵣ_; idₖ to idᵣ; _↑_ to _↑ᵣ_; _,ₖ_ to _,ᵣ_; ⦅_⦆ to ⦅_⦆ᵣ) public
  open Kit kitₛ using () renaming (wk to wkₛ; _–→_ to _→ₛ_; idₖ to idₛ; _↑_ to _↑ₛ_; _,ₖ_ to _,ₛ_; ⦅_⦆ to ⦅_⦆ₛ) public

  -- Alternative without duplication and `R.id` instead of `idᵣ`:
  module R = Kit kitᵣ
  module S = Kit kitₛ

  _⋯ₛ_ : µ₁ ⊢ M → µ₁ →ₛ µ₂ → µ₂ ⊢ M
  _⋯ₛ_ = _⋯_

  _⋯ᵣ_ : µ₁ ⊢ M → µ₁ →ᵣ µ₂ → µ₂ ⊢ M
  _⋯ᵣ_ = _⋯_

  _∘ᵣ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₃
  (f ∘ᵣ ρ) _ x = f _ (ρ _ x)

  _∘ₛ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  (f ∘ₛ σ) _ x = σ _ x ⋯ f

  _ᵣ∘ᵣ_ : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
  _ₛ∘ᵣ_ : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ₛ_ : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ₛ∘ₛ_ : µ₂ →ₛ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_
  _ᵣ∘ₛ_ = _∘ₛ_
  _ₛ∘ₛ_ = _∘ₛ_
