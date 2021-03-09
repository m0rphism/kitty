open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Kit
    (VarKind  : Set)
    (TermKind : Set)
    (k→K      : VarKind → TermKind)
    (_⊢_      : List VarKind → TermKind → Set)
    (`_       : ∀ {κ k} → k ∈ κ → κ ⊢ k→K k)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id)

private
  variable
    k k' k₁ k₂    : VarKind
    κ κ' κ₁ κ₂ κ₃ : List VarKind
    K K' K₁ K₂    : TermKind
    x y z         : k ∈ κ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

Stuff : Set → Set₁
Stuff StuffKind = List VarKind → StuffKind → Set

postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

fun-ext₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

infix  4  _∋_

_∋_ : List A → A → Set _
xs ∋ x = x ∈ xs

record Kit : Set₁ where
  infix   4  _◆_
  infixl  5  _,ₖ_
  infixl  6  _↑_
  field
    StuffKind : Set
    _◆_       : Stuff StuffKind
    k→SK      : VarKind → StuffKind
    SK→K      : StuffKind → TermKind
    vr        : ∀ k → κ ∋ k → κ ◆ (k→SK k)
    tm        : ∀ SK → κ ◆ SK → κ ⊢ SK→K SK
    wk        : ∀ SK → κ ◆ SK → (k' ∷ κ) ◆ SK
    k→SK→K    : ∀ k → SK→K (k→SK k) ≡ k→K k
    wk-vr     : ∀ k' (x : κ ∋ k) → wk {k' = k'} _ (vr _ x) ≡ vr _ (there x)
    tm-vr     : ∀ (x : κ ∋ k) → subst (κ ⊢_) (k→SK→K k) (tm _ (vr _ x)) ≡ ` x

  _–→_ : List VarKind → List VarKind → Set
  _–→_ κ₁ κ₂ = ∀ k → κ₁ ∋ k → κ₂ ◆ k→SK k

  tm' : ∀ {κ k} → κ ◆ k→SK k → κ ⊢ k→K k
  tm' {κ} {k} t = subst (κ ⊢_) (k→SK→K k) (tm _ t)

  idₖ : κ –→ κ
  idₖ = λ _ x → vr _ x

  _↑_ : κ₁ –→ κ₂ → (k : VarKind) → (k ∷ κ₁) –→ (k ∷ κ₂)
  (f ↑ k) _ (here p)  = vr _ (here p)
  (f ↑ k) _ (there x) = wk _ (f _ x)

  id↑≡id : ∀ k κ → idₖ {κ = κ} ↑ k ≡ idₖ {κ = k ∷ κ}
  id↑≡id k κ = fun-ext₂ λ where
    _ (here _)  → refl
    _ (there x) → wk-vr k x

  _,ₖ_ : κ₁ –→ κ₂ → κ₂ ◆ k→SK k → (k ∷ κ₁) –→ κ₂
  (f ,ₖ t) _ (here refl) = t
  (f ,ₖ t) _ (there x)   = f _ x

  ⦅_⦆ : κ ◆ k→SK k → (k ∷ κ) –→ κ
  ⦅ v ⦆ = idₖ ,ₖ v

open Kit {{...}}

_◆[_]_ : List VarKind → (𝕂 : Kit) → Kit.StuffKind 𝕂 → Set
κ ◆[ 𝕂 ] sk = Kit._◆_ 𝕂 κ sk

_–[_]→_ : List VarKind → (_ : Kit) → List VarKind → Set _
κ₁ –[ 𝕂 ]→ κ₂ = Kit._–→_ 𝕂 κ₁ κ₂

record KitTraversal : Set₁ where
  infixl  5  _⋯_  _⋯ᵣ_  _⋯ₛ_
  field
    _⋯_   : ∀ {{𝕂 : Kit}} →
            κ₁ ⊢ K → κ₁ –[ 𝕂 ]→ κ₂ → κ₂ ⊢ K
    ⋯-var : ∀ {{𝕂 : Kit}} (x : κ₁ ∋ k) (f : κ₁ –→ κ₂) →
            (` x) ⋯ f ≡ subst (κ₂ ⊢_) (k→SK→K k) (tm _ (f _ x))

  -- TODO: This could also be defined outside of KitTraversal.
  kitᵣ : Kit
  Kit.StuffKind kitᵣ = VarKind
  Kit._◆_       kitᵣ = _∋_
  Kit.k→SK      kitᵣ = λ x → x
  Kit.SK→K      kitᵣ = k→K
  Kit.vr        kitᵣ = λ _ x → x
  Kit.tm        kitᵣ = λ _ → `_
  Kit.wk        kitᵣ = λ _ → there
  Kit.k→SK→K    kitᵣ = λ _ → refl
  Kit.wk-vr     kitᵣ = λ _ _ → refl
  Kit.tm-vr     kitᵣ = λ _ → refl

  private instance _ = kitᵣ

  kitₛ : Kit
  Kit.StuffKind kitₛ = TermKind
  Kit._◆_       kitₛ = _⊢_
  Kit.k→SK      kitₛ = k→K
  Kit.SK→K      kitₛ = λ x → x
  Kit.vr        kitₛ = λ _ → `_
  Kit.tm        kitₛ = λ _ x → x
  Kit.wk        kitₛ = λ _ x → x ⋯ wk
  Kit.k→SK→K    kitₛ = λ _ → refl
  Kit.wk-vr     kitₛ = λ _ x → ⋯-var x wk
  Kit.tm-vr     kitₛ = λ x → refl

  private instance _ = kitₛ

  open Kit kitᵣ using () renaming (_–→_ to _→ᵣ_; idₖ to idᵣ; _↑_ to _↑ᵣ_; _,ₖ_ to _,ᵣ_; ⦅_⦆ to ⦅_⦆ᵣ) public
  open Kit kitₛ using () renaming (_–→_ to _→ₛ_; idₖ to idₛ; _↑_ to _↑ₛ_; _,ₖ_ to _,ₛ_; ⦅_⦆ to ⦅_⦆ₛ) public

  -- Alternative without duplication and `R.id` instead of `idᵣ`:
  module R = Kit kitᵣ
  module S = Kit kitₛ

  _⋯ₛ_ : κ₁ ⊢ K → κ₁ →ₛ κ₂ → κ₂ ⊢ K
  _⋯ₛ_ = _⋯_

  _⋯ᵣ_ : κ₁ ⊢ K → κ₁ →ᵣ κ₂ → κ₂ ⊢ K
  _⋯ᵣ_ = _⋯_

  _∘ᵣ_ : {{K : Kit}} → κ₂ –[ K ]→ κ₃ → κ₁ →ᵣ κ₂ → κ₁ –[ K ]→ κ₃
  (f ∘ᵣ ρ) _ x = f _ (ρ _ x)

  _∘ₛ_ : {{K : Kit}} → κ₂ –[ K ]→ κ₃ → κ₁ →ₛ κ₂ → κ₁ →ₛ κ₃
  (f ∘ₛ σ) _ x = σ _ x ⋯ f

  _ᵣ∘ᵣ_ : κ₂ →ᵣ κ₃ → κ₁ →ᵣ κ₂ → κ₁ →ᵣ κ₃
  _ₛ∘ᵣ_ : κ₂ →ₛ κ₃ → κ₁ →ᵣ κ₂ → κ₁ →ₛ κ₃
  _ᵣ∘ₛ_ : κ₂ →ᵣ κ₃ → κ₁ →ₛ κ₂ → κ₁ →ₛ κ₃
  _ₛ∘ₛ_ : κ₂ →ₛ κ₃ → κ₁ →ₛ κ₂ → κ₁ →ₛ κ₃
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_
  _ᵣ∘ₛ_ = _∘ₛ_
  _ₛ∘ₛ_ = _∘ₛ_

open KitTraversal {{...}}
