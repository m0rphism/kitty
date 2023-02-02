open import Kitty.Modes

module Kitty.Kit {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Kitty.Prelude

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

-- fun-ext₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
--              {f g : (x : A₁) → (y : A₂ x) → B x y} →
--     (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
--     f ≡ g
-- fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

infix 4 _~_
_~_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → (f g : (a : A) → (b : B a) → C a b)
  → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ~ g = ∀ a b → f a b ≡ g a b

~-refl :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f : (a : A) → (b : B a) → C a b}
  → f ~ f
~-refl a b = refl

~-sym :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f g : (a : A) → (b : B a) → C a b}
  → f ~ g
  → g ~ f
~-sym f~g a b = sym (f~g a b)

~-trans :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
  → {f g h : (a : A) → (b : B a) → C a b}
  → f ~ g
  → g ~ h
  → f ~ h
~-trans f~g g~h a b = trans (f~g a b) (g~h a b)

module ~-Reasoning where

  infix  3 _~∎
  infixr 2 _~⟨⟩_ step-~ step-~˘
  infix  1 begin~_

  private variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : A → Set ℓ₂
    C : (a : A) → B a → Set ℓ₃
    f g h : (a : A) → (b : B a) → C a b

  begin~_ : f ~ g → f ~ g
  begin~_ x≡y = x≡y

  _~⟨⟩_ :
    ∀ (f {g} : (a : A) → (b : B a) → C a b)
    → f ~ g → f ~ g
  _ ~⟨⟩ x~y = x~y

  step-~ :
    ∀ (f {g h} : (a : A) → (b : B a) → C a b)
    → g ~ h → f ~ g → f ~ h
  step-~ _ g~h f~g = ~-trans f~g g~h

  step-~˘ :
    ∀ (f {g h} : (a : A) → (b : B a) → C a b)
    → g ~ h → g ~ f → f ~ h
  step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

  _~∎ :
    ∀ (f : (a : A) → (b : B a) → C a b)
    → f ~ f
  _~∎ _ = ~-refl

  syntax step-~  f g~h f~g = f ~⟨  f~g ⟩ g~h
  syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

open ~-Reasoning

record Kit : Set₁ where
  infix   4  _∋/⊢_
  infixl  5  _,ₖ_
  infixl  6  _↑_  _↑*_
  infixl  5  _∥_

  field
    VarMode/TermMode : Set
    _∋/⊢_            : List VarMode → VarMode/TermMode → Set 

    id/m→M           : VarMode → VarMode/TermMode
    m→M/id           : VarMode/TermMode → TermMode
    id/m→M/id        : ∀ m → m→M/id (id/m→M m) ≡ m→M m

    id/`             : ∀ m → µ ∋ m → µ ∋/⊢ id/m→M m
    `/id             : ∀ m → µ ∋/⊢ id/m→M m → µ ⊢ m→M m
    id/`/id          : ∀ x → `/id {µ = µ} m (id/` _ x) ≡ ` x

    wk               : ∀ m/M → µ ∋/⊢ m/M → (µ ▷ m') ∋/⊢ m/M
    wk-id/`          : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (id/` _ x) ≡ id/` _ (there x)

  wk* : ∀ SM → µ ∋/⊢ SM → (µ ▷▷ µ') ∋/⊢ SM
  wk* {µ' = []}     m/M x = x
  wk* {µ' = µ' ▷ m} m/M x = wk m/M (wk* m/M x)

  _–→_ : List VarMode → List VarMode → Set
  _–→_ µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢ id/m→M m

  idₖ : µ –→ µ
  idₖ = id/`

  -- TODO: Can we express this as weakened f + ,ₖ ?
  _↑_ : µ₁ –→ µ₂ → ∀ m → (µ₁ ▷ m) –→ (µ₂ ▷ m)
  (ϕ ↑ m) _ (here p)  = id/` _ (here p)
  (ϕ ↑ m) _ (there x) = wk _ (ϕ _ x)

  ~-cong-↑ : {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    ϕ ↑ m ~ ϕ' ↑ m
  ~-cong-↑ ϕ~ϕ' _ (here px) = refl
  ~-cong-↑ ϕ~ϕ' _ (there x) = cong (wk _) (ϕ~ϕ' _ x)

  _↑*_ : µ₁ –→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –→ (µ₂ ▷▷ µ')
  ϕ ↑* []       = ϕ
  ϕ ↑* (µ' ▷ m) = (ϕ ↑* µ') ↑ m

  ~-cong-↑* : {ϕ ϕ' : µ₁ –→ µ₂} →
    ϕ ~ ϕ' →
    ϕ ↑* µ ~ ϕ' ↑* µ
  ~-cong-↑* {µ = []}    ϕ~ϕ' = ϕ~ϕ'
  ~-cong-↑* {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' = ~-cong-↑ (~-cong-↑* ϕ~ϕ')

  id↑~id : ∀ m µ → idₖ {µ = µ} ↑ m ~ idₖ {µ = µ ▷ m}
  id↑~id m µ _ (here _)  = refl
  id↑~id m µ _ (there x) = wk-id/` m x

  id↑*~id : ∀ µ' µ → idₖ {µ = µ} ↑* µ' ~ idₖ {µ = µ ▷▷ µ'}
  id↑*~id []       µ = ~-refl
  id↑*~id (µ' ▷ m) µ =
    begin~
      idₖ ↑* µ' ↑ m
    ~⟨ ~-cong-↑ (id↑*~id µ' µ) ⟩
      idₖ ↑ m
    ~⟨ id↑~id _ _ ⟩
      idₖ
    ~∎

  -- Extending a renaming/substitution
  _,ₖ_ : µ₁ –→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –→ µ₂
  (ϕ ,ₖ t) _ (here refl) = t
  (ϕ ,ₖ t) _ (there x)   = ϕ _ x

  -- Singleton renaming/substitution
  ⦅_⦆ : µ ∋/⊢ id/m→M m → (µ ▷ m) –→ µ
  ⦅ v ⦆ = idₖ ,ₖ v

  -- Empty renaming/substitution
  emptyₖ : [] –→ µ
  emptyₖ _ ()

  -- Singleton renaming/substitution for terms with 1 free variable.
  -- Allows the term to be substituted to have arbitrary free variables.
  -- This is useful for things like pattern matching in combination with `_∥_`,
  -- where a matching substitution needs to be built up piece by piece.
  ⦅_⦆₀ : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
  ⦅ v ⦆₀ = emptyₖ ,ₖ v

  _∥_ : ∀ {µ₁ µ₂ µ} → (µ₁ –→ µ) → (µ₂ –→ µ) → ((µ₁ ▷▷ µ₂) –→ µ)
  _∥_ {µ₂ = []}     σ₁ σ₂ _ x = σ₁ _ x
  _∥_ {µ₂ = µ₂ ▷ _} σ₁ σ₂ _ (here px) = σ₂ _ (here px)
  _∥_ {µ₂ = µ₂ ▷ _} σ₁ σ₂ _ (there x) = (σ₁ ∥ (λ m y → σ₂ m (there y))) _ x

  -- A weakening renaming/substitution
  wk' : µ –→ (µ ▷ m)
  wk' _ x = wk _ (id/` _ x)

  wk'* : µ –→ (µ ▷▷ µ')
  wk'* _ x = wk* _ (id/` _ x)

  idₖ' : µ –→ (µ' ▷▷ µ )
  idₖ' _ x = id/` _ (∈-▷▷ₗ x)  where
    ∈-▷▷ₗ : µ ∋ m → (µ' ▷▷ µ) ∋ m
    ∈-▷▷ₗ (here px) = here px
    ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  idₖ'' : ∀ {µ µ' µ''} → µ –→ (µ' ▷▷ µ ▷▷ µ'')
  idₖ'' {µ} {µ'} {µ''} _ x = wk* {µ' = µ''} _ (id/` _ (∈-▷▷ₗ x))  where
    ∈-▷▷ₗ :  ∀ {µ} {µ'} → µ ∋ m → (µ' ▷▷ µ) ∋ m
    ∈-▷▷ₗ (here px) = here px
    ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- ⦅_⦆' : (µ ▷▷ µ') ∋/⊢ m→[m/M] m → (µ ▷ m ▷▷ µ') –→ (µ ▷▷ µ')
  -- ⦅ v ⦆' = idₖ'' ∥ ⦅ v ⦆₀ ∥ idₖ''
  -- ⦅ v ⦆' = {!!} ∥ ⦅ v ⦆₀ ∥ {!!}
  -- -- ⦅ v ⦆' = (idₖ ∥ ⦅ v ⦆₀) ↑* _

open Kit {{...}}

_∋/⊢[_]_ : List VarMode → (𝕂 : Kit) → Kit.VarMode/TermMode 𝕂 → Set
µ ∋/⊢[ 𝕂 ] sm = Kit._∋/⊢_ 𝕂 µ sm

_–[_]→_ : List VarMode → Kit → List VarMode → Set
µ₁ –[ 𝕂 ]→ µ₂ = Kit._–→_ 𝕂 µ₁ µ₂

record KitTraversal : Set₁ where
  infixl  5  _⋯_  _⋯ᵣ_  _⋯ₛ_

  field
    _⋯_   : ∀ ⦃ 𝕂 : Kit ⦄
            → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (ϕ : µ₁ –→ µ₂)
            → (` x) ⋯ ϕ ≡ `/id _ (ϕ _ x)

  -- TODO: This could also be defined outside of KitTraversal.
  kitᵣ : Kit
  Kit.VarMode/TermMode kitᵣ = VarMode
  Kit._∋/⊢_            kitᵣ = _∋_
  Kit.id/m→M           kitᵣ = λ m → m
  Kit.m→M/id           kitᵣ = m→M
  Kit.id/m→M/id        kitᵣ = λ m → refl
  Kit.id/`             kitᵣ = λ m x → x
  Kit.`/id             kitᵣ = λ m x → ` x
  Kit.id/`/id          kitᵣ = λ x → refl
  Kit.wk               kitᵣ = λ m x → there x
  Kit.wk-id/`          kitᵣ = λ m x → refl

  private instance _ = kitᵣ

  kitₛ : Kit
  Kit.VarMode/TermMode kitₛ = TermMode
  Kit._∋/⊢_            kitₛ = _⊢_
  Kit.id/m→M           kitₛ = m→M
  Kit.m→M/id           kitₛ = λ M → M
  Kit.id/m→M/id        kitₛ = λ m → refl
  Kit.id/`             kitₛ = λ m x → ` x
  Kit.`/id             kitₛ = λ M t → t
  Kit.id/`/id          kitₛ = λ x → refl
  Kit.wk               kitₛ = λ M t → t ⋯ wk
  Kit.wk-id/`          kitₛ = λ m x → ⋯-var x wk

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
  (ϕ ∘ᵣ ρ) _ x = ϕ _ (ρ _ x)

  _∘ₛ_ : {{K : Kit}} → µ₂ –[ K ]→ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  (ϕ ∘ₛ σ) _ x = σ _ x ⋯ ϕ

  _ᵣ∘ᵣ_ : µ₂ →ᵣ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ᵣ µ₃
  _ₛ∘ᵣ_ : µ₂ →ₛ µ₃ → µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ₛ_ : µ₂ →ᵣ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ₛ∘ₛ_ : µ₂ →ₛ µ₃ → µ₁ →ₛ µ₂ → µ₁ →ₛ µ₃
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_
  _ᵣ∘ₛ_ = _∘ₛ_
  _ₛ∘ₛ_ = _∘ₛ_

  _∥ᵣ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ᵣ µ) → (µ₂ →ᵣ µ) → ((µ₁ ▷▷ µ₂) →ᵣ µ)
  _∥ᵣ_ = _∥_

  _∥ₛ_ : ∀ {µ₁ µ₂ µ} → (µ₁ →ₛ µ) → (µ₂ →ₛ µ) → ((µ₁ ▷▷ µ₂) →ₛ µ)
  _∥ₛ_ = _∥_

  toₛ : {{K : Kit}} → µ₁ –[ K ]→ µ₂ → µ₁ →ₛ µ₂
  toₛ ϕ = λ m x → `/id m (ϕ m x)
  -- toₛ ϕ = idₛ ∘ₖ ϕ

  ᵣtoₛ : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  ᵣtoₛ ϕ = toₛ ϕ

  fromᵣ : {{K : Kit}} → µ₁ →ᵣ µ₂ → µ₁ –[ K ]→ µ₂
  fromᵣ ϕ = λ m x → id/` m (ϕ m x)

  ₛfromᵣ : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  ₛfromᵣ ϕ = fromᵣ ϕ

  ₛfromᵣ' : µ₁ →ᵣ µ₂ → µ₁ →ₛ µ₂
  ₛfromᵣ' ϕ = λ m x → ` (ϕ m x)

  toₛ∘fromᵣ : {{K : Kit}} → (ϕ : µ₁ →ᵣ µ₂) → toₛ ⦃ K ⦄ (fromᵣ ⦃ K ⦄ ϕ) ~ ₛfromᵣ ϕ
  toₛ∘fromᵣ ϕ m x = id/`/id (ϕ m x)

  ₛfromᵣ≡ᵣtoₛ : (λ {µ₁} {µ₂} → ₛfromᵣ {µ₁} {µ₂}) ≡ (λ {µ₁} {µ₂} → ᵣtoₛ {µ₁} {µ₂})
  ₛfromᵣ≡ᵣtoₛ = refl

  ₛfromᵣ'≡ᵣtoₛ : (λ {µ₁} {µ₂} → ₛfromᵣ' {µ₁} {µ₂}) ≡ (λ {µ₁} {µ₂} → ᵣtoₛ {µ₁} {µ₂})
  ₛfromᵣ'≡ᵣtoₛ = refl
  
record KitHomotopy (T : KitTraversal) : Set₁ where
  open KitTraversal T
  field
    ~-cong-⋯ :
      ∀ ⦃ 𝕂 : Kit ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂} {t : µ₁ ⊢ M}
      → f ~ g
      → t ⋯ f ≡ t ⋯ g

Extensionality→KitHomotopy : ∀ {T} → Extensionality 0ℓ 0ℓ → KitHomotopy T
Extensionality→KitHomotopy {T} fun-ext =
  let open KitTraversal T in record
  { ~-cong-⋯ = λ f~g → cong (_ ⋯_) (fun-ext (λ m → fun-ext (λ x → f~g m x))) }
