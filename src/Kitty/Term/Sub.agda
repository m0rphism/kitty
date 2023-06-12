open import Kitty.Term.Terms

module Kitty.Term.Sub (𝕋 : Terms) where

open import Level renaming (suc to lsuc)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open Terms 𝕋
open Kit ⦃ … ⦄
open _⊑ₖ_ ⦃ … ⦄

private variable
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

record Sub ℓ : Set (lsuc ℓ) where
  infixl  12  _,ₖ_
  infixl  11  _↑_  _↑*_
  infixl  9  _∥_
  infixl  8  _&_
  infix   4  _~_  _~'_

  field
    _–[_]→_ : SortCtx → Kit _∋/⊢_ → SortCtx → Set ℓ

    []ₖ  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ → [] –[ 𝕂 ]→ []
    _,ₖ_ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → S₁ –[ 𝕂 ]→ S₂ → S₂ ∋/⊢[ 𝕂 ] s → (S₁ ▷ s) –[ 𝕂 ]→ S₂
    wkₖ  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} s → S₁ –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ (S₂ ▷ s)
    wkₖ* : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S → S₁ –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ (S₂ ▷▷ S)
    _↑_  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂 ]→ S₂ → ∀ s → (S₁ ▷ s) –[ 𝕂 ]→ (S₂ ▷ s)
    _↑*_ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂 ]→ S₂ → ∀ S' → (S₁ ▷▷ S') –[ 𝕂 ]→ (S₂ ▷▷ S')
    id   : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} → S –[ 𝕂 ]→ S
    []*  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₂} → [] –[ 𝕂 ]→ S₂
    _↓   : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → (S₁ ▷ s) –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ S₂
    -- TODO: we might want this also to be Kit-heterogenous, to allow for talking about
    -- parallel compositions of two unknown, potentially different Kits.
    _∥_  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ S} → (S₁ –[ 𝕂 ]→ S) → (S₂ –[ 𝕂 ]→ S) → ((S₁ ▷▷ S₂) –[ 𝕂 ]→ S)
    ⦅_⦆  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s} → S ∋/⊢ s → (S ▷ s) –[ 𝕂 ]→ S
    -- Singleton renaming/substitution for terms with 1 free variable.
    -- Allows the term to be substituted to have arbitrary free variables.
    -- This is useful for things like pattern matching in combination with `_∥_`,
    -- where a matching substitution needs to be built up piece by piece.
    ⦅_⦆₀ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s} → S ∋/⊢ s → ([] ▷ s) –[ 𝕂 ]→ S

    _&_  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → S₁ ∋ s → S₁ –[ 𝕂 ]→ S₂ → S₂ ∋/⊢ s

    ι-→ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {S₁} {S₂} → S₁ –[ 𝕂₁ ]→ S₂ → S₁ –[ 𝕂₂ ]→ S₂

  -- Renaming/Substitution

  _–→_ : ⦃ 𝕂 : Kit _∋/⊢_ ⦄ → SortCtx → SortCtx → Set ℓ
  _–→_ ⦃ 𝕂 ⦄ S₁ S₂ = S₁ –[ 𝕂 ]→ S₂

  -- Extensional Equality

  -- Unused, because when we use it, we get horrible, horrible names....
  module Heterogeneous-~
      {ℓ}
      (P : ∀ {_∋/⊢_ : VarScoped} (𝕂 : Kit _∋/⊢_) → Set ℓ)
      (R : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
             (ϕ₁ : P 𝕂₁) (ϕ₂ : P 𝕂₂) → Set)
      (R-refl : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {ϕ : P 𝕂} → R ϕ ϕ)
      (R-sym  : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
                  {ϕ₁ : P 𝕂₁} {ϕ₂ : P 𝕂₂}
                → R ϕ₁ ϕ₂ → R ϕ₂ ϕ₁)
      (R-trans : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} {_∋/⊢₃_ : VarScoped}
                   ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄
                   {ϕ₁ : P 𝕂₁} {ϕ₂ : P 𝕂₂} {ϕ₃ : P 𝕂₃}
                → R ϕ₁ ϕ₂ → R ϕ₂ ϕ₃ → R ϕ₁ ϕ₃)
      where

    record _~_ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped}
               ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
               (ϕ₁ : P 𝕂₁) (ϕ₂ : P 𝕂₂) : Set where
      constructor mk-~
      field
        use-~ : R ϕ₁ ϕ₂
    open _~_

    ~-refl :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {f : P 𝕂}
      → f ~ f
    ~-refl = mk-~ R-refl

    ~-sym :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {f : P 𝕂₁} {g : P 𝕂₂}
      → f ~ g
      → g ~ f
    ~-sym f~g = mk-~ (R-sym (use-~ f~g))

    ~-trans :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ {f : P 𝕂₁} {g : P 𝕂₂} {h : P 𝕂₃}
      → f ~ g
      → g ~ h
      → f ~ h
    ~-trans f~g g~h = mk-~ (R-trans (use-~ f~g) (use-~ g~h))

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      ⦃ 𝕂 ⦄ : Kit _∋/⊢_
      f g h : P 𝕂

    begin~_ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {f : P 𝕂₁} {g : P 𝕂₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ (f : P 𝕂₁) {g : P 𝕂₂}
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ (f : P 𝕂₁) {g : P 𝕂₂} {h : P 𝕂₃}
      → g ~ h → f ~ g → f ~ h
    step-~ f g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ (f : P 𝕂₁) {g : P 𝕂₂} {h : P 𝕂₃}
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ (f : P 𝕂₁) {g : P 𝕂₁} {h : P 𝕂₂}
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f : P 𝕂)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

  infix  4  _~ₜ_

  _~ₜ_ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S} {s} → S ∋/⊢[ 𝕂₁ ] s → S ∋/⊢[ 𝕂₂ ] s → Set
  _~ₜ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {S} {s} x/t₁ x/t₂ =
    `/id x/t₁ ≡ `/id x/t₂
  -- _~ₜ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {S} {s} x/t₁ x/t₂ =
  --   let eq = m→M/id (id/m→M ⦃ 𝕂₁ ⦄ m) ≡⟨ id/m→M/id m ⟩
  --            m→M m                    ≡⟨ sym (id/m→M/id m) ⟩
  --            m→M/id (id/m→M ⦃ 𝕂₂ ⦄ m) ∎
  --   in x/t₁ ~ₜ[ eq ] x/t₂

  -- module Test where
  --   module Terms-~ {S} {m} where
  --     open Heterogeneous-~ (λ 𝕂 → S ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m) _~ₜ_ refl sym trans public
  --       renaming (_~_ to _~ᵗ_)
  --   open Terms-~
  --   test : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} {m} (ϕ : S ∋/⊢[ 𝕂 ] id/m→M ⦃ 𝕂 ⦄ m) → ϕ ~ᵗ ϕ
  --   test ϕ =
  --     ϕ ~⟨ {!!} ⟩
  --     ϕ ~∎


  -- Helps with inferring ϕ₁ and ϕ₂ from implicits
  record _~_ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂) (ϕ₂ : S₁ –[ 𝕂₂ ]→ S₂) : Set where
    constructor mk-~
    field
      use-~ : ∀ s (x : _ ∋ s) → x & ϕ₁ ~ₜ x & ϕ₂
  open _~_ public

  -- Helps with inferring ϕ₁ and ϕ₂ from implicits
  record _~'_ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ₁ : S₁ –[ 𝕂 ]→ S₂) (ϕ₂ : S₁ –[ 𝕂 ]→ S₂) : Set where
    constructor mk-~'
    field
      use-~' : ∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂
  open _~'_ public

  -- _~_ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂₁ ]→ S₂ → S₁ –[ 𝕂₂ ]→ S₂ → Set
  -- ϕ₁ ~ ϕ₂ = ∀ s (x : _ ∋ s) → x & ϕ₁ ~ₜ x & ϕ₂
  -- -- ϕ₁ ~ ϕ₂ = ∀ s x → `/id (& ϕ₁ s x) ≡ `/id (& ϕ₂ s x)

  -- _~'_ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ 𝕂 ]→ S₂ → S₁ –[ 𝕂 ]→ S₂ → Set
  -- ϕ₁ ~' ϕ₂ = ∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂

  ~→~' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ 𝕂 ]→ S₂}
         → ϕ₁ ~ ϕ₂
         → ϕ₁ ~' ϕ₂
  ~→~' ϕ₁~ϕ₂ = mk-~' (λ s x → `/id-injective (use-~ ϕ₁~ϕ₂ s x))

  ~'→~ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ 𝕂 ]→ S₂}
         → ϕ₁ ~' ϕ₂
         → ϕ₁ ~ ϕ₂
  ~'→~ ϕ₁~'ϕ₂ = mk-~ (λ s x → cong `/id (use-~' ϕ₁~'ϕ₂ s x))

  use-~-hom :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ 𝕂 ]→ S₂}
    → ϕ₁ ~ ϕ₂
    → (∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂)
  use-~-hom ϕ₁~ϕ₂ = use-~' (~→~' ϕ₁~ϕ₂)

  ~ₜ-refl :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} {s} {x/t : S ∋/⊢[ 𝕂 ] s}
    → x/t ~ₜ x/t
  ~ₜ-refl = cong (`/id) refl

  ~ₓ-refl :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S} {s} {x : S ∋ s}
    → id/` ⦃ 𝕂₁ ⦄ x ~ₜ id/` ⦃ 𝕂₂ ⦄ x
  ~ₓ-refl ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {x = x} =
    `/id ⦃ 𝕂₁ ⦄ (id/` x) ≡⟨ id/`/id ⦃ 𝕂₁ ⦄ x ⟩
    ` x                  ≡⟨ sym (id/`/id ⦃ 𝕂₂ ⦄ x) ⟩
    `/id ⦃ 𝕂₂ ⦄ (id/` x) ∎

  ~-refl :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f : S₁ –[ 𝕂 ]→ S₂}
    → f ~ f
  ~-refl = mk-~ (λ a b → refl)

  ~-sym :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂}
    → f ~ g
    → g ~ f
  ~-sym f~g = mk-~ (λ a b → sym (use-~ f~g a b))

  ~-trans :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ {S₁} {S₂} {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂} {h : S₁ –[ 𝕂₃ ]→ S₂}
    → f ~ g
    → g ~ h
    → f ~ h
  ~-trans f~g g~h = mk-~ (λ a b → trans (use-~ f~g a b) (use-~ g~h a b))

  ~-cong-subst-S₁ :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₁'} {S₂} {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂} (eq : S₁ ≡ S₁')
    → f ~ g
    → subst (_–[ 𝕂₁ ]→ S₂) eq f ~ subst (_–[ 𝕂₂ ]→ S₂) eq g
  ~-cong-subst-S₁ refl f~g = f~g

  ~-cong-subst-S₂ :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {S₂'} {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂} (eq : S₂ ≡ S₂')
    → f ~ g
    → subst (S₁ –[ 𝕂₁ ]→_) eq f ~ subst (S₁ –[ 𝕂₂ ]→_) eq g
  ~-cong-subst-S₂ refl f~g = f~g

  ~-cong-subst₂ :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₁'} {S₂} {S₂'} {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂} (eq₁ : S₁ ≡ S₁') (eq₂ : S₂ ≡ S₂')
    → f ~ g
    → subst₂ (_–[ 𝕂₁ ]→_) eq₁ eq₂ f ~ subst₂ (_–[ 𝕂₂ ]→_) eq₁ eq₂ g
  ~-cong-subst₂ refl refl f~g = f~g

  module ~-Reasoning where

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      S₁ S₂ S₃ : SortCtx
      ⦃ 𝕂 ⦄ : Kit _∋/⊢_
      f g h : S₁ –[ 𝕂 ]→ S₂

    begin~_ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {f : S₁ –[ 𝕂₁ ]→ S₂} {g : S₁ –[ 𝕂₂ ]→ S₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ (f : S₁ –[ 𝕂₁ ]→ S₂) {g : S₁ –[ 𝕂₂ ]→ S₂}
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ (f : S₁ –[ 𝕂₁ ]→ S₂) {g : S₁ –[ 𝕂₂ ]→ S₂} {h : S₁ –[ 𝕂₃ ]→ S₂}
      → g ~ h → f ~ g → f ~ h
    step-~ f g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄ (f : S₁ –[ 𝕂₁ ]→ S₂) {g : S₁ –[ 𝕂₂ ]→ S₂} {h : S₁ –[ 𝕂₃ ]→ S₂}
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ (f : S₁ –[ 𝕂₁ ]→ S₂) {g : S₁ –[ 𝕂₁ ]→ S₂} {h : S₁ –[ 𝕂₂ ]→ S₂}
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f : S₁ –[ 𝕂 ]→ S₂)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

  ~'-refl :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f : S₁ –[ 𝕂 ]→ S₂}
    → f ~' f
  ~'-refl = mk-~' λ a b → refl

  ~'-sym :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f g : S₁ –[ 𝕂 ]→ S₂}
    → f ~' g
    → g ~' f
  ~'-sym f~'g = mk-~' λ a b → sym (use-~' f~'g a b)

  ~'-trans :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f g h : S₁ –[ 𝕂 ]→ S₂} 
    → f ~' g
    → g ~' h
    → f ~' h
  ~'-trans f~'g g~'h = mk-~' λ a b → trans (use-~' f~'g a b) (use-~' g~'h a b)

  ~'-cong-subst-S₁ :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₁'} {S₂} {f g : S₁ –[ 𝕂 ]→ S₂} (eq : S₁ ≡ S₁')
    → f ~' g
    → subst (_–[ 𝕂 ]→ S₂) eq f ~' subst (_–[ 𝕂 ]→ S₂) eq g
  ~'-cong-subst-S₁ refl f~'g = f~'g

  ~'-cong-subst-S₂ :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S₂'} {f g : S₁ –[ 𝕂 ]→ S₂} (eq : S₂ ≡ S₂')
    → f ~' g
    → subst (S₁ –[ 𝕂 ]→_) eq f ~' subst (S₁ –[ 𝕂 ]→_) eq g
  ~'-cong-subst-S₂ refl f~'g = f~'g

  module ~'-Reasoning where

    infix  3 _~'∎
    infixr 2 _~'⟨⟩_ step-~' step-~'˘ step-~'≡
    infix  1 begin~'_

    private variable
      S₁ S₂ S₃ : SortCtx
      ⦃ 𝕂 ⦄ : Kit _∋/⊢_
      f g h : S₁ –[ 𝕂 ]→ S₂

    begin~'_ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {f g : S₁ –[ 𝕂 ]→ S₂}
      → f ~' g → f ~' g
    begin~'_ x≡y = x≡y

    _~'⟨⟩_ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f {g} : S₁ –[ 𝕂 ]→ S₂)
      → f ~' g → f ~' g
    _ ~'⟨⟩ x~'y = x~'y

    step-~' :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ 𝕂 ]→ S₂)
      → g ~' h → f ~' g → f ~' h
    step-~' _ g~'h f~'g = ~'-trans f~'g g~'h

    step-~'˘ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ 𝕂 ]→ S₂)
      → g ~' h → g ~' f → f ~' h
    step-~'˘ _ g~'h g~'f = ~'-trans (~'-sym g~'f) g~'h

    step-~'≡ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ 𝕂 ]→ S₂)
      → g ~' h → f ≡ g → f ~' h
    step-~'≡ f g~'h f≡g = ~'-trans (subst (f ~'_) f≡g ~'-refl ) g~'h

    _~'∎ :
      ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (f : S₁ –[ 𝕂 ]→ S₂)
      → f ~' f
    _~'∎ _ = ~'-refl

    syntax step-~'  f g~'h f~'g = f ~'⟨ f~'g ⟩ g~'h
    syntax step-~'≡  f g~'h f≡g = f ~'≡⟨ f≡g ⟩ g~'h
    syntax step-~'˘ f g~'h g~'f = f ~'˘⟨ g~'f ⟩ g~'h

  data Invert-ϕ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₂} : {S₁ : SortCtx} → S₁ –[ 𝕂 ]→ S₂ → Set ℓ where
    ϕ~[]* : ∀ {ϕ} →
      ϕ ~ []* →
      Invert-ϕ ϕ
    ϕ~,ₖ : ∀ {S₁' s₁ ϕ} →
      (ϕ' : S₁' –[ 𝕂 ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      ϕ ~ (ϕ' ,ₖ x/t) →
      Invert-ϕ ϕ

  data Invert-ϕ' ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) : Set ℓ where
    ϕ~[]* :
      (eq : S₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ S₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ' ϕ
    ϕ~,ₖ : ∀ {S₁' s₁} →
      (eq : S₁ ≡ S₁' ▷ s₁) →
      (ϕ' : S₁' –[ 𝕂 ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      let sub = subst (_–[ 𝕂 ]→ S₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      Invert-ϕ' ϕ

  data Invert-ϕ'-Rec ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) : S₁ –[ 𝕂 ]→ S₂ → Set ℓ where
    ϕ~[]* :
      (eq : S₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ S₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ'-Rec ϕ (sub []*)
    ϕ~,ₖ : ∀ {S₁' s₁} →
      (eq : S₁ ≡ S₁' ▷ s₁) →
      (ϕ' : S₁' –[ 𝕂 ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      (ϕ'' : S₁' –[ 𝕂 ]→ S₂) →
      Invert-ϕ'-Rec ϕ' ϕ'' →
      let sub = subst (_–[ 𝕂 ]→ S₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      ϕ ~ sub (ϕ'' ,ₖ x/t) →
      Invert-ϕ'-Rec ϕ (sub (ϕ'' ,ₖ x/t))

  invert-ϕ'→ϕ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  invert-ϕ'→ϕ (ϕ~[]* refl ϕ~) = ϕ~[]* ϕ~
  invert-ϕ'→ϕ (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

  -- -- requires dependent subst
  -- invert-ϕ'→ϕ' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  -- invert-ϕ'→ϕ' {S₁} {S₂} {ϕ} (ϕ~[]* S₁≡[] ϕ~) = {!subst₂ (λ ■ ■' → Invert-ϕ {S₁ = ■} ■') ? ? {!ϕ~[]* ϕ~!}!}
  -- invert-ϕ'→ϕ' (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

_–[_;_]→_ : ∀ {ℓ} → SortCtx → Kit _∋/⊢_ → Sub ℓ → SortCtx → Set ℓ
_–[_;_]→_ S₁ 𝕂 𝕊 S₂ = Sub._–[_]→_ 𝕊 S₁ 𝕂 S₂

record SubWithLaws ℓ : Set (lsuc ℓ) where
  field
    ⦃ SubWithLaws-Sub ⦄ : Sub ℓ

  open Sub SubWithLaws-Sub

  field

    &-,ₖ-here : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s)
                  → here refl & (ϕ ,ₖ x/t) ≡ x/t
    &-,ₖ-there : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s) {s'} (x : S₁ ∋ s')
                   → there x & (ϕ ,ₖ x/t) ≡ x & ϕ

    &-wkₖ-wk : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x : S₁ ∋ s')
                 → x & wkₖ s ϕ ≡ wk s (x & ϕ)

    &-↓ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : (S₁ ▷ s) –[ 𝕂 ]→ S₂) (x : S₁ ∋ s')
      → x & (ϕ ↓) ≡ there x & ϕ

    wkₖ*-[] : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂)
      → wkₖ* [] ϕ ~ ϕ
    wkₖ*-▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ 𝕂 ]→ S₂)
      → wkₖ* (S ▷ s) ϕ ~ wkₖ s (wkₖ* S ϕ)

    ↑-,ₖ  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) s
      → (ϕ ↑ s) ~ (wkₖ s ϕ ,ₖ id/` (here refl))

    ↑*-[]  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂)
      → (ϕ ↑* []) ~ ϕ

    ↑*-▷  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ 𝕂 ]→ S₂)
      → (ϕ ↑* (S ▷ s)) ~ ((ϕ ↑* S) ↑ s)

    id-[] : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      → id {S = []} ~ []ₖ

    id-▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s}
      → id {S = S ▷ s} ~ (id {S = S} ↑ s)

    []*-[]  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      → []* {S₂ = []} ~ []ₖ

    []*-▷  : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s}
      → []* {S₂ = S ▷ s} ~ wkₖ s ([]* {S₂ = S})

    ↓-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s)
      → ((ϕ ,ₖ x/t) ↓) ~ ϕ

    ∥-[] : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S} → (ϕ₁ : S₁ –[ 𝕂 ]→ S) → (ϕ₂ : [] –[ 𝕂 ]→ S)
      → (ϕ₁ ∥ ϕ₂) ~ ϕ₁

    ∥-▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ S s} → (ϕ₁ : S₁ –[ 𝕂 ]→ S) → (ϕ₂ : (S₂ ▷ s) –[ 𝕂 ]→ S)
      → (ϕ₁ ∥ ϕ₂) ~ ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂))

    ⦅⦆-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s} (x/t : S ∋/⊢ s) →
      ⦅ x/t ⦆ ~ (id ,ₖ x/t)

    ⦅⦆₀-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S s} (x/t : S ∋/⊢ s) →
      ⦅ x/t ⦆₀ ~ ([]* ,ₖ x/t)

    invert' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) → Invert-ϕ' ϕ

    &-ι-→ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ 𝕂₁ ]→ S₂) (x : S₁ ∋ s)
            → x & (ι-→ ϕ) ≡ ι-∋/⊢ (x & ϕ)

  open ~-Reasoning

  ~-ι-→ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂₁ ]→ S₂)
          → ι-→ ϕ ~ ϕ
  ~-ι-→ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ ⦄ {S₁} {S₂} ϕ = mk-~ λ s x →
    `/id (x & ι-→ ϕ)     ≡⟨ cong `/id (&-ι-→ ϕ x) ⟩
    `/id (ι-∋/⊢ (x & ϕ)) ≡⟨ sym (ι-`/id (x & ϕ)) ⟩
    `/id (x & ϕ)         ∎

  &-id : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S} {s} (x : S ∋ s)
           → x & id {S = S} ≡ id/` x
  &-id ⦃ 𝕂 ⦄ {S ▷ s'} {s} x@(here refl) =
    x & (id {S = S ▷ s'})              ≡⟨ use-~-hom id-▷ s' x ⟩
    x & (id {S = S} ↑ s')              ≡⟨ use-~-hom (↑-,ₖ id s') _ x ⟩
    x & (wkₖ _ (id {S = S}) ,ₖ id/` x) ≡⟨ &-,ₖ-here (wkₖ _ (id {S = S})) (id/` x) ⟩
    id/` x                             ∎
  &-id ⦃ 𝕂 ⦄ {S ▷ s'} {s} (there x) =
    there x & (id {S = S ▷ s'})                        ≡⟨ use-~-hom id-▷ _ (there x) ⟩
    there x & (id {S = S} ↑ s')                        ≡⟨ use-~-hom (↑-,ₖ id s') _ (there x) ⟩
    there x & (wkₖ _ (id {S = S}) ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ _ (id {S = S})) (id/` (here refl)) x ⟩
    x & (wkₖ _ (id {S = S}))                           ≡⟨ &-wkₖ-wk id x ⟩
    wk s' (x & id {S = S})                             ≡⟨ cong (wk s') (&-id x) ⟩
    wk s' (id/` x)                                     ≡⟨ wk-id/` s' x ⟩
    id/` (there x)                                     ∎

  -- id-▷▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S S'}
  --   → id {S ▷▷ S'} ~ (id {S} ↑* S')
  -- id-▷▷ {S' = []} = ~-sym (↑*-[] id)
  -- id-▷▷ {S' = S' ▷ s} = ~-trans {!id-▷▷!} (~-trans {!id-▷!} (~-sym (↑*-▷ S' s id)))

  &-↑-here :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ 𝕂 ]→ S₂)
    → here refl & (ϕ ↑ s) ≡ id/` (here refl)
  &-↑-here ⦃ 𝕂 ⦄ {S₁} {S₂} {s} ϕ =
    here refl & (ϕ ↑ s)                       ≡⟨ use-~-hom (↑-,ₖ ϕ s) s (here refl) ⟩
    here refl & (wkₖ s ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-here (wkₖ s ϕ) _ ⟩
    id/` (here refl)                          ∎

  &-↑-there :
    ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x : S₁ ∋ s')
    → there x & (ϕ ↑ s) ≡ wk s (x & ϕ)
  &-↑-there ⦃ 𝕂 ⦄ {S₁} {S₂} {s} {s'} ϕ x =
    there x & (ϕ ↑ s)                       ≡⟨ use-~-hom (↑-,ₖ ϕ s) s' (there x) ⟩
    there x & (wkₖ s ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ s ϕ) _ x ⟩
    x & wkₖ s ϕ                             ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk s (x & ϕ)                            ∎

  -- Weakening preserves Homotopy

  ~'-cong-wk : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
    ϕ ~' ϕ' →
    wkₖ s ϕ ~' wkₖ s ϕ'
  ~'-cong-wk {S₁ = S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~' λ sx x →
    x & wkₖ _ ϕ   ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk _ (x & ϕ)  ≡⟨ cong (wk _) (use-~' ϕ~ϕ' sx x) ⟩
    wk _ (x & ϕ') ≡⟨ sym (&-wkₖ-wk ϕ' x) ⟩
    x & wkₖ _ ϕ'  ∎

  ~-cong-wk' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
    ϕ ~ ϕ' →
    wkₖ s ϕ ~ wkₖ s ϕ'
  ~-cong-wk' ϕ~ϕ' = ~'→~ (~'-cong-wk (~→~' ϕ~ϕ'))

  ~-cong-wk*' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
    ϕ ~ ϕ' →
    wkₖ* S ϕ ~ wkₖ* S ϕ'
  ~-cong-wk*' {S = []} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
    wkₖ* [] ϕ' ~∎
  ~-cong-wk*' {S = S ▷ s} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* (S ▷ s) ϕ    ~⟨ wkₖ*-▷ S s ϕ ⟩
    wkₖ s (wkₖ* S ϕ)  ~⟨ ~-cong-wk' (~-cong-wk*' ϕ~ϕ') ⟩
    wkₖ s (wkₖ* S ϕ') ~⟨ ~-sym (wkₖ*-▷ S s ϕ') ⟩
    wkₖ* (S ▷ s) ϕ'   ~∎

  -- Lifting preserves Homotopy

  ~-cong-,ₖ : ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {s}
    {ϕ : S₁ –[ 𝕂₁ ]→ S₂} {ϕ' : S₁ –[ 𝕂₂ ]→ S₂}
    {x/t : S₂ ∋/⊢[ 𝕂₁ ] s} {x/t' : S₂ ∋/⊢[ 𝕂₂ ] s} →
    ϕ ~ ϕ' →
    x/t ~ₜ x/t' →
    (ϕ ,ₖ x/t) ~ (ϕ' ,ₖ x/t')
  ~-cong-,ₖ {S₁ = S₁} {S₂} {_} {ϕ} {ϕ'} {x/t} {x/t'} ϕ~ϕ' x/t≡x/t' = mk-~ λ where
    sx x@(here refl) →
      `/id (x & (ϕ ,ₖ x/t))   ≡⟨ cong (`/id) (&-,ₖ-here ϕ x/t) ⟩
      `/id x/t                ≡⟨ x/t≡x/t' ⟩
      `/id x/t'               ≡⟨ cong (`/id) (sym (&-,ₖ-here ϕ' x/t')) ⟩
      `/id (x & (ϕ' ,ₖ x/t')) ∎
    sx x@(there y) →
      `/id (x & (ϕ ,ₖ x/t))   ≡⟨ cong (`/id) (&-,ₖ-there ϕ x/t y) ⟩
      `/id (y & ϕ)            ≡⟨ use-~ ϕ~ϕ' sx y ⟩
      `/id (y & ϕ')           ≡⟨ cong (`/id) (sym (&-,ₖ-there ϕ' x/t' y)) ⟩
      `/id (x & (ϕ' ,ₖ x/t')) ∎

  ~'-cong-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ ϕ' : S₁ –[ 𝕂 ]→ S₂} {x/t x/t' : S₂ ∋/⊢[ 𝕂 ] s} →
    ϕ ~' ϕ' →
    x/t ≡ x/t' →
    (ϕ ,ₖ x/t) ~' (ϕ' ,ₖ x/t')
  ~'-cong-,ₖ ϕ~ϕ' x/t≡x/t' = ~→~' (~-cong-,ₖ (~'→~ ϕ~ϕ') (cong (`/id) x/t≡x/t'))

  ~-cong-↓ :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {s} {ϕ : (S₁ ▷ s) –[ 𝕂₁ ]→ S₂} {ϕ' : (S₁ ▷ s) –[ 𝕂₂ ]→ S₂} →
    ϕ ~ ϕ' →
    (ϕ ↓) ~ (ϕ' ↓)
  ~-cong-↓ ⦃ 𝕂 ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~ λ sx x →
    `/id (x & (ϕ  ↓))   ≡⟨ cong (`/id) (&-↓ ϕ x) ⟩
    `/id (there x & ϕ ) ≡⟨ use-~ ϕ~ϕ' sx (there x) ⟩
    `/id (there x & ϕ') ≡⟨ cong (`/id) (sym (&-↓ ϕ' x)) ⟩
    `/id (x & (ϕ' ↓))   ∎

  ~-cong-∥ :
    ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S₁₁} {S₁₂} {S₂}
      {ϕ₁  : S₁₁ –[ 𝕂₁ ]→ S₂}
      {ϕ₁' : S₁₁ –[ 𝕂₂ ]→ S₂}
      {ϕ₂  : S₁₂ –[ 𝕂₁ ]→ S₂}
      {ϕ₂' : S₁₂ –[ 𝕂₂ ]→ S₂}
    → ϕ₁ ~ ϕ₁'
    → ϕ₂ ~ ϕ₂'
    → (ϕ₁ ∥ ϕ₂) ~ (ϕ₁' ∥ ϕ₂')
  ~-cong-∥ {S₁₁ = S₁₁} {[]}      {S₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    (ϕ₁ ∥ ϕ₂)   ~⟨ ∥-[] ϕ₁ ϕ₂ ⟩
    ϕ₁          ~⟨ ϕ₁~ϕ₁' ⟩
    ϕ₁'         ~⟨ ~-sym (∥-[] ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎
  ~-cong-∥ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {S₁₁} {S₁₂ ▷ s} {S₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    let sub₁ = subst (_–[ 𝕂₁ ]→ S₂) (sym (++-assoc ([] ▷ s) S₁₂ S₁₁)) in
    let sub₂ = subst (_–[ 𝕂₂ ]→ S₂) (sym (++-assoc ([] ▷ s) S₁₂ S₁₁)) in
    (ϕ₁ ∥ ϕ₂)                                      ~⟨ ∥-▷ ϕ₁ ϕ₂ ⟩
    sub₁ ((ϕ₁  ∥ (ϕ₂  ↓)) ,ₖ (here refl & ϕ₂)) ~⟨ ~-cong-subst-S₁ (sym (++-assoc ([] ▷ s) S₁₂ S₁₁))
                                                      (~-cong-,ₖ (~-cong-∥ ϕ₁~ϕ₁' (~-cong-↓ ϕ₂~ϕ₂'))
                                                                 (use-~ ϕ₂~ϕ₂' _ (here refl))) ⟩
    sub₂ ((ϕ₁' ∥ (ϕ₂' ↓)) ,ₖ (here refl & ϕ₂')) ~⟨ ~-sym (∥-▷ ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎

  invert : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) → Invert-ϕ ϕ
  invert ϕ = invert-ϕ'→ϕ (invert' ϕ)

  invert'-rec : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) → Σ[ ϕ' ∈ S₁ –[ 𝕂 ]→ S₂ ] Invert-ϕ'-Rec ϕ ϕ' × ϕ ~ ϕ'
  invert'-rec ϕ with invert ϕ
  ... | ϕ~[]* ϕ~[] = []* , ϕ~[]* refl ϕ~[] , ϕ~[]
  ... | ϕ~,ₖ ϕ' x/t ϕ~ϕ',x/t with invert'-rec ϕ'
  ...   | ϕ'' , inv , ϕ'~ϕ'' = let ϕ~ϕ'',x/t = ~-trans ϕ~ϕ',x/t (~-cong-,ₖ ϕ'~ϕ'' refl) in
                               (ϕ'' ,ₖ x/t) , ϕ~,ₖ refl ϕ' x/t ϕ'' inv ϕ~ϕ',x/t ϕ~ϕ'',x/t , ϕ~ϕ'',x/t

  ~-cong-↑' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
    ϕ ~ ϕ' →
    (ϕ ↑ s) ~ (ϕ' ↑ s)
  ~-cong-↑' {S₁ = S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' =
    (ϕ ↑ s)                         ~⟨ ↑-,ₖ ϕ s ⟩
    (wkₖ _ ϕ  ,ₖ id/` (here refl))  ~⟨ ~-cong-,ₖ (~-cong-wk' ϕ~ϕ') ~ₓ-refl ⟩
    (wkₖ _ ϕ' ,ₖ id/` (here refl))  ~⟨ ~-sym (↑-,ₖ ϕ' s) ⟩
    (ϕ' ↑ s)                        ~∎

  ~-cong-↑*' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
    ϕ ~ ϕ' →
    (ϕ ↑* S) ~ (ϕ' ↑* S)
  ~-cong-↑*' {S = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
    (ϕ' ↑* []) ~∎
  ~-cong-↑*' {S = S ▷ s} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* (S ▷ s))  ~⟨ ↑*-▷ S s ϕ ⟩
    (ϕ ↑* S) ↑ s    ~⟨ ~-cong-↑' (~-cong-↑*' ϕ~ϕ') ⟩
    (ϕ' ↑* S) ↑ s   ~⟨ ~-sym (↑*-▷ S s ϕ') ⟩
    (ϕ' ↑* (S ▷ s)) ~∎

  dist-wk-,ₖ' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} s {s'} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s') →
    wkₖ s (ϕ ,ₖ x/t) ~' (wkₖ s ϕ ,ₖ Kit.wk 𝕂 _ x/t)
  dist-wk-,ₖ' ⦃ 𝕂 ⦄ s ϕ x/t = mk-~' λ where
    sx (here refl) →
      here refl & (wkₖ s (ϕ ,ₖ x/t))    ≡⟨ &-wkₖ-wk (ϕ ,ₖ x/t) (here refl) ⟩
      wk s (here refl & (ϕ ,ₖ x/t))     ≡⟨ cong (wk s) (&-,ₖ-here ϕ x/t) ⟩
      wk s x/t                          ≡⟨ sym (&-,ₖ-here (wkₖ s ϕ) (wk s x/t)) ⟩
      here refl & (wkₖ s ϕ ,ₖ wk s x/t) ∎
    sx (there x) →
      there x & (wkₖ _ (ϕ ,ₖ x/t))    ≡⟨ &-wkₖ-wk (ϕ ,ₖ x/t) (there x) ⟩
      wk _ (there x & (ϕ ,ₖ x/t))     ≡⟨ cong (wk _) (&-,ₖ-there ϕ x/t x) ⟩
      wk _ (x & ϕ)                    ≡⟨ sym (&-wkₖ-wk ϕ x) ⟩
      x & (wkₖ _ ϕ)                   ≡⟨ sym (&-,ₖ-there (wkₖ s ϕ) (wk _ x/t) x) ⟩
      there x & (wkₖ _ ϕ ,ₖ wk _ x/t) ∎

  dist-wk-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} s {s'} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s') →
    wkₖ s (ϕ ,ₖ x/t) ~ (wkₖ s ϕ ,ₖ Kit.wk 𝕂 _ x/t)
  dist-wk-,ₖ s ϕ x/t = ~'→~ (dist-wk-,ₖ' s ϕ x/t)

  dist-wk*-,ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S {s'} (ϕ : S₁ –[ 𝕂 ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂 ] s') →
    wkₖ* S (ϕ ,ₖ x/t) ~ (wkₖ* S ϕ ,ₖ wk* _ x/t)
  dist-wk*-,ₖ []      ϕ x/t =
    wkₖ* [] (ϕ ,ₖ x/t)       ~⟨ wkₖ*-[] (ϕ ,ₖ x/t) ⟩
    ϕ ,ₖ x/t                 ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-[] ϕ)) refl ⟩
    (wkₖ* [] ϕ ,ₖ x/t)       ~⟨⟩
    (wkₖ* [] ϕ ,ₖ wk* _ x/t) ~∎
  dist-wk*-,ₖ (S ▷ s) ϕ x/t =
    wkₖ* (S ▷ s) (ϕ ,ₖ x/t)                ~⟨ wkₖ*-▷ S s (ϕ ,ₖ x/t) ⟩
    wkₖ s (wkₖ* S (ϕ ,ₖ x/t))              ~⟨ ~-cong-wk' (dist-wk*-,ₖ S ϕ x/t) ⟩
    wkₖ s (wkₖ* S ϕ ,ₖ wk* _ x/t)          ~⟨ dist-wk-,ₖ s (wkₖ* S ϕ) (wk* _ x/t) ⟩
    (wkₖ s (wkₖ* S ϕ) ,ₖ wk s (wk* S x/t)) ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-▷ S s ϕ)) refl ⟩
    (wkₖ* (S ▷ s) ϕ ,ₖ wk* _ x/t)          ~∎

  open import Kitty.Util.SubstProperties

  wkₖ*-▷▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S S' (ϕ : S₁ –[ 𝕂 ]→ S₂)  →
    let sub = subst (S₁ –[ 𝕂 ]→_) (++-assoc S S' S₂) in
    wkₖ* S (wkₖ* S' ϕ) ~ sub (wkₖ* (S' ▷▷ S) ϕ)
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {S₁} {S₂} [] S' ϕ =
    let sub = subst (S₁ –[ 𝕂 ]→_) (++-assoc [] S' S₂) in
    wkₖ* [] (wkₖ* S' ϕ)     ~⟨ wkₖ*-[] (wkₖ* S' ϕ) ⟩
    wkₖ* S' ϕ               ~⟨⟩
    sub (wkₖ* (S' ▷▷ []) ϕ) ~∎
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {S₁} {S₂} (S ▷ s) S' ϕ =
    let sub = subst (S₁ –[ 𝕂 ]→_) (++-assoc (S ▷ s) S' S₂) in
    let sub' = subst (S₁ –[ 𝕂 ]→_) (++-assoc S S' S₂) in
    wkₖ* (S ▷ s) (wkₖ* S' ϕ)        ~⟨ wkₖ*-▷ S s (wkₖ* S' ϕ) ⟩
    wkₖ s (wkₖ* S (wkₖ* S' ϕ))      ~⟨ ~-cong-wk' (wkₖ*-▷▷ S S' ϕ) ⟩
    wkₖ s (sub' (wkₖ* (S' ▷▷ S) ϕ)) ~≡⟨ dist-subst' (_▷ s) (wkₖ s) (++-assoc S S' S₂) (++-assoc (S ▷ s) S' S₂) (wkₖ* (S' ▷▷ S) ϕ) ⟩
    sub (wkₖ s (wkₖ* (S' ▷▷ S) ϕ))  ~⟨ ~-cong-subst-S₂ (++-assoc (S ▷ s) S' S₂) (~-sym (wkₖ*-▷ (S' ▷▷ S) s ϕ)) ⟩
    sub (wkₖ* (S' ▷▷ (S ▷ s)) ϕ)    ~∎

  wkₖ-▷▷ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ 𝕂 ]→ S₂)  →
    let sub = subst (S₁ –[ 𝕂 ]→_) (++-assoc S ([] ▷ s) S₂) in
    wkₖ* S (wkₖ s ϕ) ~ sub (wkₖ* (([] ▷ s) ▷▷ S) ϕ)
  wkₖ-▷▷ ⦃ 𝕂 ⦄ {S₁} {S₂} S s ϕ =
    let sub = subst (S₁ –[ 𝕂 ]→_) (++-assoc S ([] ▷ s) S₂) in
    wkₖ* S (wkₖ s ϕ)             ~⟨ ~-cong-wk*' (~-cong-wk' (~-sym (wkₖ*-[] ϕ))) ⟩
    wkₖ* S (wkₖ s (wkₖ* [] ϕ))   ~⟨ ~-cong-wk*' (~-sym (wkₖ*-▷ [] s ϕ)) ⟩
    wkₖ* S (wkₖ* ([] ▷ s) ϕ)     ~⟨ wkₖ*-▷▷ S ([] ▷ s) ϕ ⟩
    sub (wkₖ* (([] ▷ s) ▷▷ S) ϕ) ~∎

  dist-wk-↓' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ s s'} → (ϕ : (S₁ ▷ s') –[ 𝕂 ]→ S₂) →
    wkₖ s (ϕ ↓) ~' (wkₖ s ϕ ↓)
  dist-wk-↓' ⦃ 𝕂 ⦄ {S₁} {S₂} {s} {s'} ϕ = mk-~' λ sx x →
    x & (wkₖ s (ϕ ↓))   ≡⟨ &-wkₖ-wk (ϕ ↓) x ⟩
    wk s (x & (ϕ ↓))    ≡⟨ cong (wk s) (&-↓ ϕ x) ⟩
    wk s (there x & ϕ)  ≡⟨ sym (&-wkₖ-wk ϕ (there x)) ⟩
    there x & (wkₖ s ϕ) ≡⟨ sym (&-↓ (wkₖ s ϕ) x) ⟩
    x & (wkₖ s ϕ ↓)     ∎

  dist-wk-↓ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ s s'} → (ϕ : (S₁ ▷ s') –[ 𝕂 ]→ S₂) →
    wkₖ s (ϕ ↓) ~ (wkₖ s ϕ ↓)
  dist-wk-↓ ϕ = ~'→~ (dist-wk-↓' ϕ)

  dist-wk*-↓ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ S s'} → (ϕ : (S₁ ▷ s') –[ 𝕂 ]→ S₂) →
    wkₖ* S (ϕ ↓) ~ (wkₖ* S ϕ ↓)
  dist-wk*-↓ ⦃ 𝕂 ⦄ {S₁} {S₂} {S = []}    {s'} ϕ =
    wkₖ* [] (ϕ ↓)        ~⟨ wkₖ*-[] (ϕ ↓) ⟩
    (ϕ ↓)                ~⟨ ~-cong-↓ (~-sym (wkₖ*-[] ϕ)) ⟩
    (wkₖ* [] ϕ ↓)        ~∎
  dist-wk*-↓ ⦃ 𝕂 ⦄ {S₁} {S₂} {S = S ▷ s} {s'} ϕ =
    wkₖ* (S ▷ s) (ϕ ↓)   ~⟨ wkₖ*-▷ S s (ϕ ↓) ⟩
    wkₖ s (wkₖ* S (ϕ ↓)) ~⟨ ~-cong-wk' (dist-wk*-↓ ϕ) ⟩
    wkₖ s (wkₖ* S ϕ ↓)   ~⟨ dist-wk-↓ (wkₖ* S ϕ) ⟩
    (wkₖ s (wkₖ* S ϕ) ↓) ~⟨ ~-cong-↓ (~-sym (wkₖ*-▷ S s ϕ)) ⟩
    (wkₖ* (S ▷ s) ϕ ↓)   ~∎

  ∥-wk : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂} s → (ϕ₁ : S₁₁ –[ 𝕂 ]→ S₂) → (ϕ₂ : S₁₂ –[ 𝕂 ]→ S₂) →
    wkₖ s (ϕ₁ ∥ ϕ₂) ~ (wkₖ s ϕ₁ ∥ wkₖ s ϕ₂)
  ∥-wk ⦃ 𝕂 ⦄ {S₁₁} {[]} {S₂} s ϕ₁ ϕ₂ =
    wkₖ s (ϕ₁ ∥ ϕ₂)        ~⟨ ~-cong-wk' (∥-[] ϕ₁ ϕ₂) ⟩
    wkₖ s ϕ₁               ~⟨ ~-sym (∥-[] (wkₖ s ϕ₁) (wkₖ s ϕ₂)) ⟩
    (wkₖ s ϕ₁ ∥ wkₖ s ϕ₂)  ~∎
  ∥-wk ⦃ 𝕂 ⦄ {S₁₁} {S₁₂ ▷ s₂} {S₂} s ϕ₁ ϕ₂ =
    let sub = subst (_–[ 𝕂 ]→ S₂) (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁)) in
    let sub' = subst (_–[ 𝕂 ]→ (S₂ ▷ s)) (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁)) in
    wkₖ s (ϕ₁ ∥ ϕ₂)                                              ~⟨ ~-cong-wk' (∥-▷ ϕ₁ ϕ₂) ⟩
    wkₖ s (sub ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))              ~≡⟨ dist-subst {F = _–[ 𝕂 ]→ S₂} {G = _–[ 𝕂 ]→ (S₂ ▷ s)}
                                                                                    (wkₖ s) (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁))
                                                                                    ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)) ⟩
    sub' (wkₖ s ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))             ~⟨ ~-cong-subst-S₁ (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁))
                                                                        (dist-wk-,ₖ s (ϕ₁ ∥ (ϕ₂ ↓)) (here refl & ϕ₂)) ⟩
    sub' (wkₖ s (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ wk s (here refl & ϕ₂))          ~≡⟨ cong (λ ■ → sub' (wkₖ s (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ ■))
                                                                          (sym (&-wkₖ-wk ϕ₂ (here refl))) ⟩ 
    sub' (wkₖ s (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & (wkₖ s ϕ₂)))       ~⟨ ~-cong-subst-S₁ (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁))
                                                                        (~-cong-,ₖ (∥-wk s ϕ₁ (ϕ₂ ↓)) refl) ⟩
    sub' ((wkₖ s ϕ₁ ∥ wkₖ s (ϕ₂ ↓)) ,ₖ (here refl & (wkₖ s ϕ₂))) ~⟨ ~-cong-subst-S₁ (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁))
                                                                        (~-cong-,ₖ (~-cong-∥ ~-refl (dist-wk-↓ ϕ₂)) refl) ⟩
    sub' ((wkₖ s ϕ₁ ∥ (wkₖ s ϕ₂ ↓)) ,ₖ (here refl & (wkₖ s ϕ₂))) ~⟨ ~-sym (∥-▷ (wkₖ s ϕ₁) (wkₖ s ϕ₂)) ⟩
    (wkₖ s ϕ₁ ∥ wkₖ s ϕ₂) ~∎

  ∥-wk* : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂} S → (ϕ₁ : S₁₁ –[ 𝕂 ]→ S₂) → (ϕ₂ : S₁₂ –[ 𝕂 ]→ S₂) →
    wkₖ* S (ϕ₁ ∥ ϕ₂) ~ (wkₖ* S ϕ₁ ∥ wkₖ* S ϕ₂)
  ∥-wk* ⦃ 𝕂 ⦄ {S₁₁} {S₁₂} {S₂} []      ϕ₁ ϕ₂ =
    wkₖ* [] (ϕ₁ ∥ ϕ₂)         ~⟨ wkₖ*-[] (ϕ₁ ∥ ϕ₂) ⟩
    (ϕ₁ ∥ ϕ₂)                 ~⟨ ~-sym (~-cong-∥ (wkₖ*-[] ϕ₁) (wkₖ*-[] ϕ₂)) ⟩
    (wkₖ* [] ϕ₁ ∥ wkₖ* [] ϕ₂) ~∎
  ∥-wk* ⦃ 𝕂 ⦄ {S₁₁} {S₁₂} {S₂} (S ▷ s) ϕ₁ ϕ₂ =
    wkₖ* (S ▷ s) (ϕ₁ ∥ ϕ₂)                  ~⟨ wkₖ*-▷ S s (ϕ₁ ∥ ϕ₂) ⟩
    wkₖ s (wkₖ* S (ϕ₁ ∥ ϕ₂))                ~⟨ ~-cong-wk' (∥-wk* S ϕ₁ ϕ₂) ⟩
    wkₖ s (wkₖ* S ϕ₁ ∥ wkₖ* S ϕ₂)           ~⟨ ∥-wk s (wkₖ* S ϕ₁) (wkₖ* S ϕ₂) ⟩
    (wkₖ s (wkₖ* S ϕ₁) ∥ wkₖ s (wkₖ* S ϕ₂)) ~⟨ ~-sym (~-cong-∥ (wkₖ*-▷ S s ϕ₁) (wkₖ*-▷ S s ϕ₂)) ⟩
    (wkₖ* (S ▷ s) ϕ₁ ∥ wkₖ* (S ▷ s) ϕ₂)     ~∎

  ∥-↓ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂ s} → (ϕ₁ : S₁₁ –[ 𝕂 ]→ S₂) → (ϕ₂ : (S₁₂ ▷ s) –[ 𝕂 ]→ S₂) →
    (ϕ₁ ∥ ϕ₂) ↓ ~ ϕ₁ ∥ (ϕ₂ ↓)
  ∥-↓ ⦃ 𝕂 ⦄ {S₁₁} {S₁₂} {S₂} {s} ϕ₁ ϕ₂ = mk-~ λ sx x →
    `/id (x & ((ϕ₁ ∥ ϕ₂) ↓))                           ≡⟨ cong `/id (&-↓ (ϕ₁ ∥ ϕ₂) x) ⟩
    `/id (there x & (ϕ₁ ∥ ϕ₂))                         ≡⟨ use-~ (∥-▷ ϕ₁ ϕ₂) _ (there x) ⟩
    `/id (there x & (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)) ≡⟨ cong `/id (&-,ₖ-there (ϕ₁ ∥ (ϕ₂ ↓)) _ x) ⟩
    `/id (x & ϕ₁ ∥ (ϕ₂ ↓))                             ∎

  &-∥-here : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂ s} → (ϕ₁ : S₁₁ –[ 𝕂 ]→ S₂) → (ϕ₂ : (S₁₂ ▷ s) –[ 𝕂 ]→ S₂) →
    here refl & (ϕ₁ ∥ ϕ₂) ≡ here refl & ϕ₂
  &-∥-here ⦃ 𝕂 ⦄ {S₁₁} {S₁₂} {S₂} {s} ϕ₁ ϕ₂ =
    here refl & (ϕ₁ ∥ ϕ₂)                         ≡⟨ use-~-hom (∥-▷ ϕ₁ ϕ₂) _ (here refl) ⟩
    here refl & (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂) ≡⟨ &-,ₖ-here (ϕ₁ ∥ (ϕ₂ ↓)) (here refl & ϕ₂) ⟩
    here refl & ϕ₂                                ∎


  -- Identity


  -- idₖ' : S –→ (S' ▷▷ S )
  -- idₖ' _ x = id/` (∈-▷▷ₗ x)  where
  --   ∈-▷▷ₗ : S ∋ s → (S' ▷▷ S) ∋ s
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- idₖ'' : ∀ {S S' S''} → S –→ (S' ▷▷ S ▷▷ S'')
  -- idₖ'' {S} {S'} {S''} _ x = wk* {S' = S''} _ (id/` (∈-▷▷ₗ x))  where
  --   ∈-▷▷ₗ :  ∀ {S} {S'} → S ∋ s → (S' ▷▷ S) ∋ s
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- Lifted identity is identity

  id↑~id : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ s S → id {S = S} ↑ s ~ id {S = S ▷ s}
  id↑~id s S = mk-~ λ where
    _ x@(here refl) →
      `/id (x & id {S = S} ↑ s) ≡⟨ cong `/id (&-↑-here id) ⟩
      `/id (id/` (here refl))   ≡⟨ cong `/id (sym (&-id x)) ⟩
      `/id (x & id {S = S ▷ s}) ∎
    _ x@(there y) →
      `/id (x & id {S = S} ↑ s)    ≡⟨ cong `/id (&-↑-there id y) ⟩
      `/id (wk _ (y & id {S = S})) ≡⟨ cong (λ ■ → `/id (wk _ ■)) (&-id y) ⟩
      `/id (wk _ (id/` y))         ≡⟨ cong `/id (wk-id/` _ y) ⟩
      `/id (id/` x)                ≡⟨ cong `/id (sym (&-id x)) ⟩
      `/id (x & id {S = S ▷ s})    ∎

  id↑*~id : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ S' S → id {S = S} ↑* S' ~ id {S = S ▷▷ S'}
  id↑*~id []       S = ↑*-[] id
  id↑*~id (S' ▷ s) S =
    id ↑* (S' ▷ s) ~⟨ ↑*-▷ S' s id ⟩
    id ↑* S' ↑ s   ~⟨ ~-cong-↑' (id↑*~id S' S) ⟩
    id ↑ s         ~⟨ id↑~id _ _ ⟩
    id             ~∎

  -- Empty Substitution

  &-[]ₖ : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {s} (x : _ ∋ s) → x & []ₖ ≡ id/` x
  &-[]ₖ ()

  &-[]ₖ' : ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ (ϕ : [] –[ 𝕂 ]→ []) → ϕ ~ []ₖ
  &-[]ₖ' ϕ = mk-~ λ s ()

  -- -- Singleton renaming/substitution

  -- -- Singleton renaming/substitution for terms with 1 free variable.
  -- -- Allows the term to be substituted to have arbitrary free variables.
  -- -- This is useful for things like pattern inverting in combination with `_∥_`,
  -- -- where a inverting substitution needs to be built up piece by piece.
  -- ⦅_⦆₀ : S ∋/⊢ id/m→M m → ([] ▷ m) –→ S
  -- ⦅ v ⦆₀ = emptyₖ ,ₖ v

  -- -- ⦅_⦆' : (S ▷▷ S') ∋/⊢ m→[m/M] m → (S ▷ m ▷▷ S') –→ (S ▷▷ S')
  -- -- ⦅ v ⦆' = idₖ'' ∥ ⦅ v ⦆₀ ∥ idₖ''
  -- -- ⦅ v ⦆' = {!!} ∥ ⦅ v ⦆₀ ∥ {!!}
  -- -- -- ⦅ v ⦆' = (idₖ ∥ ⦅ v ⦆₀) ↑* _
