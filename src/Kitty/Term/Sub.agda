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

    []ₖ  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → [] –[ K ]→ []
    _,ₖ_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s → (S₁ ▷ s) –[ K ]→ S₂
    wkₖ  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} s → S₁ –[ K ]→ S₂ → S₁ –[ K ]→ (S₂ ▷ s)
    wkₖ* : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S → S₁ –[ K ]→ S₂ → S₁ –[ K ]→ (S₂ ▷▷ S)
    _↑_  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ K ]→ S₂ → ∀ s → (S₁ ▷ s) –[ K ]→ (S₂ ▷ s)
    _↑*_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ K ]→ S₂ → ∀ S' → (S₁ ▷▷ S') –[ K ]→ (S₂ ▷▷ S')
    id   : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S} → S –[ K ]→ S
    []*  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₂} → [] –[ K ]→ S₂
    _↓   : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → (S₁ ▷ s) –[ K ]→ S₂ → S₁ –[ K ]→ S₂
    -- TODO: we might want this also to be Kit-heterogenous, to allow for talking about
    -- parallel compositions of two unknown, potentially different Kits.
    _∥_  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S₂ S} → (S₁ –[ K ]→ S) → (S₂ –[ K ]→ S) → ((S₁ ▷▷ S₂) –[ K ]→ S)
    ⦅_⦆ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S S' s} → (S ▷▷ S') ∋/⊢ s → (S ▷ s) –[ K ]→ (S ▷▷ S')
    -- Singleton renaming/substitution for terms with 1 free variable.
    -- Allows the term to be substituted to have arbitrary free variables.
    -- This is useful for things like pattern matching in combination with `_∥_`,
    -- where a matching substitution needs to be built up piece by piece.
    ⦅_⦆₀ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S s} → S ∋/⊢ s → ([] ▷ s) –[ K ]→ S


    _&_  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} → S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢ s

    ι-→ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₁⊑K₂ : K₁ ⊑ₖ K₂ ⦄ {S₁} {S₂} → S₁ –[ K₁ ]→ S₂ → S₁ –[ K₂ ]→ S₂

  ⦅_⦆' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S s} → (S) ∋/⊢ s → (S ▷ s) –[ K ]→ S
  ⦅_⦆' = ⦅_⦆

  -- Renaming/Substitution

  _–→_ : ⦃ K : Kit _∋/⊢_ ⦄ → SortCtx → SortCtx → Set ℓ
  _–→_ ⦃ K ⦄ S₁ S₂ = S₁ –[ K ]→ S₂

  -- Extensional Equality

  -- Unused, because when we use it, we get horrible, horrible names....
  module Heterogeneous-~
      {ℓ}
      (P : ∀ {_∋/⊢_ : VarScoped} (K : Kit _∋/⊢_) → Set ℓ)
      (R : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
             (ϕ₁ : P K₁) (ϕ₂ : P K₂) → Set)
      (R-refl : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ {ϕ : P K} → R ϕ ϕ)
      (R-sym  : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
                  {ϕ₁ : P K₁} {ϕ₂ : P K₂}
                → R ϕ₁ ϕ₂ → R ϕ₂ ϕ₁)
      (R-trans : ∀ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped} {_∋/⊢₃_ : VarScoped}
                   ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄
                   {ϕ₁ : P K₁} {ϕ₂ : P K₂} {ϕ₃ : P K₃}
                → R ϕ₁ ϕ₂ → R ϕ₂ ϕ₃ → R ϕ₁ ϕ₃)
      where

    record _~_ {_∋/⊢₁_ : VarScoped} {_∋/⊢₂_ : VarScoped}
               ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
               (ϕ₁ : P K₁) (ϕ₂ : P K₂) : Set where
      constructor mk-~
      field
        use-~ : R ϕ₁ ϕ₂
    open _~_

    ~-refl :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ {f : P K}
      → f ~ f
    ~-refl = mk-~ R-refl

    ~-sym :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {f : P K₁} {g : P K₂}
      → f ~ g
      → g ~ f
    ~-sym f~g = mk-~ (R-sym (use-~ f~g))

    ~-trans :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ {f : P K₁} {g : P K₂} {h : P K₃}
      → f ~ g
      → g ~ h
      → f ~ h
    ~-trans f~g g~h = mk-~ (R-trans (use-~ f~g) (use-~ g~h))

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      ⦃ K ⦄ : Kit _∋/⊢_
      f g h : P K

    begin~_ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {f : P K₁} {g : P K₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ (f : P K₁) {g : P K₂}
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ (f : P K₁) {g : P K₂} {h : P K₃}
      → g ~ h → f ~ g → f ~ h
    step-~ f g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ (f : P K₁) {g : P K₂} {h : P K₃}
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ (f : P K₁) {g : P K₁} {h : P K₂}
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f : P K)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

  infix  4  _~ₜ_

  _~ₜ_ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S} {s} → S ∋/⊢[ K₁ ] s → S ∋/⊢[ K₂ ] s → Set
  _~ₜ_ ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S} {s} x/t₁ x/t₂ =
    `/id x/t₁ ≡ `/id x/t₂
  -- _~ₜ_ ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S} {s} x/t₁ x/t₂ =
  --   let eq = m→M/id (id/m→M ⦃ K₁ ⦄ m) ≡⟨ id/m→M/id m ⟩
  --            m→M m                    ≡⟨ sym (id/m→M/id m) ⟩
  --            m→M/id (id/m→M ⦃ K₂ ⦄ m) ∎
  --   in x/t₁ ~ₜ[ eq ] x/t₂

  -- module Test where
  --   module Terms-~ {S} {m} where
  --     open Heterogeneous-~ (λ K → S ∋/⊢[ K ] id/m→M ⦃ K ⦄ m) _~ₜ_ refl sym trans public
  --       renaming (_~_ to _~ᵗ_)
  --   open Terms-~
  --   test : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S} {m} (ϕ : S ∋/⊢[ K ] id/m→M ⦃ K ⦄ m) → ϕ ~ᵗ ϕ
  --   test ϕ =
  --     ϕ ~⟨ {!!} ⟩
  --     ϕ ~∎


  -- Helps with inferring ϕ₁ and ϕ₂ from implicits
  record _~_ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₁ –[ K₂ ]→ S₂) : Set where
    constructor mk-~
    field
      use-~ : ∀ s (x : _ ∋ s) → x & ϕ₁ ~ₜ x & ϕ₂
  open _~_ public

  -- Helps with inferring ϕ₁ and ϕ₂ from implicits
  record _~'_ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ₁ : S₁ –[ K ]→ S₂) (ϕ₂ : S₁ –[ K ]→ S₂) : Set where
    constructor mk-~'
    field
      use-~' : ∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂
  open _~'_ public

  -- _~_ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} → S₁ –[ K₁ ]→ S₂ → S₁ –[ K₂ ]→ S₂ → Set
  -- ϕ₁ ~ ϕ₂ = ∀ s (x : _ ∋ s) → x & ϕ₁ ~ₜ x & ϕ₂
  -- -- ϕ₁ ~ ϕ₂ = ∀ s x → `/id (& ϕ₁ s x) ≡ `/id (& ϕ₂ s x)

  -- _~'_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} → S₁ –[ K ]→ S₂ → S₁ –[ K ]→ S₂ → Set
  -- ϕ₁ ~' ϕ₂ = ∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂

  ~→~' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ K ]→ S₂}
         → ϕ₁ ~ ϕ₂
         → ϕ₁ ~' ϕ₂
  ~→~' ϕ₁~ϕ₂ = mk-~' (λ s x → `/id-injective (use-~ ϕ₁~ϕ₂ s x))

  ~'→~ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ K ]→ S₂}
         → ϕ₁ ~' ϕ₂
         → ϕ₁ ~ ϕ₂
  ~'→~ ϕ₁~'ϕ₂ = mk-~ (λ s x → cong `/id (use-~' ϕ₁~'ϕ₂ s x))

  use-~-hom :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ₁ ϕ₂ : S₁ –[ K ]→ S₂}
    → ϕ₁ ~ ϕ₂
    → (∀ s (x : _ ∋ s) → x & ϕ₁ ≡ x & ϕ₂)
  use-~-hom ϕ₁~ϕ₂ = use-~' (~→~' ϕ₁~ϕ₂)

  ~ₜ-refl :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S} {s} {x/t : S ∋/⊢[ K ] s}
    → x/t ~ₜ x/t
  ~ₜ-refl = cong (`/id) refl

  ~ₓ-refl :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S} {s} {x : S ∋ s}
    → id/` ⦃ K₁ ⦄ x ~ₜ id/` ⦃ K₂ ⦄ x
  ~ₓ-refl ⦃ K₁ ⦄ ⦃ K₂ ⦄ {x = x} =
    `/id ⦃ K₁ ⦄ (id/` x) ≡⟨ id/`/id ⦃ K₁ ⦄ x ⟩
    ` x                  ≡⟨ sym (id/`/id ⦃ K₂ ⦄ x) ⟩
    `/id ⦃ K₂ ⦄ (id/` x) ∎

  ~-refl :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f : S₁ –[ K ]→ S₂}
    → f ~ f
  ~-refl = mk-~ (λ a b → refl)

  ~-sym :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂}
    → f ~ g
    → g ~ f
  ~-sym f~g = mk-~ (λ a b → sym (use-~ f~g a b))

  ~-trans :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ {S₁} {S₂} {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} {h : S₁ –[ K₃ ]→ S₂}
    → f ~ g
    → g ~ h
    → f ~ h
  ~-trans f~g g~h = mk-~ (λ a b → trans (use-~ f~g a b) (use-~ g~h a b))

  ~-cong-subst-S₁ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₁'} {S₂} {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} (eq : S₁ ≡ S₁')
    → f ~ g
    → subst (_–[ K₁ ]→ S₂) eq f ~ subst (_–[ K₂ ]→ S₂) eq g
  ~-cong-subst-S₁ refl f~g = f~g

  ~-cong-subst-S₂ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {S₂'} {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} (eq : S₂ ≡ S₂')
    → f ~ g
    → subst (S₁ –[ K₁ ]→_) eq f ~ subst (S₁ –[ K₂ ]→_) eq g
  ~-cong-subst-S₂ refl f~g = f~g

  ~-cong-subst₂ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₁'} {S₂} {S₂'} {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} (eq₁ : S₁ ≡ S₁') (eq₂ : S₂ ≡ S₂')
    → f ~ g
    → subst₂ (_–[ K₁ ]→_) eq₁ eq₂ f ~ subst₂ (_–[ K₂ ]→_) eq₁ eq₂ g
  ~-cong-subst₂ refl refl f~g = f~g

  module ~-Reasoning where

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      S₁ S₂ S₃ : SortCtx
      ⦃ K ⦄ : Kit _∋/⊢_
      f g h : S₁ –[ K ]→ S₂

    begin~_ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ (f : S₁ –[ K₁ ]→ S₂) {g : S₁ –[ K₂ ]→ S₂}
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ (f : S₁ –[ K₁ ]→ S₂) {g : S₁ –[ K₂ ]→ S₂} {h : S₁ –[ K₃ ]→ S₂}
      → g ~ h → f ~ g → f ~ h
    step-~ f g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ (f : S₁ –[ K₁ ]→ S₂) {g : S₁ –[ K₂ ]→ S₂} {h : S₁ –[ K₃ ]→ S₂}
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ (f : S₁ –[ K₁ ]→ S₂) {g : S₁ –[ K₁ ]→ S₂} {h : S₁ –[ K₂ ]→ S₂}
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f : S₁ –[ K ]→ S₂)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

  ~'-refl :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f : S₁ –[ K ]→ S₂}
    → f ~' f
  ~'-refl = mk-~' λ a b → refl

  ~'-sym :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f g : S₁ –[ K ]→ S₂}
    → f ~' g
    → g ~' f
  ~'-sym f~'g = mk-~' λ a b → sym (use-~' f~'g a b)

  ~'-trans :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {f g h : S₁ –[ K ]→ S₂} 
    → f ~' g
    → g ~' h
    → f ~' h
  ~'-trans f~'g g~'h = mk-~' λ a b → trans (use-~' f~'g a b) (use-~' g~'h a b)

  ~'-cong-subst-S₁ :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₁'} {S₂} {f g : S₁ –[ K ]→ S₂} (eq : S₁ ≡ S₁')
    → f ~' g
    → subst (_–[ K ]→ S₂) eq f ~' subst (_–[ K ]→ S₂) eq g
  ~'-cong-subst-S₁ refl f~'g = f~'g

  ~'-cong-subst-S₂ :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S₂'} {f g : S₁ –[ K ]→ S₂} (eq : S₂ ≡ S₂')
    → f ~' g
    → subst (S₁ –[ K ]→_) eq f ~' subst (S₁ –[ K ]→_) eq g
  ~'-cong-subst-S₂ refl f~'g = f~'g

  module ~'-Reasoning where

    infix  3 _~'∎
    infixr 2 _~'⟨⟩_ step-~' step-~'˘ step-~'≡
    infix  1 begin~'_

    private variable
      S₁ S₂ S₃ : SortCtx
      ⦃ K ⦄ : Kit _∋/⊢_
      f g h : S₁ –[ K ]→ S₂

    begin~'_ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ {f g : S₁ –[ K ]→ S₂}
      → f ~' g → f ~' g
    begin~'_ x≡y = x≡y

    _~'⟨⟩_ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f {g} : S₁ –[ K ]→ S₂)
      → f ~' g → f ~' g
    _ ~'⟨⟩ x~'y = x~'y

    step-~' :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ K ]→ S₂)
      → g ~' h → f ~' g → f ~' h
    step-~' _ g~'h f~'g = ~'-trans f~'g g~'h

    step-~'˘ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ K ]→ S₂)
      → g ~' h → g ~' f → f ~' h
    step-~'˘ _ g~'h g~'f = ~'-trans (~'-sym g~'f) g~'h

    step-~'≡ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f {g h} : S₁ –[ K ]→ S₂)
      → g ~' h → f ≡ g → f ~' h
    step-~'≡ f g~'h f≡g = ~'-trans (subst (f ~'_) f≡g ~'-refl ) g~'h

    _~'∎ :
      ∀ ⦃ K : Kit _∋/⊢_ ⦄ (f : S₁ –[ K ]→ S₂)
      → f ~' f
    _~'∎ _ = ~'-refl

    syntax step-~'  f g~'h f~'g = f ~'⟨ f~'g ⟩ g~'h
    syntax step-~'≡  f g~'h f≡g = f ~'≡⟨ f≡g ⟩ g~'h
    syntax step-~'˘ f g~'h g~'f = f ~'˘⟨ g~'f ⟩ g~'h

  data Invert-ϕ ⦃ K : Kit _∋/⊢_ ⦄ {S₂} : {S₁ : SortCtx} → S₁ –[ K ]→ S₂ → Set ℓ where
    ϕ~[]* : ∀ {ϕ} →
      ϕ ~ []* →
      Invert-ϕ ϕ
    ϕ~,ₖ : ∀ {S₁' s₁ ϕ} →
      (ϕ' : S₁' –[ K ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      ϕ ~ (ϕ' ,ₖ x/t) →
      Invert-ϕ ϕ

  data Invert-ϕ' ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) : Set ℓ where
    ϕ~[]* :
      (eq : S₁ ≡ []) →
      let sub = subst (_–[ K ]→ S₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ' ϕ
    ϕ~,ₖ : ∀ {S₁' s₁} →
      (eq : S₁ ≡ S₁' ▷ s₁) →
      (ϕ' : S₁' –[ K ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      let sub = subst (_–[ K ]→ S₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      Invert-ϕ' ϕ

  data Invert-ϕ'-Rec ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) : S₁ –[ K ]→ S₂ → Set ℓ where
    ϕ~[]* :
      (eq : S₁ ≡ []) →
      let sub = subst (_–[ K ]→ S₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ'-Rec ϕ (sub []*)
    ϕ~,ₖ : ∀ {S₁' s₁} →
      (eq : S₁ ≡ S₁' ▷ s₁) →
      (ϕ' : S₁' –[ K ]→ S₂) →
      (x/t : S₂ ∋/⊢ s₁) →
      (ϕ'' : S₁' –[ K ]→ S₂) →
      Invert-ϕ'-Rec ϕ' ϕ'' →
      let sub = subst (_–[ K ]→ S₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      ϕ ~ sub (ϕ'' ,ₖ x/t) →
      Invert-ϕ'-Rec ϕ (sub (ϕ'' ,ₖ x/t))

  invert-ϕ'→ϕ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ : S₁ –[ K ]→ S₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  invert-ϕ'→ϕ (ϕ~[]* refl ϕ~) = ϕ~[]* ϕ~
  invert-ϕ'→ϕ (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

  -- -- requires dependent subst
  -- invert-ϕ'→ϕ' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {ϕ : S₁ –[ K ]→ S₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  -- invert-ϕ'→ϕ' {S₁} {S₂} {ϕ} (ϕ~[]* S₁≡[] ϕ~) = {!subst₂ (λ ■ ■' → Invert-ϕ {S₁ = ■} ■') ? ? {!ϕ~[]* ϕ~!}!}
  -- invert-ϕ'→ϕ' (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

_–[_;_]→_ : ∀ {ℓ} → SortCtx → Kit _∋/⊢_ → Sub ℓ → SortCtx → Set ℓ
_–[_;_]→_ S₁ K 𝕊 S₂ = Sub._–[_]→_ 𝕊 S₁ K S₂

record SubWithLaws ℓ : Set (lsuc ℓ) where
  field
    ⦃ SubWithLaws-Sub ⦄ : Sub ℓ

  open Sub SubWithLaws-Sub

  field

    &-,ₖ-here : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s)
                  → here refl & (ϕ ,ₖ x/t) ≡ x/t
    &-,ₖ-there : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s) {s'} (x : S₁ ∋ s')
                   → there x & (ϕ ,ₖ x/t) ≡ x & ϕ

    &-wkₖ-wk : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : S₁ –[ K ]→ S₂) (x : S₁ ∋ s')
                 → x & wkₖ s ϕ ≡ wk s (x & ϕ)

    &-↓ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : (S₁ ▷ s) –[ K ]→ S₂) (x : S₁ ∋ s')
      → x & (ϕ ↓) ≡ there x & ϕ

    wkₖ*-[] : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂)
      → wkₖ* [] ϕ ~ ϕ
    wkₖ*-▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ K ]→ S₂)
      → wkₖ* (S ▷ s) ϕ ~ wkₖ s (wkₖ* S ϕ)

    ↑-,ₖ  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) s
      → (ϕ ↑ s) ~ (wkₖ s ϕ ,ₖ id/` (here refl))

    ↑*-[]  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂)
      → (ϕ ↑* []) ~ ϕ

    ↑*-▷  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ K ]→ S₂)
      → (ϕ ↑* (S ▷ s)) ~ ((ϕ ↑* S) ↑ s)

    id-[] : ∀ ⦃ K : Kit _∋/⊢_ ⦄
      → id {S = []} ~ []ₖ

    id-▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S s}
      → id {S = S ▷ s} ~ (id {S = S} ↑ s)

    []*-[]  : ∀ ⦃ K : Kit _∋/⊢_ ⦄
      → []* {S₂ = []} ~ []ₖ

    []*-▷  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S s}
      → []* {S₂ = S ▷ s} ~ wkₖ s ([]* {S₂ = S})

    ↓-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s)
      → ((ϕ ,ₖ x/t) ↓) ~ ϕ

    ∥-[] : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S} → (ϕ₁ : S₁ –[ K ]→ S) → (ϕ₂ : [] –[ K ]→ S)
      → (ϕ₁ ∥ ϕ₂) ~ ϕ₁

    ∥-▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S₂ S s} → (ϕ₁ : S₁ –[ K ]→ S) → (ϕ₂ : (S₂ ▷ s) –[ K ]→ S)
      → (ϕ₁ ∥ ϕ₂) ~ ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂))

    ⦅⦆-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S S' s} (x/t : (S ▷▷ S') ∋/⊢ s) →
      ⦅ x/t ⦆ ~ (wkₖ* S' id ,ₖ x/t)

    ⦅⦆₀-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S s} (x/t : S ∋/⊢ s) →
      ⦅ x/t ⦆₀ ~ ([]* ,ₖ x/t)

    invert' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) → Invert-ϕ' ϕ

    &-ι-→ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₁⊑K₂ : K₁ ⊑ₖ K₂ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ K₁ ]→ S₂) (x : S₁ ∋ s)
            → x & (ι-→ ϕ) ≡ ι-∋/⊢ (x & ϕ)

  open ~-Reasoning

  ~-ι-→ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₁⊑K₂ : K₁ ⊑ₖ K₂ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K₁ ]→ S₂)
          → ι-→ ϕ ~ ϕ
  ~-ι-→ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₁⊑K₂ ⦄ {S₁} {S₂} ϕ = mk-~ λ s x →
    `/id (x & ι-→ ϕ)     ≡⟨ cong `/id (&-ι-→ ϕ x) ⟩
    `/id (ι-∋/⊢ (x & ϕ)) ≡⟨ sym (ι-`/id (x & ϕ)) ⟩
    `/id (x & ϕ)         ∎

  &-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S} {s} (x : S ∋ s)
           → x & id {S = S} ≡ id/` x
  &-id ⦃ K ⦄ {S ▷ s'} {s} x@(here refl) =
    x & (id {S = S ▷ s'})              ≡⟨ use-~-hom id-▷ s' x ⟩
    x & (id {S = S} ↑ s')              ≡⟨ use-~-hom (↑-,ₖ id s') _ x ⟩
    x & (wkₖ _ (id {S = S}) ,ₖ id/` x) ≡⟨ &-,ₖ-here (wkₖ _ (id {S = S})) (id/` x) ⟩
    id/` x                             ∎
  &-id ⦃ K ⦄ {S ▷ s'} {s} (there x) =
    there x & (id {S = S ▷ s'})                        ≡⟨ use-~-hom id-▷ _ (there x) ⟩
    there x & (id {S = S} ↑ s')                        ≡⟨ use-~-hom (↑-,ₖ id s') _ (there x) ⟩
    there x & (wkₖ _ (id {S = S}) ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ _ (id {S = S})) (id/` (here refl)) x ⟩
    x & (wkₖ _ (id {S = S}))                           ≡⟨ &-wkₖ-wk id x ⟩
    wk s' (x & id {S = S})                             ≡⟨ cong (wk s') (&-id x) ⟩
    wk s' (id/` x)                                     ≡⟨ wk-id/` s' x ⟩
    id/` (there x)                                     ∎

  -- id-▷▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S S'}
  --   → id {S ▷▷ S'} ~ (id {S} ↑* S')
  -- id-▷▷ {S' = []} = ~-sym (↑*-[] id)
  -- id-▷▷ {S' = S' ▷ s} = ~-trans {!id-▷▷!} (~-trans {!id-▷!} (~-sym (↑*-▷ S' s id)))

  &-↑-here :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} (ϕ : S₁ –[ K ]→ S₂)
    → here refl & (ϕ ↑ s) ≡ id/` (here refl)
  &-↑-here ⦃ K ⦄ {S₁} {S₂} {s} ϕ =
    here refl & (ϕ ↑ s)                       ≡⟨ use-~-hom (↑-,ₖ ϕ s) s (here refl) ⟩
    here refl & (wkₖ s ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-here (wkₖ s ϕ) _ ⟩
    id/` (here refl)                          ∎

  &-↑-there :
    ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {s'} (ϕ : S₁ –[ K ]→ S₂) (x : S₁ ∋ s')
    → there x & (ϕ ↑ s) ≡ wk s (x & ϕ)
  &-↑-there ⦃ K ⦄ {S₁} {S₂} {s} {s'} ϕ x =
    there x & (ϕ ↑ s)                       ≡⟨ use-~-hom (↑-,ₖ ϕ s) s' (there x) ⟩
    there x & (wkₖ s ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ s ϕ) _ x ⟩
    x & wkₖ s ϕ                             ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk s (x & ϕ)                            ∎

  -- Weakening preserves Homotopy

  ~'-cong-wk : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ K ]→ S₂} {ϕ' : S₁ –[ K ]→ S₂} →
    ϕ ~' ϕ' →
    wkₖ s ϕ ~' wkₖ s ϕ'
  ~'-cong-wk {S₁ = S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~' λ sx x →
    x & wkₖ _ ϕ   ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk _ (x & ϕ)  ≡⟨ cong (wk _) (use-~' ϕ~ϕ' sx x) ⟩
    wk _ (x & ϕ') ≡⟨ sym (&-wkₖ-wk ϕ' x) ⟩
    x & wkₖ _ ϕ'  ∎

  ~-cong-wk' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ K ]→ S₂} {ϕ' : S₁ –[ K ]→ S₂} →
    ϕ ~ ϕ' →
    wkₖ s ϕ ~ wkₖ s ϕ'
  ~-cong-wk' ϕ~ϕ' = ~'→~ (~'-cong-wk (~→~' ϕ~ϕ'))

  ~-cong-wk*' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S} {ϕ : S₁ –[ K ]→ S₂} {ϕ' : S₁ –[ K ]→ S₂} →
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

  ~-cong-,ₖ : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {s}
    {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂}
    {x/t : S₂ ∋/⊢[ K₁ ] s} {x/t' : S₂ ∋/⊢[ K₂ ] s} →
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

  ~'-cong-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ ϕ' : S₁ –[ K ]→ S₂} {x/t x/t' : S₂ ∋/⊢[ K ] s} →
    ϕ ~' ϕ' →
    x/t ≡ x/t' →
    (ϕ ,ₖ x/t) ~' (ϕ' ,ₖ x/t')
  ~'-cong-,ₖ ϕ~ϕ' x/t≡x/t' = ~→~' (~-cong-,ₖ (~'→~ ϕ~ϕ') (cong (`/id) x/t≡x/t'))

  ~-cong-↓ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁} {S₂} {s} {ϕ : (S₁ ▷ s) –[ K₁ ]→ S₂} {ϕ' : (S₁ ▷ s) –[ K₂ ]→ S₂} →
    ϕ ~ ϕ' →
    (ϕ ↓) ~ (ϕ' ↓)
  ~-cong-↓ ⦃ K ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~ λ sx x →
    `/id (x & (ϕ  ↓))   ≡⟨ cong (`/id) (&-↓ ϕ x) ⟩
    `/id (there x & ϕ ) ≡⟨ use-~ ϕ~ϕ' sx (there x) ⟩
    `/id (there x & ϕ') ≡⟨ cong (`/id) (sym (&-↓ ϕ' x)) ⟩
    `/id (x & (ϕ' ↓))   ∎

  ~-cong-∥ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S₁₁} {S₁₂} {S₂}
      {ϕ₁  : S₁₁ –[ K₁ ]→ S₂}
      {ϕ₁' : S₁₁ –[ K₂ ]→ S₂}
      {ϕ₂  : S₁₂ –[ K₁ ]→ S₂}
      {ϕ₂' : S₁₂ –[ K₂ ]→ S₂}
    → ϕ₁ ~ ϕ₁'
    → ϕ₂ ~ ϕ₂'
    → (ϕ₁ ∥ ϕ₂) ~ (ϕ₁' ∥ ϕ₂')
  ~-cong-∥ {S₁₁ = S₁₁} {[]}      {S₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    (ϕ₁ ∥ ϕ₂)   ~⟨ ∥-[] ϕ₁ ϕ₂ ⟩
    ϕ₁          ~⟨ ϕ₁~ϕ₁' ⟩
    ϕ₁'         ~⟨ ~-sym (∥-[] ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎
  ~-cong-∥ ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S₁₁} {S₁₂ ▷ s} {S₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    let sub₁ = subst (_–[ K₁ ]→ S₂) (sym (++-assoc ([] ▷ s) S₁₂ S₁₁)) in
    let sub₂ = subst (_–[ K₂ ]→ S₂) (sym (++-assoc ([] ▷ s) S₁₂ S₁₁)) in
    (ϕ₁ ∥ ϕ₂)                                      ~⟨ ∥-▷ ϕ₁ ϕ₂ ⟩
    sub₁ ((ϕ₁  ∥ (ϕ₂  ↓)) ,ₖ (here refl & ϕ₂)) ~⟨ ~-cong-subst-S₁ (sym (++-assoc ([] ▷ s) S₁₂ S₁₁))
                                                      (~-cong-,ₖ (~-cong-∥ ϕ₁~ϕ₁' (~-cong-↓ ϕ₂~ϕ₂'))
                                                                 (use-~ ϕ₂~ϕ₂' _ (here refl))) ⟩
    sub₂ ((ϕ₁' ∥ (ϕ₂' ↓)) ,ₖ (here refl & ϕ₂')) ~⟨ ~-sym (∥-▷ ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎

  invert : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) → Invert-ϕ ϕ
  invert ϕ = invert-ϕ'→ϕ (invert' ϕ)

  invert'-rec : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} (ϕ : S₁ –[ K ]→ S₂) → Σ[ ϕ' ∈ S₁ –[ K ]→ S₂ ] Invert-ϕ'-Rec ϕ ϕ' × ϕ ~ ϕ'
  invert'-rec ϕ with invert ϕ
  ... | ϕ~[]* ϕ~[] = []* , ϕ~[]* refl ϕ~[] , ϕ~[]
  ... | ϕ~,ₖ ϕ' x/t ϕ~ϕ',x/t with invert'-rec ϕ'
  ...   | ϕ'' , inv , ϕ'~ϕ'' = let ϕ~ϕ'',x/t = ~-trans ϕ~ϕ',x/t (~-cong-,ₖ ϕ'~ϕ'' refl) in
                               (ϕ'' ,ₖ x/t) , ϕ~,ₖ refl ϕ' x/t ϕ'' inv ϕ~ϕ',x/t ϕ~ϕ'',x/t , ϕ~ϕ'',x/t

  ~-cong-↑' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {s} {ϕ : S₁ –[ K ]→ S₂} {ϕ' : S₁ –[ K ]→ S₂} →
    ϕ ~ ϕ' →
    (ϕ ↑ s) ~ (ϕ' ↑ s)
  ~-cong-↑' {S₁ = S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' =
    (ϕ ↑ s)                         ~⟨ ↑-,ₖ ϕ s ⟩
    (wkₖ _ ϕ  ,ₖ id/` (here refl))  ~⟨ ~-cong-,ₖ (~-cong-wk' ϕ~ϕ') ~ₓ-refl ⟩
    (wkₖ _ ϕ' ,ₖ id/` (here refl))  ~⟨ ~-sym (↑-,ₖ ϕ' s) ⟩
    (ϕ' ↑ s)                        ~∎

  ~-cong-↑*' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} {S} {ϕ : S₁ –[ K ]→ S₂} {ϕ' : S₁ –[ K ]→ S₂} →
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

  dist-wk-,ₖ' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} s {s'} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s') →
    wkₖ s (ϕ ,ₖ x/t) ~' (wkₖ s ϕ ,ₖ Kit.wk K _ x/t)
  dist-wk-,ₖ' ⦃ K ⦄ s ϕ x/t = mk-~' λ where
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

  dist-wk-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} s {s'} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s') →
    wkₖ s (ϕ ,ₖ x/t) ~ (wkₖ s ϕ ,ₖ Kit.wk K _ x/t)
  dist-wk-,ₖ s ϕ x/t = ~'→~ (dist-wk-,ₖ' s ϕ x/t)

  dist-wk*-,ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S {s'} (ϕ : S₁ –[ K ]→ S₂) (x/t : S₂ ∋/⊢[ K ] s') →
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

  wkₖ*-▷▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S S' (ϕ : S₁ –[ K ]→ S₂)  →
    let sub = subst (S₁ –[ K ]→_) (++-assoc S S' S₂) in
    wkₖ* S (wkₖ* S' ϕ) ~ sub (wkₖ* (S' ▷▷ S) ϕ)
  wkₖ*-▷▷ ⦃ K ⦄ {S₁} {S₂} [] S' ϕ =
    let sub = subst (S₁ –[ K ]→_) (++-assoc [] S' S₂) in
    wkₖ* [] (wkₖ* S' ϕ)     ~⟨ wkₖ*-[] (wkₖ* S' ϕ) ⟩
    wkₖ* S' ϕ               ~⟨⟩
    sub (wkₖ* (S' ▷▷ []) ϕ) ~∎
  wkₖ*-▷▷ ⦃ K ⦄ {S₁} {S₂} (S ▷ s) S' ϕ =
    let sub = subst (S₁ –[ K ]→_) (++-assoc (S ▷ s) S' S₂) in
    let sub' = subst (S₁ –[ K ]→_) (++-assoc S S' S₂) in
    wkₖ* (S ▷ s) (wkₖ* S' ϕ)        ~⟨ wkₖ*-▷ S s (wkₖ* S' ϕ) ⟩
    wkₖ s (wkₖ* S (wkₖ* S' ϕ))      ~⟨ ~-cong-wk' (wkₖ*-▷▷ S S' ϕ) ⟩
    wkₖ s (sub' (wkₖ* (S' ▷▷ S) ϕ)) ~≡⟨ dist-subst' (_▷ s) (wkₖ s) (++-assoc S S' S₂) (++-assoc (S ▷ s) S' S₂) (wkₖ* (S' ▷▷ S) ϕ) ⟩
    sub (wkₖ s (wkₖ* (S' ▷▷ S) ϕ))  ~⟨ ~-cong-subst-S₂ (++-assoc (S ▷ s) S' S₂) (~-sym (wkₖ*-▷ (S' ▷▷ S) s ϕ)) ⟩
    sub (wkₖ* (S' ▷▷ (S ▷ s)) ϕ)    ~∎

  wkₖ-▷▷ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} S s (ϕ : S₁ –[ K ]→ S₂)  →
    let sub = subst (S₁ –[ K ]→_) (++-assoc S ([] ▷ s) S₂) in
    wkₖ* S (wkₖ s ϕ) ~ sub (wkₖ* (([] ▷ s) ▷▷ S) ϕ)
  wkₖ-▷▷ ⦃ K ⦄ {S₁} {S₂} S s ϕ =
    let sub = subst (S₁ –[ K ]→_) (++-assoc S ([] ▷ s) S₂) in
    wkₖ* S (wkₖ s ϕ)             ~⟨ ~-cong-wk*' (~-cong-wk' (~-sym (wkₖ*-[] ϕ))) ⟩
    wkₖ* S (wkₖ s (wkₖ* [] ϕ))   ~⟨ ~-cong-wk*' (~-sym (wkₖ*-▷ [] s ϕ)) ⟩
    wkₖ* S (wkₖ* ([] ▷ s) ϕ)     ~⟨ wkₖ*-▷▷ S ([] ▷ s) ϕ ⟩
    sub (wkₖ* (([] ▷ s) ▷▷ S) ϕ) ~∎

  dist-wk-↓' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S₂ s s'} → (ϕ : (S₁ ▷ s') –[ K ]→ S₂) →
    wkₖ s (ϕ ↓) ~' (wkₖ s ϕ ↓)
  dist-wk-↓' ⦃ K ⦄ {S₁} {S₂} {s} {s'} ϕ = mk-~' λ sx x →
    x & (wkₖ s (ϕ ↓))   ≡⟨ &-wkₖ-wk (ϕ ↓) x ⟩
    wk s (x & (ϕ ↓))    ≡⟨ cong (wk s) (&-↓ ϕ x) ⟩
    wk s (there x & ϕ)  ≡⟨ sym (&-wkₖ-wk ϕ (there x)) ⟩
    there x & (wkₖ s ϕ) ≡⟨ sym (&-↓ (wkₖ s ϕ) x) ⟩
    x & (wkₖ s ϕ ↓)     ∎

  dist-wk-↓ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S₂ s s'} → (ϕ : (S₁ ▷ s') –[ K ]→ S₂) →
    wkₖ s (ϕ ↓) ~ (wkₖ s ϕ ↓)
  dist-wk-↓ ϕ = ~'→~ (dist-wk-↓' ϕ)

  dist-wk*-↓ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁ S₂ S s'} → (ϕ : (S₁ ▷ s') –[ K ]→ S₂) →
    wkₖ* S (ϕ ↓) ~ (wkₖ* S ϕ ↓)
  dist-wk*-↓ ⦃ K ⦄ {S₁} {S₂} {S = []}    {s'} ϕ =
    wkₖ* [] (ϕ ↓)        ~⟨ wkₖ*-[] (ϕ ↓) ⟩
    (ϕ ↓)                ~⟨ ~-cong-↓ (~-sym (wkₖ*-[] ϕ)) ⟩
    (wkₖ* [] ϕ ↓)        ~∎
  dist-wk*-↓ ⦃ K ⦄ {S₁} {S₂} {S = S ▷ s} {s'} ϕ =
    wkₖ* (S ▷ s) (ϕ ↓)   ~⟨ wkₖ*-▷ S s (ϕ ↓) ⟩
    wkₖ s (wkₖ* S (ϕ ↓)) ~⟨ ~-cong-wk' (dist-wk*-↓ ϕ) ⟩
    wkₖ s (wkₖ* S ϕ ↓)   ~⟨ dist-wk-↓ (wkₖ* S ϕ) ⟩
    (wkₖ s (wkₖ* S ϕ) ↓) ~⟨ ~-cong-↓ (~-sym (wkₖ*-▷ S s ϕ)) ⟩
    (wkₖ* (S ▷ s) ϕ ↓)   ~∎

  ∥-wk : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂} s → (ϕ₁ : S₁₁ –[ K ]→ S₂) → (ϕ₂ : S₁₂ –[ K ]→ S₂) →
    wkₖ s (ϕ₁ ∥ ϕ₂) ~ (wkₖ s ϕ₁ ∥ wkₖ s ϕ₂)
  ∥-wk ⦃ K ⦄ {S₁₁} {[]} {S₂} s ϕ₁ ϕ₂ =
    wkₖ s (ϕ₁ ∥ ϕ₂)        ~⟨ ~-cong-wk' (∥-[] ϕ₁ ϕ₂) ⟩
    wkₖ s ϕ₁               ~⟨ ~-sym (∥-[] (wkₖ s ϕ₁) (wkₖ s ϕ₂)) ⟩
    (wkₖ s ϕ₁ ∥ wkₖ s ϕ₂)  ~∎
  ∥-wk ⦃ K ⦄ {S₁₁} {S₁₂ ▷ s₂} {S₂} s ϕ₁ ϕ₂ =
    let sub = subst (_–[ K ]→ S₂) (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁)) in
    let sub' = subst (_–[ K ]→ (S₂ ▷ s)) (sym (++-assoc ([] ▷ s₂) S₁₂ S₁₁)) in
    wkₖ s (ϕ₁ ∥ ϕ₂)                                              ~⟨ ~-cong-wk' (∥-▷ ϕ₁ ϕ₂) ⟩
    wkₖ s (sub ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))              ~≡⟨ dist-subst {F = _–[ K ]→ S₂} {G = _–[ K ]→ (S₂ ▷ s)}
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

  ∥-wk* : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂} S → (ϕ₁ : S₁₁ –[ K ]→ S₂) → (ϕ₂ : S₁₂ –[ K ]→ S₂) →
    wkₖ* S (ϕ₁ ∥ ϕ₂) ~ (wkₖ* S ϕ₁ ∥ wkₖ* S ϕ₂)
  ∥-wk* ⦃ K ⦄ {S₁₁} {S₁₂} {S₂} []      ϕ₁ ϕ₂ =
    wkₖ* [] (ϕ₁ ∥ ϕ₂)         ~⟨ wkₖ*-[] (ϕ₁ ∥ ϕ₂) ⟩
    (ϕ₁ ∥ ϕ₂)                 ~⟨ ~-sym (~-cong-∥ (wkₖ*-[] ϕ₁) (wkₖ*-[] ϕ₂)) ⟩
    (wkₖ* [] ϕ₁ ∥ wkₖ* [] ϕ₂) ~∎
  ∥-wk* ⦃ K ⦄ {S₁₁} {S₁₂} {S₂} (S ▷ s) ϕ₁ ϕ₂ =
    wkₖ* (S ▷ s) (ϕ₁ ∥ ϕ₂)                  ~⟨ wkₖ*-▷ S s (ϕ₁ ∥ ϕ₂) ⟩
    wkₖ s (wkₖ* S (ϕ₁ ∥ ϕ₂))                ~⟨ ~-cong-wk' (∥-wk* S ϕ₁ ϕ₂) ⟩
    wkₖ s (wkₖ* S ϕ₁ ∥ wkₖ* S ϕ₂)           ~⟨ ∥-wk s (wkₖ* S ϕ₁) (wkₖ* S ϕ₂) ⟩
    (wkₖ s (wkₖ* S ϕ₁) ∥ wkₖ s (wkₖ* S ϕ₂)) ~⟨ ~-sym (~-cong-∥ (wkₖ*-▷ S s ϕ₁) (wkₖ*-▷ S s ϕ₂)) ⟩
    (wkₖ* (S ▷ s) ϕ₁ ∥ wkₖ* (S ▷ s) ϕ₂)     ~∎

  ∥-↓ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂ s} → (ϕ₁ : S₁₁ –[ K ]→ S₂) → (ϕ₂ : (S₁₂ ▷ s) –[ K ]→ S₂) →
    (ϕ₁ ∥ ϕ₂) ↓ ~ ϕ₁ ∥ (ϕ₂ ↓)
  ∥-↓ ⦃ K ⦄ {S₁₁} {S₁₂} {S₂} {s} ϕ₁ ϕ₂ = mk-~ λ sx x →
    `/id (x & ((ϕ₁ ∥ ϕ₂) ↓))                           ≡⟨ cong `/id (&-↓ (ϕ₁ ∥ ϕ₂) x) ⟩
    `/id (there x & (ϕ₁ ∥ ϕ₂))                         ≡⟨ use-~ (∥-▷ ϕ₁ ϕ₂) _ (there x) ⟩
    `/id (there x & (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)) ≡⟨ cong `/id (&-,ₖ-there (ϕ₁ ∥ (ϕ₂ ↓)) _ x) ⟩
    `/id (x & ϕ₁ ∥ (ϕ₂ ↓))                             ∎

  &-∥-here : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {S₁₁ S₁₂ S₂ s} → (ϕ₁ : S₁₁ –[ K ]→ S₂) → (ϕ₂ : (S₁₂ ▷ s) –[ K ]→ S₂) →
    here refl & (ϕ₁ ∥ ϕ₂) ≡ here refl & ϕ₂
  &-∥-here ⦃ K ⦄ {S₁₁} {S₁₂} {S₂} {s} ϕ₁ ϕ₂ =
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

  id↑~id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ s S → id {S = S} ↑ s ~ id {S = S ▷ s}
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

  id↑*~id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ S' S → id {S = S} ↑* S' ~ id {S = S ▷▷ S'}
  id↑*~id []       S = ↑*-[] id
  id↑*~id (S' ▷ s) S =
    id ↑* (S' ▷ s) ~⟨ ↑*-▷ S' s id ⟩
    id ↑* S' ↑ s   ~⟨ ~-cong-↑' (id↑*~id S' S) ⟩
    id ↑ s         ~⟨ id↑~id _ _ ⟩
    id             ~∎

  -- Empty Substitution

  &-[]ₖ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {s} (x : _ ∋ s) → x & []ₖ ≡ id/` x
  &-[]ₖ ()

  &-[]ₖ' : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (ϕ : [] –[ K ]→ []) → ϕ ~ []ₖ
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
