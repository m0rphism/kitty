open import Kitty.Term.Modes

module Kitty.Term.Sub {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Level renaming (suc to lsuc)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open Modes 𝕄
open Terms 𝕋
open Kit ⦃ … ⦄
open _⊑ₖ_ ⦃ … ⦄

record Sub ℓ : Set (lsuc ℓ) where
  infixl  12  _,ₖ_
  infixl  11  _↑_  _↑*_
  infixl  9  _∥_
  infixl  8  _&_
  infix   4  _~_  _~'_

  field
    _–[_]→_ : List VarMode → Kit → List VarMode → Set ℓ

    []ₖ  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→ []
    _,ₖ_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂
    wkₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷ m)
    wkₖ* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ (µ₂ ▷▷ µ)
    _↑_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ m → (µ₁ ▷ m) –[ 𝕂 ]→ (µ₂ ▷ m)
    _↑*_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
    id   : ∀ ⦃ 𝕂 ⦄ {µ} → µ –[ 𝕂 ]→ µ
    []*  : ∀ ⦃ 𝕂 ⦄ {µ₂} → [] –[ 𝕂 ]→ µ₂
    _↓   : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → (µ₁ ▷ m) –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₂
    -- TODO: we might want this also to be Kit-heterogenous, to allow for talking about
    -- parallel compositions of two unknown, potentially different Kits.
    _∥_  : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} → (µ₁ –[ 𝕂 ]→ µ) → (µ₂ –[ 𝕂 ]→ µ) → ((µ₁ ▷▷ µ₂) –[ 𝕂 ]→ µ)
    ⦅_⦆  : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → (µ ▷ m) –[ 𝕂 ]→ µ
    -- Singleton renaming/substitution for terms with 1 free variable.
    -- Allows the term to be substituted to have arbitrary free variables.
    -- This is useful for things like pattern matching in combination with `_∥_`,
    -- where a matching substitution needs to be built up piece by piece.
    ⦅_⦆₀ : ∀ ⦃ 𝕂 ⦄ {µ m} → µ ∋/⊢ id/m→M m → ([] ▷ m) –[ 𝕂 ]→ µ

    _&_  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ ∋ m → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ∋/⊢ id/m→M m

    ι-→ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂₁ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₂

  -- Renaming/Substitution

  _–→_ : ⦃ 𝕂 : Kit ⦄ → List VarMode → List VarMode → Set ℓ
  _–→_ ⦃ 𝕂 ⦄ µ₁ µ₂ = µ₁ –[ 𝕂 ]→ µ₂

  -- Extensional Equality

  infix  4  _~ₘ_  _~ₜ[_]_  _~ₜ_

  _~ₘ_ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ → VarMode/TermMode ⦃ 𝕂₁ ⦄ → VarMode/TermMode ⦃ 𝕂₂ ⦄ → Set
  m/M₁ ~ₘ m/M₂ = m→M/id m/M₁ ≡ m→M/id m/M₂

  -- potentially useful for:
  --   ap/⋯-ap' : ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) 
  --              → id/` ⦃ 𝕂₁ ⦄ _ x ap/⋯ ϕ ~ₜ[ sym {!ι-m→M/id m!} ] & ϕ _ x
  _~ₜ[_]_ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ} {m/M₁} {m/M₂} → µ ∋/⊢[ 𝕂₁ ] m/M₁ → m→M/id m/M₁ ≡ m→M/id m/M₂ → µ ∋/⊢[ 𝕂₂ ] m/M₂ → Set
  _~ₜ[_]_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ} {m/M₁} {m/M₂} x/t₁ eq x/t₂ = subst (µ ⊢_) eq (`/id' ⦃ 𝕂₁ ⦄ x/t₁) ≡  `/id' ⦃ 𝕂₂ ⦄ x/t₂

  _~ₜ_ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ} {m} → µ ∋/⊢[ 𝕂₁ ] id/m→M m → µ ∋/⊢[ 𝕂₂ ] id/m→M m → Set
  _~ₜ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ} {m} x/t₁ x/t₂ =
    `/id x/t₁ ≡ `/id x/t₂
  -- _~ₜ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ} {m} x/t₁ x/t₂ =
  --   let eq = m→M/id (id/m→M ⦃ 𝕂₁ ⦄ m) ≡⟨ id/m→M/id m ⟩
  --            m→M m                    ≡⟨ sym (id/m→M/id m) ⟩
  --            m→M/id (id/m→M ⦃ 𝕂₂ ⦄ m) ∎
  --   in x/t₁ ~ₜ[ eq ] x/t₂

  _~_ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂₁ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₂ → Set
  ϕ₁ ~ ϕ₂ = ∀ m (x : _ ∋ m) → x & ϕ₁ ~ₜ x & ϕ₂
  -- ϕ₁ ~ ϕ₂ = ∀ m x → `/id (& ϕ₁ m x) ≡ `/id (& ϕ₂ m x)

  _~'_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Set
  ϕ₁ ~' ϕ₂ = ∀ m (x : _ ∋ m) → x & ϕ₁ ≡ x & ϕ₂

  ~→~' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂}
         → ϕ₁ ~ ϕ₂
         → ϕ₁ ~' ϕ₂
  ~→~' ϕ₁~ϕ₂ = λ m x → `/id-injective (ϕ₁~ϕ₂ m x)

  ~'→~ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂}
         → ϕ₁ ~' ϕ₂
         → ϕ₁ ~ ϕ₂
  ~'→~ ϕ₁~'ϕ₂ = λ m x → cong `/id (ϕ₁~'ϕ₂ m x)

  ~ₜ-refl :
    ∀ ⦃ 𝕂 ⦄ {µ} {m} {x/t : µ ∋/⊢[ 𝕂 ] id/m→M m}
    → x/t ~ₜ x/t
  ~ₜ-refl = cong (`/id) refl

  ~ₓ-refl :
    ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ} {m} {x : µ ∋ m}
    → id/` ⦃ 𝕂₁ ⦄ x ~ₜ id/` ⦃ 𝕂₂ ⦄ x
  ~ₓ-refl {x = x} =
    `/id (id/` x) ≡⟨ id/`/id x ⟩
    ` x               ≡⟨ sym (id/`/id x) ⟩
    `/id (id/` x) ∎

  ~-refl :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f : µ₁ –[ 𝕂 ]→ µ₂}
    → f ~ f
  ~-refl a b = refl

  ~-sym :
    ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ₁} {µ₂} {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂}
    → f ~ g
    → g ~ f
  ~-sym f~g a b = sym (f~g a b)

  ~-trans :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ ⦄ {µ₁} {µ₂} {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} {h : µ₁ –[ 𝕂₃ ]→ µ₂}
    → f ~ g
    → g ~ h
    → f ~ h
  ~-trans f~g g~h a b = trans (f~g a b) (g~h a b)

  ~-cong-subst-µ₁ :
    ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ₁} {µ₁'} {µ₂} {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} (eq : µ₁ ≡ µ₁')
    → f ~ g
    → subst (_–[ 𝕂₁ ]→ µ₂) eq f ~ subst (_–[ 𝕂₂ ]→ µ₂) eq g
  ~-cong-subst-µ₁ refl f~g = f~g

  ~-cong-subst-µ₂ :
    ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {µ₁} {µ₂} {µ₂'} {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂} (eq : µ₂ ≡ µ₂')
    → f ~ g
    → subst (µ₁ –[ 𝕂₁ ]→_) eq f ~ subst (µ₁ –[ 𝕂₂ ]→_) eq g
  ~-cong-subst-µ₂ refl f~g = f~g

  module ~-Reasoning where

    infix  3 _~∎
    infixr 2 _~⟨⟩_ step-~ step-~˘ step-~≡
    infix  1 begin~_

    private variable
      µ₁ µ₂ µ₃ : List VarMode
      ⦃ 𝕂 ⦄ : Kit
      f g h : µ₁ –[ 𝕂 ]→ µ₂

    begin~_ :
      ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ {f : µ₁ –[ 𝕂₁ ]→ µ₂} {g : µ₁ –[ 𝕂₂ ]→ µ₂}
      → f ~ g → f ~ g
    begin~_ x≡y = x≡y

    _~⟨⟩_ :
      ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ (f : µ₁ –[ 𝕂₁ ]→ µ₂) {g : µ₁ –[ 𝕂₂ ]→ µ₂}
      → f ~ g → f ~ g
    _ ~⟨⟩ x~y = x~y

    step-~ :
      ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ ⦄ (f : µ₁ –[ 𝕂₁ ]→ µ₂) {g : µ₁ –[ 𝕂₂ ]→ µ₂} {h : µ₁ –[ 𝕂₃ ]→ µ₂}
      → g ~ h → f ~ g → f ~ h
    step-~ _ g~h f~g = ~-trans f~g g~h

    step-~˘ :
      ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ ⦄ (f : µ₁ –[ 𝕂₁ ]→ µ₂) {g : µ₁ –[ 𝕂₂ ]→ µ₂} {h : µ₁ –[ 𝕂₃ ]→ µ₂}
      → g ~ h → g ~ f → f ~ h
    step-~˘ _ g~h g~f = ~-trans (~-sym g~f) g~h

    step-~≡ :
      ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ (f : µ₁ –[ 𝕂₁ ]→ µ₂) {g : µ₁ –[ 𝕂₁ ]→ µ₂} {h : µ₁ –[ 𝕂₂ ]→ µ₂}
      → g ~ h → f ≡ g → f ~ h
    step-~≡ f g~h f≡g = ~-trans (subst (f ~_) f≡g ~-refl ) g~h

    _~∎ :
      ∀ ⦃ 𝕂 ⦄ (f : µ₁ –[ 𝕂 ]→ µ₂)
      → f ~ f
    _~∎ _ = ~-refl

    syntax step-~  f g~h f~g = f ~⟨ f~g ⟩ g~h
    syntax step-~≡  f g~h f≡g = f ~≡⟨ f≡g ⟩ g~h
    syntax step-~˘ f g~h g~f = f ~˘⟨ g~f ⟩ g~h

  ~'-refl :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f : µ₁ –[ 𝕂 ]→ µ₂}
    → f ~' f
  ~'-refl a b = refl

  ~'-sym :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f g : µ₁ –[ 𝕂 ]→ µ₂}
    → f ~' g
    → g ~' f
  ~'-sym f~'g a b = sym (f~'g a b)

  ~'-trans :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {f g h : µ₁ –[ 𝕂 ]→ µ₂} 
    → f ~' g
    → g ~' h
    → f ~' h
  ~'-trans f~'g g~'h a b = trans (f~'g a b) (g~'h a b)

  ~'-cong-subst-µ₁ :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₁'} {µ₂} {f g : µ₁ –[ 𝕂 ]→ µ₂} (eq : µ₁ ≡ µ₁')
    → f ~' g
    → subst (_–[ 𝕂 ]→ µ₂) eq f ~' subst (_–[ 𝕂 ]→ µ₂) eq g
  ~'-cong-subst-µ₁ refl f~'g = f~'g

  ~'-cong-subst-µ₂ :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₂'} {f g : µ₁ –[ 𝕂 ]→ µ₂} (eq : µ₂ ≡ µ₂')
    → f ~' g
    → subst (µ₁ –[ 𝕂 ]→_) eq f ~' subst (µ₁ –[ 𝕂 ]→_) eq g
  ~'-cong-subst-µ₂ refl f~'g = f~'g

  module ~'-Reasoning where

    infix  3 _~'∎
    infixr 2 _~'⟨⟩_ step-~' step-~'˘ step-~'≡
    infix  1 begin~'_

    private variable
      µ₁ µ₂ µ₃ : List VarMode
      ⦃ 𝕂 ⦄ : Kit
      f g h : µ₁ –[ 𝕂 ]→ µ₂

    begin~'_ :
      ∀ ⦃ 𝕂 ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂}
      → f ~' g → f ~' g
    begin~'_ x≡y = x≡y

    _~'⟨⟩_ :
      ∀ ⦃ 𝕂 ⦄ (f {g} : µ₁ –[ 𝕂 ]→ µ₂)
      → f ~' g → f ~' g
    _ ~'⟨⟩ x~'y = x~'y

    step-~' :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~' h → f ~' g → f ~' h
    step-~' _ g~'h f~'g = ~'-trans f~'g g~'h

    step-~'˘ :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~' h → g ~' f → f ~' h
    step-~'˘ _ g~'h g~'f = ~'-trans (~'-sym g~'f) g~'h

    step-~'≡ :
      ∀ ⦃ 𝕂 ⦄ (f {g h} : µ₁ –[ 𝕂 ]→ µ₂)
      → g ~' h → f ≡ g → f ~' h
    step-~'≡ f g~'h f≡g = ~'-trans (subst (f ~'_) f≡g ~'-refl ) g~'h

    _~'∎ :
      ∀ ⦃ 𝕂 ⦄ (f : µ₁ –[ 𝕂 ]→ µ₂)
      → f ~' f
    _~'∎ _ = ~'-refl

    syntax step-~'  f g~'h f~'g = f ~'⟨ f~'g ⟩ g~'h
    syntax step-~'≡  f g~'h f≡g = f ~'≡⟨ f≡g ⟩ g~'h
    syntax step-~'˘ f g~'h g~'f = f ~'˘⟨ g~'f ⟩ g~'h

  data Invert-ϕ ⦃ 𝕂 ⦄ {µ₂} : {µ₁ : List VarMode} → µ₁ –[ 𝕂 ]→ µ₂ → Set ℓ where
    ϕ~[]* : ∀ {ϕ} →
      ϕ ~ []* →
      Invert-ϕ ϕ
    ϕ~,ₖ : ∀ {µ₁' m₁ ϕ} →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      ϕ ~ (ϕ' ,ₖ x/t) →
      Invert-ϕ ϕ

  data Invert-ϕ' ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) : Set ℓ where
    ϕ~[]* :
      (eq : µ₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ' ϕ
    ϕ~,ₖ : ∀ {µ₁' m₁} →
      (eq : µ₁ ≡ µ₁' ▷ m₁) →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      Invert-ϕ' ϕ

  data Invert-ϕ'-Rec ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) : µ₁ –[ 𝕂 ]→ µ₂ → Set ℓ where
    ϕ~[]* :
      (eq : µ₁ ≡ []) →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub []* →
      Invert-ϕ'-Rec ϕ (sub []*)
    ϕ~,ₖ : ∀ {µ₁' m₁} →
      (eq : µ₁ ≡ µ₁' ▷ m₁) →
      (ϕ' : µ₁' –[ 𝕂 ]→ µ₂) →
      (x/t : µ₂ ∋/⊢ id/m→M m₁) →
      (ϕ'' : µ₁' –[ 𝕂 ]→ µ₂) →
      Invert-ϕ'-Rec ϕ' ϕ'' →
      let sub = subst (_–[ 𝕂 ]→ µ₂) (sym eq) in
      ϕ ~ sub (ϕ' ,ₖ x/t) →
      ϕ ~ sub (ϕ'' ,ₖ x/t) →
      Invert-ϕ'-Rec ϕ (sub (ϕ'' ,ₖ x/t))

  invert-ϕ'→ϕ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  invert-ϕ'→ϕ (ϕ~[]* refl ϕ~) = ϕ~[]* ϕ~
  invert-ϕ'→ϕ (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

  -- requires dependent subst
  -- invert-ϕ'→ϕ' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} → Invert-ϕ' ϕ → Invert-ϕ ϕ
  -- invert-ϕ'→ϕ' {µ₁} {µ₂} {ϕ} (ϕ~[]* µ₁≡[] ϕ~) = {!subst₂ (λ ■ ■' → Invert-ϕ {µ₁ = ■} ■') ? ? {!ϕ~[]* ϕ~!}!}
  -- invert-ϕ'→ϕ' (ϕ~,ₖ refl ϕ' x/t ϕ~) = ϕ~,ₖ ϕ' x/t ϕ~

_–[_;_]→_ : ∀ {ℓ} → List VarMode → Kit → Sub ℓ → List VarMode → Set ℓ
_–[_;_]→_ µ₁ 𝕂 𝕊 µ₂ = Sub._–[_]→_ 𝕊 µ₁ 𝕂 µ₂

record SubWithLaws ℓ : Set (lsuc ℓ) where
  open Sub ⦃ … ⦄
  field
    ⦃ SubWithLaws-Sub ⦄ : Sub ℓ

    &-,ₖ-here : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
                  → here refl & (ϕ ,ₖ x/t) ≡ x/t
    &-,ₖ-there : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) {m'} (x : µ₁ ∋ m')
                   → there x & (ϕ ,ₖ x/t) ≡ x & ϕ

    &-wkₖ-wk : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
                 → x & wkₖ m ϕ ≡ wk m (x & ϕ)

    &-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : (µ₁ ▷ m) –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
      → x & (ϕ ↓) ≡ there x & ϕ

    wkₖ*-[] : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → wkₖ* [] ϕ ~ ϕ
    wkₖ*-▷ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → wkₖ* (µ ▷ m) ϕ ~ wkₖ m (wkₖ* µ ϕ)

    ↑-,ₖ  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) m
      → (ϕ ↑ m) ~ (wkₖ m ϕ ,ₖ id/` (here refl))

    ↑*-[]  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → (ϕ ↑* []) ~ ϕ

    ↑*-▷  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
      → (ϕ ↑* (µ ▷ m)) ~ ((ϕ ↑* µ) ↑ m)

    id-[] : ∀ ⦃ 𝕂 : Kit ⦄
      → id {µ = []} ~ []ₖ

    id-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
      → id {µ = µ ▷ m} ~ (id {µ = µ} ↑ m)

    []*-[]  : ∀ ⦃ 𝕂 : Kit ⦄
      → []* {µ₂ = []} ~ []ₖ

    []*-▷  : ∀ ⦃ 𝕂 : Kit ⦄ {µ m}
      → []* {µ₂ = µ ▷ m} ~ wkₖ m ([]* {µ₂ = µ})

    ↓-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
      → ((ϕ ,ₖ x/t) ↓) ~ ϕ

    ∥-[] : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ} → (ϕ₁ : µ₁ –[ 𝕂 ]→ µ) → (ϕ₂ : [] –[ 𝕂 ]→ µ)
      → (ϕ₁ ∥ ϕ₂) ~ ϕ₁

    ∥-▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ µ m} → (ϕ₁ : µ₁ –[ 𝕂 ]→ µ) → (ϕ₂ : (µ₂ ▷ m) –[ 𝕂 ]→ µ)
      → (ϕ₁ ∥ ϕ₂) ~ subst (_–[ 𝕂 ]→ µ) (sym (++-assoc ([] ▷ m) µ₂ µ₁)) ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂))

    ⦅⦆-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m} (x/t : µ ∋/⊢ id/m→M m) →
      ⦅ x/t ⦆ ~ (id ,ₖ x/t)

    ⦅⦆₀-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ m} (x/t : µ ∋/⊢ id/m→M m) →
      ⦅ x/t ⦆₀ ~ ([]* ,ₖ x/t)

    invert' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ' ϕ

    ι-ap-→ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) (x : µ₁ ∋ m)
             → let sub = subst (µ₂ ∋/⊢_) (ι-id/m→M m ) in
               x & (ι-→ ϕ) ≡ sub (ι-∋/⊢ (x & ϕ))

  open ~-Reasoning

  ι-~-→ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ : 𝕂₁ ⊑ₖ 𝕂₂ ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
          → ι-→ ϕ ~ ϕ
  ι-~-→ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊑𝕂₂ ⦄ {µ₁} {µ₂} ϕ m x =
    let sub = subst (µ₂ ∋/⊢_) (ι-id/m→M m ) in
    `/id (x & ι-→ ϕ)           ≡⟨ cong `/id (ι-ap-→ ϕ x) ⟩
    `/id (sub (ι-∋/⊢ (x & ϕ))) ≡⟨ ι-∋/⊢-~ₜ (x & ϕ) ⟩
    `/id (x & ϕ)               ∎

  &-id : ∀ ⦃ 𝕂 : Kit ⦄ {µ} {m} (x : µ ∋ m)
           → x & id {µ = µ} ≡ id/` x
  &-id ⦃ 𝕂 ⦄ {µ ▷ m'} {m} x@(here refl) =
    x & (id {µ = µ ▷ m'})              ≡⟨ ~→~' id-▷ m' x ⟩
    x & (id {µ = µ} ↑ m')              ≡⟨ ~→~' (↑-,ₖ id m') _ x ⟩
    x & (wkₖ _ (id {µ = µ}) ,ₖ id/` x) ≡⟨ &-,ₖ-here (wkₖ _ (id {µ = µ})) (id/` x) ⟩
    id/` x                             ∎
  &-id ⦃ 𝕂 ⦄ {µ ▷ m'} {m} (there x) =
    there x & (id {µ = µ ▷ m'})                        ≡⟨ ~→~' id-▷ _ (there x) ⟩
    there x & (id {µ = µ} ↑ m')                        ≡⟨ ~→~' (↑-,ₖ id m') _ (there x) ⟩
    there x & (wkₖ _ (id {µ = µ}) ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ _ (id {µ = µ})) (id/` (here refl)) x ⟩
    x & (wkₖ _ (id {µ = µ}))                           ≡⟨ &-wkₖ-wk id x ⟩
    wk m' (x & id {µ = µ})                             ≡⟨ cong (wk m') (&-id x) ⟩
    wk m' (id/` x)                                     ≡⟨ wk-id/` m' x ⟩
    id/` (there x)                                     ∎

  -- id-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ µ'}
  --   → id {µ ▷▷ µ'} ~ (id {µ} ↑* µ')
  -- id-▷▷ {µ' = []} = ~-sym (↑*-[] id)
  -- id-▷▷ {µ' = µ' ▷ m} = ~-trans {!id-▷▷!} (~-trans {!id-▷!} (~-sym (↑*-▷ µ' m id)))

  &-↑-here :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
    → here refl & (ϕ ↑ m) ≡ id/` (here refl)
  &-↑-here ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} ϕ =
    here refl & (ϕ ↑ m)                       ≡⟨ ~→~' (↑-,ₖ ϕ m) m (here refl) ⟩
    here refl & (wkₖ m ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-here (wkₖ m ϕ) _ ⟩
    id/` (here refl)                          ∎

  &-↑-there :
    ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x : µ₁ ∋ m')
    → there x & (ϕ ↑ m) ≡ wk m (x & ϕ)
  &-↑-there ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} ϕ x =
    there x & (ϕ ↑ m)                       ≡⟨ ~→~' (↑-,ₖ ϕ m) m' (there x) ⟩
    there x & (wkₖ m ϕ ,ₖ id/` (here refl)) ≡⟨ &-,ₖ-there (wkₖ m ϕ) _ x ⟩
    x & wkₖ m ϕ                             ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk m (x & ϕ)                            ∎

  -- Weakening preserves Homotopy

  ~'-cong-wk : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ ~' ϕ' →
    wkₖ m ϕ ~' wkₖ m ϕ'
  ~'-cong-wk {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
    x & wkₖ _ ϕ   ≡⟨ &-wkₖ-wk ϕ x ⟩
    wk _ (x & ϕ)  ≡⟨ cong (wk _) (ϕ~ϕ' mx x) ⟩
    wk _ (x & ϕ') ≡⟨ sym (&-wkₖ-wk ϕ' x) ⟩
    x & wkₖ _ ϕ'  ∎

  ~-cong-wk' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ ~ ϕ' →
    wkₖ m ϕ ~ wkₖ m ϕ'
  ~-cong-wk' ϕ~ϕ' = ~'→~ (~'-cong-wk (~→~' ϕ~ϕ'))

  ~-cong-wk*' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ ~ ϕ' →
    wkₖ* µ ϕ ~ wkₖ* µ ϕ'
  ~-cong-wk*' {µ = []} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
    wkₖ* [] ϕ' ~∎
  ~-cong-wk*' {µ = µ ▷ m} {ϕ} {ϕ'} ϕ~ϕ' =
    wkₖ* (µ ▷ m) ϕ    ~⟨ wkₖ*-▷ µ m ϕ ⟩
    wkₖ m (wkₖ* µ ϕ)  ~⟨ ~-cong-wk' (~-cong-wk*' ϕ~ϕ') ⟩
    wkₖ m (wkₖ* µ ϕ') ~⟨ ~-sym (wkₖ*-▷ µ m ϕ') ⟩
    wkₖ* (µ ▷ m) ϕ' ~∎

  -- Lifting preserves Homotopy

  ~-cong-,ₖ : ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {m}
    {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂}
    {x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m} {x/t' : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m} →
    ϕ ~ ϕ' →
    x/t ~ₜ x/t' →
    (ϕ ,ₖ x/t) ~ (ϕ' ,ₖ x/t')
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {.mx} {ϕ} {ϕ'} {x/t} {x/t'} ϕ~ϕ' x/t≡x/t' mx x@(here refl) =
    `/id (x & (ϕ ,ₖ x/t))   ≡⟨ cong (`/id) (&-,ₖ-here ϕ x/t) ⟩
    `/id x/t                ≡⟨ x/t≡x/t' ⟩
    `/id x/t'               ≡⟨ cong (`/id) (sym (&-,ₖ-here ϕ' x/t')) ⟩
    `/id (x & (ϕ' ,ₖ x/t')) ∎
  ~-cong-,ₖ {µ₁ = µ₁} {µ₂} {m} {ϕ} {ϕ'} {x/t} {x/t'} ϕ~ϕ' x/t≡x/t' mx x@(there y) =
    `/id (x & (ϕ ,ₖ x/t))   ≡⟨ cong (`/id) (&-,ₖ-there ϕ x/t y) ⟩
    `/id (y & ϕ)            ≡⟨ ϕ~ϕ' mx y ⟩
    `/id (y & ϕ')           ≡⟨ cong (`/id) (sym (&-,ₖ-there ϕ' x/t' y)) ⟩
    `/id (x & (ϕ' ,ₖ x/t')) ∎

  ~'-cong-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂} {x/t x/t' : µ₂ ∋/⊢[ 𝕂 ] id/m→M m} →
    ϕ ~' ϕ' →
    x/t ≡ x/t' →
    (ϕ ,ₖ x/t) ~' (ϕ' ,ₖ x/t')
  ~'-cong-,ₖ ϕ~ϕ' x/t≡x/t' = ~→~' (~-cong-,ₖ (~'→~ ϕ~ϕ') (cong (`/id) x/t≡x/t'))

  ~-cong-↓ : ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {m} {ϕ : (µ₁ ▷ m) –[ 𝕂₁ ]→ µ₂} {ϕ' : (µ₁ ▷ m) –[ 𝕂₂ ]→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↓) ~ (ϕ' ↓)
  ~-cong-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
    `/id (x & (ϕ  ↓))   ≡⟨ cong (`/id) (&-↓ ϕ x) ⟩
    `/id (there x & ϕ ) ≡⟨ ϕ~ϕ' mx (there x) ⟩
    `/id (there x & ϕ') ≡⟨ cong (`/id) (sym (&-↓ ϕ' x)) ⟩
    `/id (x & (ϕ' ↓))   ∎

  ~-cong-∥ :
    ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ {µ₁₁} {µ₁₂} {µ₂}
      {ϕ₁  : µ₁₁ –[ 𝕂₁ ]→ µ₂}
      {ϕ₁' : µ₁₁ –[ 𝕂₂ ]→ µ₂}
      {ϕ₂  : µ₁₂ –[ 𝕂₁ ]→ µ₂}
      {ϕ₂' : µ₁₂ –[ 𝕂₂ ]→ µ₂}
    → ϕ₁ ~ ϕ₁'
    → ϕ₂ ~ ϕ₂'
    → (ϕ₁ ∥ ϕ₂) ~ (ϕ₁' ∥ ϕ₂')
  ~-cong-∥ {µ₁₁ = µ₁₁} {[]}      {µ₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    (ϕ₁ ∥ ϕ₂)   ~⟨ ∥-[] ϕ₁ ϕ₂ ⟩
    ϕ₁          ~⟨ ϕ₁~ϕ₁' ⟩
    ϕ₁'         ~⟨ ~-sym (∥-[] ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎
  ~-cong-∥ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ₁₁} {µ₁₂ ▷ m} {µ₂} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' =
    let sub₁ = subst (_–[ 𝕂₁ ]→ µ₂) (sym (++-assoc ([] ▷ m) µ₁₂ µ₁₁)) in
    let sub₂ = subst (_–[ 𝕂₂ ]→ µ₂) (sym (++-assoc ([] ▷ m) µ₁₂ µ₁₁)) in
    (ϕ₁ ∥ ϕ₂)                                      ~⟨ ∥-▷ ϕ₁ ϕ₂ ⟩
    sub₁ ((ϕ₁  ∥ (ϕ₂  ↓)) ,ₖ (here refl & ϕ₂)) ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m) µ₁₂ µ₁₁))
                                                      (~-cong-,ₖ (~-cong-∥ ϕ₁~ϕ₁' (~-cong-↓ ϕ₂~ϕ₂'))
                                                                 (ϕ₂~ϕ₂' _ (here refl))) ⟩
    sub₂ ((ϕ₁' ∥ (ϕ₂' ↓)) ,ₖ (here refl & ϕ₂')) ~⟨ ~-sym (∥-▷ ϕ₁' ϕ₂') ⟩
    (ϕ₁' ∥ ϕ₂') ~∎

  invert : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Invert-ϕ ϕ
  invert ϕ = invert-ϕ'→ϕ (invert' ϕ)

  invert'-rec : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) → Σ[ ϕ' ∈ µ₁ –[ 𝕂 ]→ µ₂ ] Invert-ϕ'-Rec ϕ ϕ' × ϕ ~ ϕ'
  invert'-rec ϕ with invert ϕ
  ... | ϕ~[]* ϕ~[] = []* , ϕ~[]* refl ϕ~[] , ϕ~[]
  ... | ϕ~,ₖ ϕ' x/t ϕ~ϕ',x/t with invert'-rec ϕ'
  ...   | ϕ'' , inv , ϕ'~ϕ'' = let ϕ~ϕ'',x/t = ~-trans ϕ~ϕ',x/t (~-cong-,ₖ ϕ'~ϕ'' refl) in
                               (ϕ'' ,ₖ x/t) , ϕ~,ₖ refl ϕ' x/t ϕ'' inv ϕ~ϕ',x/t ϕ~ϕ'',x/t , ϕ~ϕ'',x/t

  ~-cong-↑' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↑ m) ~ (ϕ' ↑ m)
  ~-cong-↑' {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' =
    (ϕ ↑ m)                           ~⟨ ↑-,ₖ ϕ m ⟩
    (wkₖ _ ϕ  ,ₖ id/` (here refl))  ~⟨ ~-cong-,ₖ (~-cong-wk' ϕ~ϕ') ~ₓ-refl ⟩
    (wkₖ _ ϕ' ,ₖ id/` (here refl))  ~⟨ ~-sym (↑-,ₖ ϕ' m) ⟩
    (ϕ' ↑ m)                          ~∎

  ~-cong-↑*' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ ~ ϕ' →
    (ϕ ↑* µ) ~ (ϕ' ↑* µ)
  ~-cong-↑*' {µ = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
    ϕ          ~⟨ ϕ~ϕ' ⟩
    ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
    (ϕ' ↑* []) ~∎
  ~-cong-↑*' {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
    (ϕ ↑* (µ ▷ m))  ~⟨ ↑*-▷ µ m ϕ ⟩
    (ϕ ↑* µ) ↑ m    ~⟨ ~-cong-↑' (~-cong-↑*' ϕ~ϕ') ⟩
    (ϕ' ↑* µ) ↑ m   ~⟨ ~-sym (↑*-▷ µ m ϕ') ⟩
    (ϕ' ↑* (µ ▷ m)) ~∎

  dist-wk-,ₖ' : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} m {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m') →
    wkₖ m (ϕ ,ₖ x/t) ~' (wkₖ m ϕ ,ₖ Kit.wk 𝕂 _ x/t)
  dist-wk-,ₖ' ⦃ 𝕂 ⦄ m ϕ x/t mx (here refl) =
    here refl & (wkₖ m (ϕ ,ₖ x/t))    ≡⟨ &-wkₖ-wk (ϕ ,ₖ x/t) (here refl) ⟩
    wk m (here refl & (ϕ ,ₖ x/t))     ≡⟨ cong (wk m) (&-,ₖ-here ϕ x/t) ⟩
    wk m x/t                          ≡⟨ sym (&-,ₖ-here (wkₖ m ϕ) (wk m x/t)) ⟩
    here refl & (wkₖ m ϕ ,ₖ wk m x/t) ∎
  dist-wk-,ₖ' m ϕ x/t mx (there x) =
    there x & (wkₖ _ (ϕ ,ₖ x/t))    ≡⟨ &-wkₖ-wk (ϕ ,ₖ x/t) (there x) ⟩
    wk _ (there x & (ϕ ,ₖ x/t))     ≡⟨ cong (wk _) (&-,ₖ-there ϕ x/t x) ⟩
    wk _ (x & ϕ)                    ≡⟨ sym (&-wkₖ-wk ϕ x) ⟩
    x & (wkₖ _ ϕ)                   ≡⟨ sym (&-,ₖ-there (wkₖ m ϕ) (wk _ x/t) x) ⟩
    there x & (wkₖ _ ϕ ,ₖ wk _ x/t) ∎

  dist-wk-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} m {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m') →
    wkₖ m (ϕ ,ₖ x/t) ~ (wkₖ m ϕ ,ₖ Kit.wk 𝕂 _ x/t)
  dist-wk-,ₖ m ϕ x/t = ~'→~ (dist-wk-,ₖ' m ϕ x/t)

  dist-wk*-,ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ {m'} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m') →
    wkₖ* µ (ϕ ,ₖ x/t) ~ (wkₖ* µ ϕ ,ₖ wk* _ x/t)
  dist-wk*-,ₖ []      ϕ x/t =
    wkₖ* [] (ϕ ,ₖ x/t)       ~⟨ wkₖ*-[] (ϕ ,ₖ x/t) ⟩
    ϕ ,ₖ x/t                 ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-[] ϕ)) refl ⟩
    (wkₖ* [] ϕ ,ₖ x/t)       ~⟨⟩
    (wkₖ* [] ϕ ,ₖ wk* _ x/t) ~∎
  dist-wk*-,ₖ (µ ▷ m) ϕ x/t =
    wkₖ* (µ ▷ m) (ϕ ,ₖ x/t)                ~⟨ wkₖ*-▷ µ m (ϕ ,ₖ x/t) ⟩
    wkₖ m (wkₖ* µ (ϕ ,ₖ x/t))              ~⟨ ~-cong-wk' (dist-wk*-,ₖ µ ϕ x/t) ⟩
    wkₖ m (wkₖ* µ ϕ ,ₖ wk* _ x/t)          ~⟨ dist-wk-,ₖ m (wkₖ* µ ϕ) (wk* _ x/t) ⟩
    (wkₖ m (wkₖ* µ ϕ) ,ₖ wk m (wk* µ x/t)) ~⟨ ~-cong-,ₖ (~-sym (wkₖ*-▷ µ m ϕ)) refl ⟩
    (wkₖ* (µ ▷ m) ϕ ,ₖ wk* _ x/t)          ~∎

  open import Kitty.Util.SubstProperties

  wkₖ*-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ µ' (ϕ : µ₁ –[ 𝕂 ]→ µ₂)  →
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
    wkₖ* µ (wkₖ* µ' ϕ) ~ sub (wkₖ* (µ' ▷▷ µ) ϕ)
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} [] µ' ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc [] µ' µ₂) in
    wkₖ* [] (wkₖ* µ' ϕ)     ~⟨ wkₖ*-[] (wkₖ* µ' ϕ) ⟩
    wkₖ* µ' ϕ               ~⟨⟩
    sub (wkₖ* (µ' ▷▷ []) ϕ) ~∎
  wkₖ*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (µ ▷ m) µ' ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc (µ ▷ m) µ' µ₂) in
    let sub' = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
    wkₖ* (µ ▷ m) (wkₖ* µ' ϕ)        ~⟨ wkₖ*-▷ µ m (wkₖ* µ' ϕ) ⟩
    wkₖ m (wkₖ* µ (wkₖ* µ' ϕ))      ~⟨ ~-cong-wk' (wkₖ*-▷▷ µ µ' ϕ) ⟩
    wkₖ m (sub' (wkₖ* (µ' ▷▷ µ) ϕ)) ~≡⟨ dist-subst' (_▷ m) (wkₖ m) (++-assoc µ µ' µ₂) (++-assoc (µ ▷ m) µ' µ₂) (wkₖ* (µ' ▷▷ µ) ϕ) ⟩
    sub (wkₖ m (wkₖ* (µ' ▷▷ µ) ϕ))  ~⟨ ~-cong-subst-µ₂ (++-assoc (µ ▷ m) µ' µ₂) (~-sym (wkₖ*-▷ (µ' ▷▷ µ) m ϕ)) ⟩
    sub (wkₖ* (µ' ▷▷ (µ ▷ m)) ϕ)    ~∎

  wkₖ-▷▷ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} µ m (ϕ : µ₁ –[ 𝕂 ]→ µ₂)  →
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ ([] ▷ m) µ₂) in
    wkₖ* µ (wkₖ m ϕ) ~ sub (wkₖ* (([] ▷ m) ▷▷ µ) ϕ)
  wkₖ-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ m ϕ =
    let sub = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ ([] ▷ m) µ₂) in
    wkₖ* µ (wkₖ m ϕ)             ~⟨ ~-cong-wk*' (~-cong-wk' (~-sym (wkₖ*-[] ϕ))) ⟩
    wkₖ* µ (wkₖ m (wkₖ* [] ϕ))   ~⟨ ~-cong-wk*' (~-sym (wkₖ*-▷ [] m ϕ)) ⟩
    wkₖ* µ (wkₖ* ([] ▷ m) ϕ)     ~⟨ wkₖ*-▷▷ µ ([] ▷ m) ϕ ⟩
    sub (wkₖ* (([] ▷ m) ▷▷ µ) ϕ) ~∎

  dist-wk-↓' : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ m m'} → (ϕ : (µ₁ ▷ m') –[ 𝕂 ]→ µ₂) →
    wkₖ m (ϕ ↓) ~' (wkₖ m ϕ ↓)
  dist-wk-↓' ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {m'} ϕ mx x =
    x & (wkₖ m (ϕ ↓))   ≡⟨ &-wkₖ-wk (ϕ ↓) x ⟩
    wk m (x & (ϕ ↓))    ≡⟨ cong (wk m) (&-↓ ϕ x) ⟩
    wk m (there x & ϕ)  ≡⟨ sym (&-wkₖ-wk ϕ (there x)) ⟩
    there x & (wkₖ m ϕ) ≡⟨ sym (&-↓ (wkₖ m ϕ) x) ⟩
    x & (wkₖ m ϕ ↓)     ∎

  dist-wk-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ m m'} → (ϕ : (µ₁ ▷ m') –[ 𝕂 ]→ µ₂) →
    wkₖ m (ϕ ↓) ~ (wkₖ m ϕ ↓)
  dist-wk-↓ ϕ = ~'→~ (dist-wk-↓' ϕ)

  dist-wk*-↓ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ m'} → (ϕ : (µ₁ ▷ m') –[ 𝕂 ]→ µ₂) →
    wkₖ* µ (ϕ ↓) ~ (wkₖ* µ ϕ ↓)
  dist-wk*-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ = []}    {m'} ϕ =
    wkₖ* [] (ϕ ↓) ~⟨ wkₖ*-[] (ϕ ↓) ⟩
    (ϕ ↓)         ~⟨ ~-cong-↓ (~-sym (wkₖ*-[] ϕ)) ⟩
    (wkₖ* [] ϕ ↓) ~∎
  dist-wk*-↓ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ = µ ▷ m} {m'} ϕ =
    wkₖ* (µ ▷ m) (ϕ ↓) ~⟨ wkₖ*-▷ µ m (ϕ ↓) ⟩
    wkₖ m (wkₖ* µ (ϕ ↓)) ~⟨ ~-cong-wk' (dist-wk*-↓ ϕ) ⟩
    wkₖ m (wkₖ* µ ϕ ↓)   ~⟨ dist-wk-↓ (wkₖ* µ ϕ) ⟩
    (wkₖ m (wkₖ* µ ϕ) ↓) ~⟨ ~-cong-↓ (~-sym (wkₖ*-▷ µ m ϕ)) ⟩
    (wkₖ* (µ ▷ m) ϕ ↓) ~∎

  ∥-wk : ∀ ⦃ 𝕂 ⦄ {µ₁₁ µ₁₂ µ₂} m → (ϕ₁ : µ₁₁ –[ 𝕂 ]→ µ₂) → (ϕ₂ : µ₁₂ –[ 𝕂 ]→ µ₂) →
    wkₖ m (ϕ₁ ∥ ϕ₂) ~ (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂)
  ∥-wk ⦃ 𝕂 ⦄ {µ₁₁} {[]} {µ₂} m ϕ₁ ϕ₂ =
    wkₖ m (ϕ₁ ∥ ϕ₂)        ~⟨ ~-cong-wk' (∥-[] ϕ₁ ϕ₂) ⟩
    wkₖ m ϕ₁               ~⟨ ~-sym (∥-[] (wkₖ m ϕ₁) (wkₖ m ϕ₂)) ⟩
    (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂)  ~∎
  ∥-wk ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂ ▷ m₂} {µ₂} m ϕ₁ ϕ₂ =
    let sub = subst (_–[ 𝕂 ]→ µ₂) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁)) in
    let sub' = subst (_–[ 𝕂 ]→ (µ₂ ▷ m)) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁)) in
    wkₖ m (ϕ₁ ∥ ϕ₂)                                                  ~⟨ ~-cong-wk' (∥-▷ ϕ₁ ϕ₂) ⟩
    wkₖ m (sub ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))              ~≡⟨ dist-subst {F = _–[ 𝕂 ]→ µ₂} {G = _–[ 𝕂 ]→ (µ₂ ▷ m)}
                                                                                    (wkₖ m) (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                                    ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)) ⟩
    sub' (wkₖ m ((ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))             ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (dist-wk-,ₖ m (ϕ₁ ∥ (ϕ₂ ↓)) (here refl & ϕ₂)) ⟩
    sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ wk m (here refl & ϕ₂))        ~≡⟨ cong (λ ■ → sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ ■))
                                                                         (sym (&-wkₖ-wk ϕ₂ (here refl))) ⟩ 
    sub' (wkₖ m (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & (wkₖ m ϕ₂)))       ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (~-cong-,ₖ (∥-wk m ϕ₁ (ϕ₂ ↓)) refl) ⟩
    sub' ((wkₖ m ϕ₁ ∥ wkₖ m (ϕ₂ ↓)) ,ₖ (here refl & (wkₖ m ϕ₂))) ~⟨ ~-cong-subst-µ₁ (sym (++-assoc ([] ▷ m₂) µ₁₂ µ₁₁))
                                                                        (~-cong-,ₖ (~-cong-∥ ~-refl (dist-wk-↓ ϕ₂)) refl) ⟩
    sub' ((wkₖ m ϕ₁ ∥ (wkₖ m ϕ₂ ↓)) ,ₖ (here refl & (wkₖ m ϕ₂))) ~⟨ ~-sym (∥-▷ (wkₖ m ϕ₁) (wkₖ m ϕ₂)) ⟩
    (wkₖ m ϕ₁ ∥ wkₖ m ϕ₂) ~∎

  ∥-wk* : ∀ ⦃ 𝕂 ⦄ {µ₁₁ µ₁₂ µ₂} µ → (ϕ₁ : µ₁₁ –[ 𝕂 ]→ µ₂) → (ϕ₂ : µ₁₂ –[ 𝕂 ]→ µ₂) →
    wkₖ* µ (ϕ₁ ∥ ϕ₂) ~ (wkₖ* µ ϕ₁ ∥ wkₖ* µ ϕ₂)
  ∥-wk* ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂} {µ₂} []      ϕ₁ ϕ₂ =
    wkₖ* [] (ϕ₁ ∥ ϕ₂)         ~⟨ wkₖ*-[] (ϕ₁ ∥ ϕ₂) ⟩
    (ϕ₁ ∥ ϕ₂)                 ~⟨ ~-sym (~-cong-∥ (wkₖ*-[] ϕ₁) (wkₖ*-[] ϕ₂)) ⟩
    (wkₖ* [] ϕ₁ ∥ wkₖ* [] ϕ₂) ~∎
  ∥-wk* ⦃ 𝕂 ⦄ {µ₁₁} {µ₁₂} {µ₂} (µ ▷ m) ϕ₁ ϕ₂ =
    wkₖ* (µ ▷ m) (ϕ₁ ∥ ϕ₂)                  ~⟨ wkₖ*-▷ µ m (ϕ₁ ∥ ϕ₂) ⟩
    wkₖ m (wkₖ* µ (ϕ₁ ∥ ϕ₂))                ~⟨ ~-cong-wk' (∥-wk* µ ϕ₁ ϕ₂) ⟩
    wkₖ m (wkₖ* µ ϕ₁ ∥ wkₖ* µ ϕ₂)           ~⟨ ∥-wk m (wkₖ* µ ϕ₁) (wkₖ* µ ϕ₂) ⟩
    (wkₖ m (wkₖ* µ ϕ₁) ∥ wkₖ m (wkₖ* µ ϕ₂)) ~⟨ ~-sym (~-cong-∥ (wkₖ*-▷ µ m ϕ₁) (wkₖ*-▷ µ m ϕ₂)) ⟩
    (wkₖ* (µ ▷ m) ϕ₁ ∥ wkₖ* (µ ▷ m) ϕ₂)     ~∎

  -- Identity


  -- idₖ' : µ –→ (µ' ▷▷ µ )
  -- idₖ' _ x = id/` (∈-▷▷ₗ x)  where
  --   ∈-▷▷ₗ : µ ∋ m → (µ' ▷▷ µ) ∋ m
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- idₖ'' : ∀ {µ µ' µ''} → µ –→ (µ' ▷▷ µ ▷▷ µ'')
  -- idₖ'' {µ} {µ'} {µ''} _ x = wk* {µ' = µ''} _ (id/` (∈-▷▷ₗ x))  where
  --   ∈-▷▷ₗ :  ∀ {µ} {µ'} → µ ∋ m → (µ' ▷▷ µ) ∋ m
  --   ∈-▷▷ₗ (here px) = here px
  --   ∈-▷▷ₗ (there x) = there (∈-▷▷ₗ x)

  -- Lifted identity is identity

  id↑~id : ∀ ⦃ 𝕂 : Kit ⦄ m µ → id {µ = µ} ↑ m ~ id {µ = µ ▷ m}
  id↑~id m µ _ x@(here refl)  =
    `/id (x & id {µ = µ} ↑ m) ≡⟨ cong `/id (&-↑-here id) ⟩
    `/id (id/` (here refl))   ≡⟨ cong `/id (sym (&-id x)) ⟩
    `/id (x & id {µ = µ ▷ m}) ∎
  id↑~id m µ _ x@(there y) = -- {!wk-id/` m y!}
    `/id (x & id {µ = µ} ↑ m)    ≡⟨ cong `/id (&-↑-there id y) ⟩
    `/id (wk _ (y & id {µ = µ})) ≡⟨ cong (λ ■ → `/id (wk _ ■)) (&-id y) ⟩
    `/id (wk _ (id/` y))         ≡⟨ cong `/id (wk-id/` _ y) ⟩
    `/id (id/` x)                ≡⟨ cong `/id (sym (&-id x)) ⟩
    `/id (x & id {µ = µ ▷ m})    ∎

  id↑*~id : ∀ ⦃ 𝕂 : Kit ⦄ µ' µ → id {µ = µ} ↑* µ' ~ id {µ = µ ▷▷ µ'}
  id↑*~id []       µ = ↑*-[] id
  id↑*~id (µ' ▷ m) µ =
    id ↑* (µ' ▷ m) ~⟨ ↑*-▷ µ' m id ⟩
    id ↑* µ' ↑ m   ~⟨ ~-cong-↑' (id↑*~id µ' µ) ⟩
    id ↑ m         ~⟨ id↑~id _ _ ⟩
    id             ~∎

  -- Empty Substitution

  &-[]ₖ : ∀ ⦃ 𝕂 : Kit ⦄ {m} (x : _ ∋ m) → x & []ₖ ≡ id/` x
  &-[]ₖ ()

  &-[]ₖ' : ∀ ⦃ 𝕂 : Kit ⦄ (ϕ : [] –[ 𝕂 ]→ []) → ϕ ~ []ₖ
  &-[]ₖ' ϕ m ()

  -- -- Singleton renaming/substitution

  -- -- Singleton renaming/substitution for terms with 1 free variable.
  -- -- Allows the term to be substituted to have arbitrary free variables.
  -- -- This is useful for things like pattern inverting in combination with `_∥_`,
  -- -- where a inverting substitution needs to be built up piece by piece.
  -- ⦅_⦆₀ : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
  -- ⦅ v ⦆₀ = emptyₖ ,ₖ v

  -- -- ⦅_⦆' : (µ ▷▷ µ') ∋/⊢ m→[m/M] m → (µ ▷ m ▷▷ µ') –→ (µ ▷▷ µ')
  -- -- ⦅ v ⦆' = idₖ'' ∥ ⦅ v ⦆₀ ∥ idₖ''
  -- -- ⦅ v ⦆' = {!!} ∥ ⦅ v ⦆₀ ∥ {!!}
  -- -- -- ⦅ v ⦆' = (idₖ ∥ ⦅ v ⦆₀) ↑* _

