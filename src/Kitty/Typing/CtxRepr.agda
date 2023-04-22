open import Kitty.Term.Modes
open import Kitty.Typing.Types

module Kitty.Typing.CtxRepr {𝕄 : Modes} {𝕋 : Terms 𝕄} (KT : KitType 𝕋) where

open import Data.List using (List; []; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties
open import Level using (_⊔_)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open Modes 𝕄
open Terms 𝕋
open KitType KT using (_∶⊢_)

record CtxRepr : Set₁ where
  infix   4  _~ᶜ_  _≡ᶜ_
  infixl  5  _▶_  _▶▶_  _▶'_  _▶▶'_
  infixl  6  _↓ᶜ

  field
    Ctx' : List VarMode → List VarMode → Set

    ∅' : ∀ {µ} → Ctx' µ []

    _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)

    lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → (µ₁ ▷▷ drop-∈ x µ₂) ∶⊢ m→M m

    lookup-▶'-here : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) →
      lookup' (Γ ▶' t) (here refl) ≡ t

    lookup-▶'-there : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) {mx} (x : µ₂ ∋ mx) →
      lookup' (Γ ▶' t) (there x) ≡ lookup' Γ x

  _~ᶜ_ : ∀ {µ₁ µ₂} → (Γ₁ Γ₂ : Ctx' µ₁ µ₂) → Set 
  Γ₁ ~ᶜ Γ₂ = ∀ m (x : _ ∋ m) → lookup' Γ₁ x ≡ lookup' Γ₂ x

  field

    _≡ᶜ_ : ∀ {µ₁ µ₂} → (Γ₁ Γ₂ : Ctx' µ₁ µ₂) → Set 

    ≡ᶜ→~ᶜ : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
      Γ₁ ≡ᶜ Γ₂ →
      (∀ m (x : µ₂ ∋ m) → lookup' Γ₁ x ≡ lookup' Γ₂ x)

    ~ᶜ→≡ᶜ : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
      (∀ m (x : µ₂ ∋ m) → lookup' Γ₁ x ≡ lookup' Γ₂ x) →
      Γ₁ ≡ᶜ Γ₂

    _↓ᶜ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
      
    lookup-↓ᶜ : ∀ {µ₁ µ₂ m₂} (Γ : Ctx' µ₁ (µ₂ ▷ m₂)) {m} (x : µ₂ ∋ m) →
      lookup' (Γ ↓ᶜ) x ≡ lookup' Γ (there x)

    -- TODO: unnecessary
    ↓ᶜ-▶' : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) {m} (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m) →
      ((Γ ▶' t) ↓ᶜ) ≡ᶜ Γ

    invert-Ctx'-[] :
      ∀ {µ₁} (Γ : Ctx' µ₁ []) →
      Γ ≡ᶜ ∅'

    invert-Ctx'-▷ :
      ∀ {µ₁ µ₂ m₂} (Γ : Ctx' µ₁ (µ₂ ▷ m₂)) →
      ∃[ Γ' ] ∃[ t ] Γ ≡ᶜ Γ' ▶' t

  Ctx'-Map : List VarMode → List VarMode → List VarMode → Set
  Ctx'-Map µ₁ µ₁' µ₂ = ∀ m → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m → µ₁' ▷▷ drop-∈ x µ₂ ∶⊢ m→M m

  field
    map-Ctx' :
      ∀ {µ₁ µ₁' µ₂} →
      (f : Ctx'-Map µ₁ µ₁' µ₂) →
      Ctx' µ₁ µ₂ →
      Ctx' µ₁' µ₂

    lookup-map-Ctx' :
      ∀ {µ₁ µ₁' µ₂ m}
      (f : Ctx'-Map µ₁ µ₁' µ₂) →
      (Γ : Ctx' µ₁ µ₂) →
      (x : µ₂ ∋ m) →
      lookup' (map-Ctx' f Γ) x ≡ f _ x (lookup' Γ x)

  map-Ctx'-▶'-~ :
    ∀ {µ₁ µ₁' µ₂ m₂}
    (Γ : Ctx' µ₁ µ₂) →
    (t : (µ₁ ▷▷ µ₂) ∶⊢ m→M m₂) →
    (f : Ctx'-Map µ₁ µ₁' (µ₂ ▷ m₂)) →
    map-Ctx' f (Γ ▶' t) ~ᶜ (map-Ctx' (λ m x → f m (there x)) Γ) ▶' (f _ (here refl) t)
  map-Ctx'-▶'-~ {µ₁} {µ₁'} {µ₂} {m₂} Γ t f m x@(here refl) =
    lookup' (map-Ctx' f (Γ ▶' t)) x ≡⟨ lookup-map-Ctx' f (Γ ▶' t) x ⟩
    f _ x (lookup' (Γ ▶' t) x)      ≡⟨ cong (f _ x) (lookup-▶'-here Γ t) ⟩
    f _ x t                         ≡⟨ sym (lookup-▶'-here (map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ) (f m₂ (here refl) t)) ⟩
    lookup' (map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ ▶' f m₂ (here refl) t) x ∎
  map-Ctx'-▶'-~ {µ₁} {µ₁'} {µ₂} {m₂} Γ t f m x@(there y) =
    lookup' (map-Ctx' f (Γ ▶' t)) x ≡⟨ lookup-map-Ctx' f (Γ ▶' t) x ⟩
    f _ x (lookup' (Γ ▶' t) x)      ≡⟨ cong (f _ x) (lookup-▶'-there Γ t y) ⟩
    f _ x (lookup' Γ y)             ≡⟨ sym (lookup-map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ y)  ⟩
    lookup' (map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ) y ≡⟨ sym (lookup-▶'-there (map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ)
                                                                 (f m₂ (here refl) t) y) ⟩
    lookup' (map-Ctx' (λ m₁ x₁ → f m₁ (there x₁)) Γ ▶' f m₂ (here refl) t) x ∎

  map-Ctx'-▶' :
    ∀ {µ₁ µ₁' µ₂ m₂}
    (Γ : Ctx' µ₁ µ₂) →
    (t : (µ₁ ▷▷ µ₂) ∶⊢ m→M m₂) →
    (f : Ctx'-Map µ₁ µ₁' (µ₂ ▷ m₂)) →
    map-Ctx' f (Γ ▶' t) ≡ᶜ (map-Ctx' (λ m x → f m (there x)) Γ) ▶' (f _ (here refl) t)
  map-Ctx'-▶' {µ₁} {µ₁'} {µ₂} {m₂} Γ t f = ~ᶜ→≡ᶜ (map-Ctx'-▶'-~ Γ t f)

  map-Ctx'-∅'-~ :
    ∀ {µ₁ µ₁'}
    (f : Ctx'-Map µ₁ µ₁' []) →
    map-Ctx' f ∅' ~ᶜ ∅'
  map-Ctx'-∅'-~ f m ()

  map-Ctx'-∅' :
    ∀ {µ₁ µ₁'}
    (f : Ctx'-Map µ₁ µ₁' []) →
    map-Ctx' f ∅' ≡ᶜ ∅'
  map-Ctx'-∅' f = ~ᶜ→≡ᶜ (map-Ctx'-∅'-~ f)

  data Invert-Ctx' {µ₁} : ∀ {µ₂} → Ctx' µ₁ µ₂ → Set where
    Ctx'-∅' :
      {Γ : Ctx' µ₁ []} →
      Γ ≡ᶜ ∅' →
      Invert-Ctx' {µ₂ = []} Γ
    Ctx'-▶' :
      ∀ µ₂ m₂ →
      {Γ : Ctx' µ₁ (µ₂ ▷ m₂)} →
      (Γ' : Ctx' µ₁ µ₂) →
      (t : µ₁ ▷▷ µ₂ ∶⊢ m→M m₂) →
      Γ ≡ᶜ Γ' ▶' t →
      Invert-Ctx' Γ

  invert-Ctx' : ∀ {µ₁ µ₂} (Γ : Ctx' µ₁ µ₂) → Invert-Ctx' Γ
  invert-Ctx' {µ₂ = []}      Γ = Ctx'-∅' (invert-Ctx'-[] Γ)
  invert-Ctx' {µ₂ = µ₂ ▷ m₂} Γ with invert-Ctx'-▷ Γ
  ... | Γ' , t , Γ≡ᶜΓ'▶t = Ctx'-▶' _ _ Γ' t Γ≡ᶜΓ'▶t

  _~₃_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} {D : (a : A) → (b : B a) → C a b → Set ℓ₄}
        (f g : ∀ (a : A) (b : B a) → (c : C a b) → D a b c) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  f ~₃ g = ∀ a b c → f a b c ≡ g a b c

  ~-cong-map-Ctx' :
    ∀ {µ₁ µ₁' µ₂}
      {f₁ f₂ : Ctx'-Map µ₁ µ₁' µ₂}
      {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
    Γ₁ ~ᶜ Γ₂ →
    f₁ ~₃ f₂ →
    map-Ctx' f₁ Γ₁ ~ᶜ map-Ctx' f₂ Γ₂
  ~-cong-map-Ctx' {µ₁} {µ₁'} {µ₂} {f₁} {f₂} {Γ₁} {Γ₂} Γ₁~Γ₂ f₁~f₂ m x =
    lookup' (map-Ctx' f₁ Γ₁) x ≡⟨ lookup-map-Ctx' f₁ Γ₁ x ⟩
    f₁ _ x (lookup' Γ₁ x)      ≡⟨ cong (f₁ _ x) (Γ₁~Γ₂ m x) ⟩
    f₁ _ x (lookup' Γ₂ x)      ≡⟨ f₁~f₂ _ x (lookup' Γ₂ x) ⟩
    f₂ _ x (lookup' Γ₂ x)      ≡⟨ sym (lookup-map-Ctx' f₂ Γ₂ x) ⟩
    lookup' (map-Ctx' f₂ Γ₂) x ∎

  ≡ᶜ-cong-map-Ctx' :
    ∀ {µ₁ µ₁' µ₂}
      {f₁ f₂ : Ctx'-Map µ₁ µ₁' µ₂}
      {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
    Γ₁ ≡ᶜ Γ₂ →
    f₁ ~₃ f₂ →
    map-Ctx' f₁ Γ₁ ≡ᶜ map-Ctx' f₂ Γ₂
  ≡ᶜ-cong-map-Ctx' Γ₁≡Γ₂ f₁~f₂ = ~ᶜ→≡ᶜ (~-cong-map-Ctx' (≡ᶜ→~ᶜ Γ₁≡Γ₂) f₁~f₂)

  ≡ᶜ-▷₁ : ∀ {µ₁ µ₂ m} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} {t₁ t₂ : µ₁ ▷▷ µ₂ ∶⊢ m→M m} →
    (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂) →
    Γ₁ ≡ᶜ Γ₂
  ≡ᶜ-▷₁ {µ₁} {µ₂} {m} {Γ₁} {Γ₂} {t₁} {t₂} eq = ~ᶜ→≡ᶜ (λ m₁ x →
    lookup' Γ₁ x                 ≡⟨ sym (lookup-▶'-there Γ₁ t₁ x) ⟩
    lookup' (Γ₁ ▶' t₁) (there x) ≡⟨ ≡ᶜ→~ᶜ eq _ (there x) ⟩
    lookup' (Γ₂ ▶' t₂) (there x) ≡⟨ lookup-▶'-there Γ₂ t₂ x ⟩
    lookup' Γ₂ x                 ∎)

  ≡ᶜ-▷₂ : ∀ {µ₁ µ₂ m} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} {t₁ t₂ : µ₁ ▷▷ µ₂ ∶⊢ m→M m} →
    (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂) →
    t₁ ≡ t₂
  ≡ᶜ-▷₂ {µ₁} {µ₂} {m} {Γ₁} {Γ₂} {t₁} {t₂} eq =
    t₁                             ≡⟨ sym (lookup-▶'-here Γ₁ t₁) ⟩
    lookup' (Γ₁ ▶' t₁) (here refl) ≡⟨ ≡ᶜ→~ᶜ eq _ (here refl) ⟩
    lookup' (Γ₂ ▶' t₂) (here refl) ≡⟨ lookup-▶'-here Γ₂ t₂ ⟩
    t₂                             ∎

  _▶▶'_ : ∀ {µ₁ µ₂ µ₃} → Ctx' µ₁ µ₂ → Ctx' (µ₁ ▷▷ µ₂) µ₃ → Ctx' µ₁ (µ₂ ▷▷ µ₃)
  _▶▶'_ {µ₁} {µ₂} {[]}     Γ₁ Γ₂ = Γ₁
  _▶▶'_ {µ₁} {µ₂} {µ₃ ▷ m} Γ₁ Γ₂ = (Γ₁ ▶▶' (Γ₂ ↓ᶜ)) ▶' subst (_∶⊢ m→M m) (sym (++-assoc µ₃ µ₂ µ₁)) (lookup' Γ₂ (here refl))

  Ctx : List VarMode → Set
  Ctx µ = Ctx' [] µ

  ∅ : Ctx []
  ∅ = ∅'

  _▶_ : ∀ {µ m} → Ctx µ → µ ∶⊢ m→M m → Ctx (µ ▷ m)
  _▶_ {µ} {m} Γ t = Γ ▶' subst (_∶⊢ m→M m) (sym (++-identityʳ µ)) t

  _▶▶_ : ∀ {µ₁ µ₂} → Ctx µ₁ → Ctx' µ₁ µ₂ → Ctx (µ₁ ▷▷ µ₂)
  _▶▶_ {µ₁} {µ₂} Γ₁ Γ₂ = Γ₁ ▶▶' subst (λ ■ → Ctx' ■ µ₂) (sym (++-identityʳ µ₁)) Γ₂

  lookup'' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → drop-∈ x (µ₁ ▷▷ µ₂) ∶⊢ m→M m
  lookup'' {µ₁} {µ₂} Γ {m} x = subst (_∶⊢ m→M m) (sym (drop-∈-▷▷ x)) (lookup' Γ x)

  lookup : ∀ {µ} → Ctx' [] µ → ∀ {m} → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m
  lookup {µ} Γ {m} x = subst (_∶⊢ m→M m) (++-identityʳ (drop-∈ x µ)) (lookup' Γ x)

  lookup-▶-here : ∀ {µ} (Γ : Ctx µ) {m} (t : µ ∶⊢ m→M m) →
    lookup (Γ ▶ t) (here refl) ≡ t
  lookup-▶-here {µ} Γ {m} t =
    let sub = subst (_∶⊢ m→M m) (++-identityʳ µ) in
    let sub⁻¹ = subst (_∶⊢ m→M m) (sym (++-identityʳ µ)) in
    lookup (Γ ▶ t) (here refl)               ≡⟨⟩
    sub (lookup' (Γ ▶' sub⁻¹ t) (here refl)) ≡⟨ cong sub (lookup-▶'-here Γ (sub⁻¹ t)) ⟩
    sub (sub⁻¹ t)                            ≡⟨ cancel-subst' _ (++-identityʳ µ) t ⟩
    t                                        ∎

  lookup-▶-there : ∀ {µ} (Γ : Ctx µ) {m} (t : µ ∶⊢ m→M m) {mx} (x : µ ∋ mx) →
    lookup (Γ ▶ t) (there x) ≡ lookup Γ x
  lookup-▶-there {µ} Γ {m} t {mx} x =
    let sub = subst (_∶⊢ m→M mx) (++-identityʳ (drop-∈ x µ)) in
    let sub⁻¹ = subst (_∶⊢ m→M m) (sym (++-identityʳ µ)) in
    lookup (Γ ▶ t) (there x)               ≡⟨⟩
    sub (lookup' (Γ ▶' sub⁻¹ t) (there x)) ≡⟨ cong sub (lookup-▶'-there Γ (sub⁻¹ t) x) ⟩
    sub (lookup' Γ x)                      ≡⟨⟩
    lookup Γ x                             ∎
    
  ~ᶜ-refl : ∀ {µ₁ µ₂} {Γ : Ctx' µ₁ µ₂} → Γ ~ᶜ Γ 
  ~ᶜ-refl = λ m x → refl

  ~ᶜ-sym : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} → Γ₁ ~ᶜ Γ₂ → Γ₂ ~ᶜ Γ₁
  ~ᶜ-sym Γ₁~Γ₂ = λ m x → sym (Γ₁~Γ₂ m x)

  ~ᶜ-trans : ∀ {µ₁ µ₂} {Γ₁ Γ₂ Γ₃ : Ctx' µ₁ µ₂} → Γ₁ ~ᶜ Γ₂ → Γ₂ ~ᶜ Γ₃ → Γ₁ ~ᶜ Γ₃
  ~ᶜ-trans Γ₁~Γ₂ Γ₂~Γ₃ = λ m x → trans (Γ₁~Γ₂ m x) (Γ₂~Γ₃ m x)

  ≡ᶜ-refl : ∀ {µ₁ µ₂} {Γ : Ctx' µ₁ µ₂} → Γ ≡ᶜ Γ 
  ≡ᶜ-refl = ~ᶜ→≡ᶜ ~ᶜ-refl

  ≡ᶜ-sym : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} → Γ₁ ≡ᶜ Γ₂ → Γ₂ ≡ᶜ Γ₁
  ≡ᶜ-sym Γ₁≡Γ₂ = ~ᶜ→≡ᶜ (~ᶜ-sym (≡ᶜ→~ᶜ Γ₁≡Γ₂))

  ≡ᶜ-trans : ∀ {µ₁ µ₂} {Γ₁ Γ₂ Γ₃ : Ctx' µ₁ µ₂} → Γ₁ ≡ᶜ Γ₂ → Γ₂ ≡ᶜ Γ₃ → Γ₁ ≡ᶜ Γ₃
  ≡ᶜ-trans Γ₁≡Γ₂ Γ₂≡Γ₃ = ~ᶜ→≡ᶜ (~ᶜ-trans (≡ᶜ→~ᶜ Γ₁≡Γ₂) (≡ᶜ→~ᶜ Γ₂≡Γ₃))

  ~-cong-↓ᶜ :
    ∀ {µ µ' m'} {Γ₁' Γ₂' : Ctx' µ (µ' ▷ m')}
    → Γ₁' ~ᶜ Γ₂'
    → Γ₁' ↓ᶜ ~ᶜ Γ₂' ↓ᶜ
  ~-cong-↓ᶜ {µ} {µ'} {m'} {Γ₁'} {Γ₂'} Γ₁'~Γ₂' m x =
    lookup' (Γ₁' ↓ᶜ) x    ≡⟨ lookup-↓ᶜ Γ₁' x ⟩
    lookup' Γ₁' (there x) ≡⟨ Γ₁'~Γ₂' _ (there x) ⟩
    lookup' Γ₂' (there x) ≡⟨ sym (lookup-↓ᶜ Γ₂' x) ⟩
    lookup' (Γ₂' ↓ᶜ) x    ∎

  ≡ᶜ-cong-↓ᶜ :
    ∀ {µ µ' m'} {Γ₁' Γ₂' : Ctx' µ (µ' ▷ m')}
    → Γ₁' ≡ᶜ Γ₂'
    → Γ₁' ↓ᶜ ≡ᶜ Γ₂' ↓ᶜ
  ≡ᶜ-cong-↓ᶜ Γ₁'≡Γ₂' = ~ᶜ→≡ᶜ (~-cong-↓ᶜ (≡ᶜ→~ᶜ Γ₁'≡Γ₂'))

  ~-cong-▶' :
    ∀ {µ₁ µ₂ m} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} {t₁ t₂ : µ₁ ▷▷ µ₂ ∶⊢ m→M m}
    → Γ₁ ~ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶' t₁) ~ᶜ (Γ₂ ▶' t₂)
  ~-cong-▶' {µ₁} {µ₂} {m} {Γ₁} {Γ₂} {t₁} {.t₁} Γ₁~Γ₂ refl mx (here refl) =
    lookup' (Γ₁ ▶' t₁) (here refl) ≡⟨ lookup-▶'-here Γ₁ t₁ ⟩
    t₁                             ≡⟨ sym (lookup-▶'-here Γ₂ t₁) ⟩
    lookup' (Γ₂ ▶' t₁) (here refl) ∎
  ~-cong-▶' {µ₁} {µ₂} {m} {Γ₁} {Γ₂} {t₁} {.t₁} Γ₁~Γ₂ refl mx (there x) =
    lookup' (Γ₁ ▶' t₁) (there x) ≡⟨ lookup-▶'-there Γ₁ t₁ x ⟩
    lookup' Γ₁ x                 ≡⟨ Γ₁~Γ₂ _ x ⟩
    lookup' Γ₂ x                 ≡⟨ sym (lookup-▶'-there Γ₂ t₁ x) ⟩
    lookup' (Γ₂ ▶' t₁) (there x) ∎

  open import Data.List.Properties using (++-assoc; ++-identityʳ)
  ~-cong-▶ :
    ∀ {µ₁ m} {Γ₁ Γ₂ : Ctx µ₁} {t₁ t₂ : µ₁ ∶⊢ m→M m}
    → Γ₁ ~ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶ t₁) ~ᶜ (Γ₂ ▶ t₂)
  ~-cong-▶ {µ₁} {m} {Γ₁} {Γ₂} {t₁} {t₂} Γ₁~Γ₂ refl mx x =
    let sub = subst (_∶⊢ m→M m) (sym (++-identityʳ µ₁)) in
    lookup' (Γ₁ ▶ t₁) x      ≡⟨⟩
    lookup' (Γ₁ ▶' sub t₁) x ≡⟨ ~-cong-▶' Γ₁~Γ₂ refl _ x ⟩
    lookup' (Γ₂ ▶' sub t₁) x ≡⟨⟩
    lookup' (Γ₂ ▶ t₁) x ∎

  ≡ᶜ-cong-▶' :
    ∀ {µ₁ µ₂ m} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} {t₁ t₂ : µ₁ ▷▷ µ₂ ∶⊢ m→M m}
    → Γ₁ ≡ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂)
  ≡ᶜ-cong-▶' Γ₁≡Γ₂ t₁≡t₂ = ~ᶜ→≡ᶜ (~-cong-▶' (≡ᶜ→~ᶜ Γ₁≡Γ₂) t₁≡t₂)

  ≡ᶜ-cong-▶ :
    ∀ {µ₁ m} {Γ₁ Γ₂ : Ctx µ₁} {t₁ t₂ : µ₁ ∶⊢ m→M m}
    → Γ₁ ≡ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶ t₁) ≡ᶜ (Γ₂ ▶ t₂)
  ≡ᶜ-cong-▶ Γ₁≡Γ₂ t₁≡t₂ = ~ᶜ→≡ᶜ (~-cong-▶ (≡ᶜ→~ᶜ Γ₁≡Γ₂) t₁≡t₂)

  ~-cong-▶▶' :
    ∀ {µ₁ µ₂ µ₃} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} {Γ₁' Γ₂' : Ctx' (µ₁ ▷▷ µ₂) µ₃}
    → Γ₁  ~ᶜ Γ₂
    → Γ₁' ~ᶜ Γ₂'
    → (Γ₁ ▶▶' Γ₁') ~ᶜ (Γ₂ ▶▶' Γ₂')
  ~-cong-▶▶' {µ₁} {µ₂} {[]}      {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' m x =
    lookup' (Γ₁ ▶▶' Γ₁') x ≡⟨ refl ⟩
    lookup' Γ₁           x ≡⟨  Γ₁~Γ₂ m x ⟩
    lookup' Γ₂           x ≡⟨ refl ⟩
    lookup' (Γ₂ ▶▶' Γ₂') x ∎
  ~-cong-▶▶' {µ₁} {µ₂} {µ₃ ▷ m₃} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' .m₃ x@(here refl) =
    let sub = subst (_∶⊢ m→M m₃) (sym (++-assoc µ₃ µ₂ µ₁)) in
    lookup' (Γ₁ ▶▶' Γ₁') x                                     ≡⟨⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ ▶' sub (lookup' Γ₁' (here refl))) x ≡⟨ lookup-▶'-here (Γ₁ ▶▶' Γ₁' ↓ᶜ) _ ⟩
    sub (lookup' Γ₁' (here refl))                              ≡⟨ cong sub (Γ₁'~Γ₂' _ (here refl)) ⟩
    sub (lookup' Γ₂' (here refl))                              ≡⟨ sym (lookup-▶'-here (Γ₂ ▶▶' Γ₂' ↓ᶜ) _) ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ ▶' sub (lookup' Γ₂' (here refl))) x ≡⟨⟩
    lookup' (Γ₂ ▶▶' Γ₂') x                                     ∎
  ~-cong-▶▶' {µ₁} {µ₂} {µ₃ ▷ m₃} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' m x@(there y) =
    let sub = subst (_∶⊢ m→M m₃) (sym (++-assoc µ₃ µ₂ µ₁)) in
    lookup' (Γ₁ ▶▶' Γ₁') x                                     ≡⟨⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ ▶' sub (lookup' Γ₁' (here refl))) x ≡⟨ lookup-▶'-there (Γ₁ ▶▶' Γ₁' ↓ᶜ) _ y ⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ) y                                  ≡⟨ ~-cong-▶▶' Γ₁~Γ₂ (~-cong-↓ᶜ Γ₁'~Γ₂') _ y ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ) y                                  ≡⟨ sym (lookup-▶'-there (Γ₂ ▶▶' Γ₂' ↓ᶜ) _ y) ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ ▶' sub (lookup' Γ₂' (here refl))) x ≡⟨⟩
    lookup' (Γ₂ ▶▶' Γ₂') x                                     ∎

  ~-cong-subst :
    ∀ {µ₁ µ₂ µ₁'} {Γ₁ Γ₂ : Ctx' µ₁ µ₂}
    → Γ₁ ~ᶜ Γ₂
    → (eq : µ₁ ≡ µ₁')
    → let sub = subst (λ ■ → Ctx' ■ µ₂) eq in
      sub Γ₁ ~ᶜ sub Γ₂
  ~-cong-subst Γ₁~Γ₂ refl = Γ₁~Γ₂

  ~-cong-▶▶ :
    ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx µ₁} {Γ₁' Γ₂' : Ctx' µ₁ µ₂}
    → Γ₁  ~ᶜ Γ₂
    → Γ₁' ~ᶜ Γ₂'
    → (Γ₁ ▶▶ Γ₁') ~ᶜ (Γ₂ ▶▶ Γ₂')
  ~-cong-▶▶ {µ₁} {µ₂} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' m x =
    let sub = subst (λ ■ → Ctx' ■ µ₂) (sym (++-identityʳ µ₁)) in
    lookup' (Γ₁ ▶▶ Γ₁') x      ≡⟨⟩
    lookup' (Γ₁ ▶▶' sub Γ₁') x ≡⟨ ~-cong-▶▶' Γ₁~Γ₂ (~-cong-subst Γ₁'~Γ₂' _) _ x ⟩
    lookup' (Γ₂ ▶▶' sub Γ₂') x ≡⟨⟩
    lookup' (Γ₂ ▶▶ Γ₂') x      ∎

  ≡ᶜ-cong-▶▶ :
    ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx µ₁} {Γ₁' Γ₂' : Ctx' µ₁ µ₂}
    → Γ₁  ≡ᶜ Γ₂
    → Γ₁' ≡ᶜ Γ₂'
    → (Γ₁ ▶▶ Γ₁') ≡ᶜ (Γ₂ ▶▶ Γ₂')
  ≡ᶜ-cong-▶▶ Γ₁≡Γ₂ Γ₁'≡Γ₂' = ~ᶜ→≡ᶜ (~-cong-▶▶ (≡ᶜ→~ᶜ Γ₁≡Γ₂) (≡ᶜ→~ᶜ Γ₁'≡Γ₂'))

  ▶▶-↓ : ∀ {µ₁ µ₂ m₂} (Γ : Ctx µ₁) (Γ' : Ctx' µ₁ (µ₂ ▷ m₂)) →
    Γ ▶▶ Γ' ≡ Γ ▶▶ (Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)
  ▶▶-↓ {µ₁} {µ₂} {m₂} Γ Γ' =
    let sub = subst (λ ■ → Ctx' ■ (µ₂ ▷ m₂)) (sym (++-identityʳ µ₁)) in
    let subx = subst (_∶⊢ m→M m₂) (cong (_▷▷ µ₂) (sym (++-identityʳ µ₁))) in
    let sub' = subst (_∶⊢ m→M m₂) (sym (++-assoc µ₂ µ₁ [])) in
    let subx' = subst (_∶⊢ m→M m₂) (trans (cong (_▷▷ µ₂) (sym (++-identityʳ µ₁))) (sym (++-assoc µ₂ µ₁ []))) in
    let sub'' = subst (λ ■ → Ctx' ■ µ₂) (sym (++-identityʳ µ₁)) in
    let sub''' = subst (_∶⊢ m→M m₂) (sym (++-identityʳ (µ₁ ▷▷ µ₂))) in
    Γ ▶▶ Γ'                                                    ≡⟨⟩
    Γ ▶▶' sub Γ'                                               ≡⟨⟩
    Γ ▶▶' sub Γ' ↓ᶜ     ▶' sub' (lookup' (sub Γ') (here refl)) ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' sub' ■₂)
                                                                           (dist-subst _↓ᶜ _ Γ')
                                                                           (dist-subst' (_▷▷ µ₂)
                                                                                        (λ Γ → lookup' Γ (here refl)) _
                                                                                        (cong (_▷▷ µ₂)
                                                                                          (sym (++-identityʳ µ₁))) Γ')
                                                                   ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' sub' (subx (lookup' Γ' (here refl))) ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' ■₂) refl
                                                                        (subst-merge (_∶⊢ m→M m₂) _ (sym (++-assoc µ₂ µ₁ [])) (lookup' Γ' (here refl))) ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' subx' (lookup' Γ' (here refl))      ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' ■₂) refl
                                                                      (subst-irrelevant _ (sym (++-identityʳ (µ₁ ▷▷ µ₂))) (lookup' Γ' (here refl))) ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' sub''' (lookup' Γ' (here refl))     ≡⟨⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)               ≡⟨⟩
    Γ ▶▶ Γ' ↓ᶜ ▶ lookup' Γ' (here refl)                        ∎

  dist-↓ᶜ-map : ∀ {µ₁' µ₁ µ₂ m₂} (f : Ctx'-Map µ₁ µ₁' (µ₂ ▷ m₂)) (Γ' : Ctx' µ₁ (µ₂ ▷ m₂)) →
    map-Ctx' (λ _ x → f _ (there x)) (Γ' ↓ᶜ) ~ᶜ (map-Ctx' f Γ') ↓ᶜ
  dist-↓ᶜ-map {µ₁'} {µ₁} {µ₂} {m₂} f Γ' m x =
    lookup' (map-Ctx' (λ _ x → f _ (there x)) (Γ' ↓ᶜ)) x ≡⟨ lookup-map-Ctx' _ (Γ' ↓ᶜ) x ⟩
    f _ (there x) (lookup' (Γ' ↓ᶜ) x)                    ≡⟨ cong (f _ (there x)) (lookup-↓ᶜ Γ' x) ⟩
    f _ (there x) (lookup' Γ' (there x))                 ≡⟨ sym (lookup-map-Ctx' f Γ' (there x)) ⟩
    lookup' (map-Ctx' f Γ') (there x)                    ≡⟨ sym (lookup-↓ᶜ _ x) ⟩
    lookup' (map-Ctx' f Γ' ↓ᶜ) x                         ∎


  -- lookup-wk : ∀ {µ} → Ctx' [] µ → ∀ {m} → (x : µ ∋ m) → µ ∶⊢ m→M m

  open import Kitty.Term.Kit 𝕋
  open import Kitty.Term.Traversal 𝕋
  open import Kitty.Term.Sub 𝕋
  open import Kitty.Term.KitHomotopy 𝕋

  module CtxReprSubst {ℓ} (𝕊 : SubWithLaws ℓ) (T : Traversal 𝕊) (H : KitHomotopy 𝕊 T) where
    private instance _ = 𝕊

    open KitType KT
    open Traversal 𝕊 T
    open Kit ⦃ … ⦄
    open SubWithLaws 𝕊
    open Sub SubWithLaws-Sub
    open KitHomotopy 𝕊 T H
    open import Kitty.Term.KitT 𝕋 𝕊 T

    wk*-Ctx' : ∀ {µ₁ µ₂} µ₁' → Ctx' µ₁ µ₂ → Ctx' (µ₁ ▷▷ µ₁') µ₂
    wk*-Ctx' {µ₁} {µ₂} µ₁' Γ =
      map-Ctx' (λ mx x t → t ⋯ᵣ ((wkₖ* µ₁' (id {µ = µ₁})) ↑* drop-∈ x µ₂)) Γ
      where instance _ = kitᵣ

    wk*-Ctx : ∀ {µ₂} µ₁ → Ctx µ₂ → Ctx' µ₁ µ₂
    wk*-Ctx {µ₂} µ₁ Γ =
      let sub = subst (λ ■ → Ctx' ■ µ₂) (++-identityʳ µ₁) in
      sub (wk*-Ctx' µ₁ Γ)

    infixl  5  _⋯Ctx'_
    _⋯Ctx'_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ µ'} → Ctx' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx' µ₂ µ'
    _⋯Ctx'_ ⦃ 𝕂 ⦄ {µ' = µ'} Γ ϕ = map-Ctx' (λ _ x t → t ⋯ (ϕ ↑* drop-∈ x µ')) Γ

    ~-cong-⋯Ctx' :
      ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ 
        ⦃ K₁ : KitT 𝕂₁ ⦄ 
        ⦃ K₂ : KitT 𝕂₂ ⦄ 
        {µ₁ µ₁' µ₂}
        {ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₁'}
        {ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₁'}
        {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
      Γ₁ ~ᶜ Γ₂ →
      ϕ₁ ~ ϕ₂ →
      (Γ₁ ⋯Ctx' ϕ₁) ~ᶜ (Γ₂ ⋯Ctx' ϕ₂)
    ~-cong-⋯Ctx' ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ₁} {µ₁'} {µ₂} {ϕ₁} {ϕ₂} {Γ₁} {Γ₂} Γ₁~Γ₂ ϕ₁~ϕ₂ =
      ~-cong-map-Ctx' Γ₁~Γ₂ (λ m x t → ~-cong-⋯ t (~-cong-↑* ϕ₁~ϕ₂))

    ≡ᶜ-cong-⋯Ctx' :
      ∀ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ 
        ⦃ K₁ : KitT 𝕂₁ ⦄ 
        ⦃ K₂ : KitT 𝕂₂ ⦄ 
        {µ₁ µ₁' µ₂}
        {ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₁'}
        {ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₁'}
        {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
      Γ₁ ≡ᶜ Γ₂ →
      ϕ₁ ~ ϕ₂ →
      (Γ₁ ⋯Ctx' ϕ₁) ≡ᶜ (Γ₂ ⋯Ctx' ϕ₂)
    ≡ᶜ-cong-⋯Ctx' Γ₁≡Γ₂ ϕ₁~ϕ₂ = ~ᶜ→≡ᶜ (~-cong-⋯Ctx' (≡ᶜ→~ᶜ Γ₁≡Γ₂) ϕ₁~ϕ₂)


module FunctionalCtx where
  Ctx' : List VarMode → List VarMode → Set
  Ctx' µ₁ µ₂ = ∀ m → (x : µ₂ ∋ m) → (µ₁ ▷▷ drop-∈ x µ₂) ∶⊢ m→M m

  ∅' : ∀ {µ} → Ctx' µ []
  ∅' _ ()

  _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)
  (Γ ▶' t) _ (here refl) = t
  (Γ ▶' t) _ (there x)   = Γ _ x

  lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → (µ₁ ▷▷ drop-∈ x µ₂) ∶⊢ m→M m
  lookup' Γ x = Γ _ x

  _≡ᶜ_ : ∀ {µ₁ µ₂} → (Γ₁ Γ₂ : Ctx' µ₁ µ₂) → Set 
  Γ₁ ≡ᶜ Γ₂ = ∀ m (x : _ ∋ m) → Γ₁ _ x ≡ Γ₂ _ x 

  _↓ᶜ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
  Γ ↓ᶜ = λ m x → Γ m (there x)

  map-Ctx' :
    ∀ {µ₁ µ₁' µ₂} →
    (f : ∀ m → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m → µ₁' ▷▷ drop-∈ x µ₂ ∶⊢ m→M m) →
    Ctx' µ₁ µ₂ →
    Ctx' µ₁' µ₂
  map-Ctx' f Γ m x = f _ x (Γ m x)

  Functional-CtxRepr : CtxRepr
  Functional-CtxRepr = record
    { Ctx'            = Ctx'
    ; ∅'              = λ {µ} → ∅' {µ}
    ; _▶'_            = _▶'_
    ; lookup'         = lookup'
    ; lookup-▶'-here  = λ Γ t → refl
    ; lookup-▶'-there = λ Γ t x → refl
    ; invert-Ctx'-[]  = λ Γ m ()
    ; invert-Ctx'-▷   = λ Γ → (Γ ↓ᶜ) , Γ _ (here refl) , λ { m (here refl) → refl ; m (there x) → refl }
    ; lookup-map-Ctx' = λ f Γ x → refl
    ; _≡ᶜ_            = _≡ᶜ_
    ; ≡ᶜ→~ᶜ           = λ Γ₁≡Γ₂ → Γ₁≡Γ₂
    ; ~ᶜ→≡ᶜ           = λ Γ₁≡Γ₂ → Γ₁≡Γ₂
    ; _↓ᶜ             = _↓ᶜ
    ; lookup-↓ᶜ       = λ Γ x → refl
    ; ↓ᶜ-▶'           = λ Γ t m x → refl
    ; map-Ctx'        = map-Ctx'
    }

open FunctionalCtx public using (Functional-CtxRepr)

module ListCtx where
  data Ctx' : List VarMode → List VarMode → Set where
    []   : ∀ {µ₁} → Ctx' µ₁ []
    _▶'_ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ µ₂ → (µ₁ ▷▷ µ₂) ∶⊢ m→M m → Ctx' µ₁ (µ₂ ▷ m)

  lookup' : ∀ {µ₁ µ₂} → Ctx' µ₁ µ₂ → ∀ {m} → (x : µ₂ ∋ m) → (µ₁ ▷▷ drop-∈ x µ₂) ∶⊢ m→M m
  lookup' (Γ ▶' t) (here refl) = t
  lookup' (Γ ▶' t) (there x)   = lookup' Γ x

  _↓ᶜ : ∀ {µ₁ µ₂ m} → Ctx' µ₁ (µ₂ ▷ m) → Ctx' µ₁ µ₂
  (Γ ▶' t) ↓ᶜ = Γ

  map-Ctx' :
    ∀ {µ₁ µ₁' µ₂} →
    (f : ∀ m → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m → µ₁' ▷▷ drop-∈ x µ₂ ∶⊢ m→M m) →
    Ctx' µ₁ µ₂ →
    Ctx' µ₁' µ₂
  map-Ctx' f []       = []
  map-Ctx' f (Γ ▶' t) = map-Ctx' (λ _ x t' → f _ (there x) t') Γ ▶' f _ (here refl) t

  ~ᶜ→≡ᶜ : ∀ {µ₁ µ₂} {Γ₁ Γ₂ : Ctx' µ₁ µ₂} →
    (∀ m (x : µ₂ ∋ m) → lookup' Γ₁ x ≡ lookup' Γ₂ x) →
    Γ₁ ≡ Γ₂
  ~ᶜ→≡ᶜ {Γ₁ = []} {Γ₂ = []} Γ₁~Γ₂ = refl
  ~ᶜ→≡ᶜ {Γ₁ = Γ₁ ▶' T₁} {Γ₂ = Γ₂ ▶' T₂} Γ₁~Γ₂
    rewrite ~ᶜ→≡ᶜ {Γ₁ = Γ₁} {Γ₂ = Γ₂} (λ m x → Γ₁~Γ₂ m (there x))
    = cong (Γ₂ ▶'_) (Γ₁~Γ₂ _ (here refl))

  Ctx'-Map : List VarMode → List VarMode → List VarMode → Set
  Ctx'-Map µ₁ µ₁' µ₂ = ∀ m → (x : µ₂ ∋ m) → µ₁ ▷▷ drop-∈ x µ₂ ∶⊢ m→M m → µ₁' ▷▷ drop-∈ x µ₂ ∶⊢ m→M m

  lookup-map-Ctx' :
    ∀ {µ₁ µ₁' µ₂ m}
    (f : Ctx'-Map µ₁ µ₁' µ₂) →
    (Γ : Ctx' µ₁ µ₂) →
    (x : µ₂ ∋ m) →
    lookup' (map-Ctx' f Γ) x ≡ f _ x (lookup' Γ x)
  lookup-map-Ctx' f (Γ ▶' t) (here refl) = refl
  lookup-map-Ctx' f (Γ ▶' t) (there x) = lookup-map-Ctx' (λ _ x → f _ (there x)) Γ x

  List-CtxRepr : CtxRepr
  List-CtxRepr = record
    { Ctx'            = Ctx'
    ; ∅'              = []
    ; _▶'_            = _▶'_
    ; lookup'         = lookup'
    ; lookup-▶'-here  = λ Γ t → refl
    ; lookup-▶'-there = λ Γ t x → refl
    ; invert-Ctx'-[]  = λ { [] → refl }
    ; invert-Ctx'-▷   = λ { (Γ ▶' t) → Γ , t , refl }
    ; lookup-map-Ctx' = lookup-map-Ctx'
    ; _≡ᶜ_            = _≡_
    ; ≡ᶜ→~ᶜ           = λ { refl m x → refl }
    ; ~ᶜ→≡ᶜ           = ~ᶜ→≡ᶜ
    ; _↓ᶜ             = _↓ᶜ
    ; lookup-↓ᶜ       = λ { (Γ ▶' t) x → refl }
    ; ↓ᶜ-▶'           = λ Γ t → refl
    ; map-Ctx'        = map-Ctx'
    }

open ListCtx public using (List-CtxRepr)
