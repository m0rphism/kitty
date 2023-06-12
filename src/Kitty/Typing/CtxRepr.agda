open import Kitty.Term.Terms
open import Kitty.Typing.TypeSorts

module Kitty.Typing.CtxRepr {𝕋 : Terms} (TM : TypeSorts 𝕋) where

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

open Terms 𝕋
open TypeSorts TM using (_∶⊢_)

record CtxRepr : Set₁ where
  infix   4  _~ᶜ_  _≡ᶜ_
  infixl  5  _▶_  _▶▶_  _▶'_  _▶▶'_
  infixl  6  _↓ᶜ

  field
    Ctx' : SortCtx → SortCtx → Set

    ∅' : ∀ {S} → Ctx' S []

    _▶'_ : ∀ {S₁ S₂ s} → Ctx' S₁ S₂ → (S₁ ▷▷ S₂) ∶⊢ s → Ctx' S₁ (S₂ ▷ s)

    lookup' : ∀ {S₁ S₂} → Ctx' S₁ S₂ → ∀ {s} → (x : S₂ ∋ s) → (S₁ ▷▷ drop-∈ x S₂) ∶⊢ s

    lookup-▶'-here : ∀ {S₁ S₂} (Γ : Ctx' S₁ S₂) {s} (t : S₁ ▷▷ S₂ ∶⊢ s) →
      lookup' (Γ ▶' t) (here refl) ≡ t

    lookup-▶'-there : ∀ {S₁ S₂} (Γ : Ctx' S₁ S₂) {s} (t : S₁ ▷▷ S₂ ∶⊢ s) {sx} (x : S₂ ∋ sx) →
      lookup' (Γ ▶' t) (there x) ≡ lookup' Γ x

  _~ᶜ_ : ∀ {S₁ S₂} → (Γ₁ Γ₂ : Ctx' S₁ S₂) → Set 
  Γ₁ ~ᶜ Γ₂ = ∀ s (x : _ ∋ s) → lookup' Γ₁ x ≡ lookup' Γ₂ x

  field

    _≡ᶜ_ : ∀ {S₁ S₂} → (Γ₁ Γ₂ : Ctx' S₁ S₂) → Set 

    ≡ᶜ→~ᶜ : ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx' S₁ S₂} →
      Γ₁ ≡ᶜ Γ₂ →
      (∀ s (x : S₂ ∋ s) → lookup' Γ₁ x ≡ lookup' Γ₂ x)

    ~ᶜ→≡ᶜ : ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx' S₁ S₂} →
      (∀ s (x : S₂ ∋ s) → lookup' Γ₁ x ≡ lookup' Γ₂ x) →
      Γ₁ ≡ᶜ Γ₂

    _↓ᶜ : ∀ {S₁ S₂ s} → Ctx' S₁ (S₂ ▷ s) → Ctx' S₁ S₂
      
    lookup'-↓ᶜ : ∀ {S₁ S₂ s₂} (Γ : Ctx' S₁ (S₂ ▷ s₂)) {s} (x : S₂ ∋ s) →
      lookup' (Γ ↓ᶜ) x ≡ lookup' Γ (there x)

    -- TODO: unnecessary
    ↓ᶜ-▶' : ∀ {S₁ S₂} (Γ : Ctx' S₁ S₂) {s} (t : S₁ ▷▷ S₂ ∶⊢ s) →
      ((Γ ▶' t) ↓ᶜ) ≡ᶜ Γ

    invert-Ctx'-[] :
      ∀ {S₁} (Γ : Ctx' S₁ []) →
      Γ ≡ᶜ ∅'

    invert-Ctx'-▷ :
      ∀ {S₁ S₂ s₂} (Γ : Ctx' S₁ (S₂ ▷ s₂)) →
      ∃[ Γ' ] ∃[ t ] Γ ≡ᶜ Γ' ▶' t

  Ctx'-Map : SortCtx → SortCtx → SortCtx → Set
  Ctx'-Map S₁ S₁' S₂ = ∀ s → (x : S₂ ∋ s) → S₁ ▷▷ drop-∈ x S₂ ∶⊢ s → S₁' ▷▷ drop-∈ x S₂ ∶⊢ s

  field
    map-Ctx' :
      ∀ {S₁ S₁' S₂} →
      (f : Ctx'-Map S₁ S₁' S₂) →
      Ctx' S₁ S₂ →
      Ctx' S₁' S₂

    lookup-map-Ctx' :
      ∀ {S₁ S₁' S₂ s}
      (f : Ctx'-Map S₁ S₁' S₂) →
      (Γ : Ctx' S₁ S₂) →
      (x : S₂ ∋ s) →
      lookup' (map-Ctx' f Γ) x ≡ f _ x (lookup' Γ x)

  map-Ctx'-▶'-~ :
    ∀ {S₁ S₁' S₂ s₂}
    (Γ : Ctx' S₁ S₂) →
    (t : (S₁ ▷▷ S₂) ∶⊢ s₂) →
    (f : Ctx'-Map S₁ S₁' (S₂ ▷ s₂)) →
    map-Ctx' f (Γ ▶' t) ~ᶜ (map-Ctx' (λ s x → f s (there x)) Γ) ▶' (f _ (here refl) t)
  map-Ctx'-▶'-~ {S₁} {S₁'} {S₂} {s₂} Γ t f s x@(here refl) =
    lookup' (map-Ctx' f (Γ ▶' t)) x ≡⟨ lookup-map-Ctx' f (Γ ▶' t) x ⟩
    f _ x (lookup' (Γ ▶' t) x)      ≡⟨ cong (f _ x) (lookup-▶'-here Γ t) ⟩
    f _ x t                         ≡⟨ sym (lookup-▶'-here (map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ) (f s₂ (here refl) t)) ⟩
    lookup' (map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ ▶' f s₂ (here refl) t) x ∎
  map-Ctx'-▶'-~ {S₁} {S₁'} {S₂} {s₂} Γ t f s x@(there y) =
    lookup' (map-Ctx' f (Γ ▶' t)) x ≡⟨ lookup-map-Ctx' f (Γ ▶' t) x ⟩
    f _ x (lookup' (Γ ▶' t) x)      ≡⟨ cong (f _ x) (lookup-▶'-there Γ t y) ⟩
    f _ x (lookup' Γ y)             ≡⟨ sym (lookup-map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ y)  ⟩
    lookup' (map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ) y ≡⟨ sym (lookup-▶'-there (map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ)
                                                                 (f s₂ (here refl) t) y) ⟩
    lookup' (map-Ctx' (λ s₁ x₁ → f s₁ (there x₁)) Γ ▶' f s₂ (here refl) t) x ∎

  map-Ctx'-▶' :
    ∀ {S₁ S₁' S₂ s₂}
    (Γ : Ctx' S₁ S₂) →
    (t : (S₁ ▷▷ S₂) ∶⊢ s₂) →
    (f : Ctx'-Map S₁ S₁' (S₂ ▷ s₂)) →
    map-Ctx' f (Γ ▶' t) ≡ᶜ (map-Ctx' (λ s x → f s (there x)) Γ) ▶' (f _ (here refl) t)
  map-Ctx'-▶' {S₁} {S₁'} {S₂} {s₂} Γ t f = ~ᶜ→≡ᶜ (map-Ctx'-▶'-~ Γ t f)

  map-Ctx'-∅'-~ :
    ∀ {S₁ S₁'}
    (f : Ctx'-Map S₁ S₁' []) →
    map-Ctx' f ∅' ~ᶜ ∅'
  map-Ctx'-∅'-~ f s ()

  map-Ctx'-∅' :
    ∀ {S₁ S₁'}
    (f : Ctx'-Map S₁ S₁' []) →
    map-Ctx' f ∅' ≡ᶜ ∅'
  map-Ctx'-∅' f = ~ᶜ→≡ᶜ (map-Ctx'-∅'-~ f)

  _↓ᶠ : 
    ∀ {S₁ S₁' S₂ s₂} →
    Ctx'-Map S₁ S₁' (S₂ ▷ s₂) →
    Ctx'-Map S₁ S₁' S₂
  (f ↓ᶠ) s x t = f s (there x) t

  map-Ctx'-↓-~ :
    ∀ {S₁ S₁' S₂ s₂}
    (Γ : Ctx' S₁ (S₂ ▷ s₂))
    (f : Ctx'-Map S₁ S₁' (S₂ ▷ s₂)) →
    map-Ctx' (f ↓ᶠ) (Γ ↓ᶜ) ~ᶜ (map-Ctx' f Γ) ↓ᶜ
  map-Ctx'-↓-~ {S₁} {S₁'} {S₂} {s₂} Γ f s x =
    lookup' (map-Ctx' (f ↓ᶠ) (Γ ↓ᶜ)) x  ≡⟨ lookup-map-Ctx' (f ↓ᶠ) (Γ ↓ᶜ) x ⟩
    (f ↓ᶠ) s x (lookup' (Γ ↓ᶜ) x)       ≡⟨⟩
    f s (there x) (lookup' (Γ ↓ᶜ) x)    ≡⟨ cong (f s (there x)) (lookup'-↓ᶜ Γ x) ⟩
    f s (there x) (lookup' Γ (there x)) ≡⟨ sym (lookup-map-Ctx' f Γ (there x)) ⟩
    lookup' (map-Ctx' f Γ) (there x)    ≡⟨ sym (lookup'-↓ᶜ (map-Ctx' f Γ) x) ⟩
    lookup' (map-Ctx' f Γ ↓ᶜ) x         ∎

  map-Ctx'-↓ :
    ∀ {S₁ S₁' S₂ s₂}
    (Γ : Ctx' S₁ (S₂ ▷ s₂))
    (f : Ctx'-Map S₁ S₁' (S₂ ▷ s₂)) →
    map-Ctx' (f ↓ᶠ) (Γ ↓ᶜ) ≡ᶜ (map-Ctx' f Γ) ↓ᶜ
  map-Ctx'-↓ Γ f = ~ᶜ→≡ᶜ (map-Ctx'-↓-~ Γ f)

  data Invert-Ctx' {S₁} : ∀ {S₂} → Ctx' S₁ S₂ → Set where
    Ctx'-∅' :
      {Γ : Ctx' S₁ []} →
      Γ ≡ᶜ ∅' →
      Invert-Ctx' {S₂ = []} Γ
    Ctx'-▶' :
      ∀ S₂ s₂ →
      {Γ : Ctx' S₁ (S₂ ▷ s₂)} →
      (Γ' : Ctx' S₁ S₂) →
      (t : S₁ ▷▷ S₂ ∶⊢ s₂) →
      Γ ≡ᶜ Γ' ▶' t →
      Invert-Ctx' Γ

  invert-Ctx' : ∀ {S₁ S₂} (Γ : Ctx' S₁ S₂) → Invert-Ctx' Γ
  invert-Ctx' {S₂ = []}      Γ = Ctx'-∅' (invert-Ctx'-[] Γ)
  invert-Ctx' {S₂ = S₂ ▷ s₂} Γ with invert-Ctx'-▷ Γ
  ... | Γ' , t , Γ≡ᶜΓ'▶t = Ctx'-▶' _ _ Γ' t Γ≡ᶜΓ'▶t

  _~₃_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} {D : (a : A) → (b : B a) → C a b → Set ℓ₄}
        (f g : ∀ (a : A) (b : B a) → (c : C a b) → D a b c) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  f ~₃ g = ∀ a b c → f a b c ≡ g a b c

  ~-cong-map-Ctx' :
    ∀ {S₁ S₁' S₂}
      {f₁ f₂ : Ctx'-Map S₁ S₁' S₂}
      {Γ₁ Γ₂ : Ctx' S₁ S₂} →
    Γ₁ ~ᶜ Γ₂ →
    f₁ ~₃ f₂ →
    map-Ctx' f₁ Γ₁ ~ᶜ map-Ctx' f₂ Γ₂
  ~-cong-map-Ctx' {S₁} {S₁'} {S₂} {f₁} {f₂} {Γ₁} {Γ₂} Γ₁~Γ₂ f₁~f₂ s x =
    lookup' (map-Ctx' f₁ Γ₁) x ≡⟨ lookup-map-Ctx' f₁ Γ₁ x ⟩
    f₁ _ x (lookup' Γ₁ x)      ≡⟨ cong (f₁ _ x) (Γ₁~Γ₂ s x) ⟩
    f₁ _ x (lookup' Γ₂ x)      ≡⟨ f₁~f₂ _ x (lookup' Γ₂ x) ⟩
    f₂ _ x (lookup' Γ₂ x)      ≡⟨ sym (lookup-map-Ctx' f₂ Γ₂ x) ⟩
    lookup' (map-Ctx' f₂ Γ₂) x ∎

  ≡ᶜ-cong-map-Ctx' :
    ∀ {S₁ S₁' S₂}
      {f₁ f₂ : Ctx'-Map S₁ S₁' S₂}
      {Γ₁ Γ₂ : Ctx' S₁ S₂} →
    Γ₁ ≡ᶜ Γ₂ →
    f₁ ~₃ f₂ →
    map-Ctx' f₁ Γ₁ ≡ᶜ map-Ctx' f₂ Γ₂
  ≡ᶜ-cong-map-Ctx' Γ₁≡Γ₂ f₁~f₂ = ~ᶜ→≡ᶜ (~-cong-map-Ctx' (≡ᶜ→~ᶜ Γ₁≡Γ₂) f₁~f₂)

  ≡ᶜ-▷₁ : ∀ {S₁ S₂ s} {Γ₁ Γ₂ : Ctx' S₁ S₂} {t₁ t₂ : S₁ ▷▷ S₂ ∶⊢ s} →
    (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂) →
    Γ₁ ≡ᶜ Γ₂
  ≡ᶜ-▷₁ {S₁} {S₂} {s} {Γ₁} {Γ₂} {t₁} {t₂} eq = ~ᶜ→≡ᶜ (λ s₁ x →
    lookup' Γ₁ x                 ≡⟨ sym (lookup-▶'-there Γ₁ t₁ x) ⟩
    lookup' (Γ₁ ▶' t₁) (there x) ≡⟨ ≡ᶜ→~ᶜ eq _ (there x) ⟩
    lookup' (Γ₂ ▶' t₂) (there x) ≡⟨ lookup-▶'-there Γ₂ t₂ x ⟩
    lookup' Γ₂ x                 ∎)

  ≡ᶜ-▷₂ : ∀ {S₁ S₂ s} {Γ₁ Γ₂ : Ctx' S₁ S₂} {t₁ t₂ : S₁ ▷▷ S₂ ∶⊢ s} →
    (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂) →
    t₁ ≡ t₂
  ≡ᶜ-▷₂ {S₁} {S₂} {s} {Γ₁} {Γ₂} {t₁} {t₂} eq =
    t₁                             ≡⟨ sym (lookup-▶'-here Γ₁ t₁) ⟩
    lookup' (Γ₁ ▶' t₁) (here refl) ≡⟨ ≡ᶜ→~ᶜ eq _ (here refl) ⟩
    lookup' (Γ₂ ▶' t₂) (here refl) ≡⟨ lookup-▶'-here Γ₂ t₂ ⟩
    t₂                             ∎

  _▶▶'_ : ∀ {S₁ S₂ S₃} → Ctx' S₁ S₂ → Ctx' (S₁ ▷▷ S₂) S₃ → Ctx' S₁ (S₂ ▷▷ S₃)
  _▶▶'_ {S₁} {S₂} {[]}     Γ₁ Γ₂ = Γ₁
  _▶▶'_ {S₁} {S₂} {S₃ ▷ s} Γ₁ Γ₂ = (Γ₁ ▶▶' (Γ₂ ↓ᶜ)) ▶' subst (_∶⊢ s) (sym (++-assoc S₃ S₂ S₁)) (lookup' Γ₂ (here refl))

  Ctx : SortCtx → Set
  Ctx S = Ctx' [] S

  ∅ : Ctx []
  ∅ = ∅'

  _▶_ : ∀ {S s} → Ctx S → S ∶⊢ s → Ctx (S ▷ s)
  _▶_ {S} {s} Γ t = Γ ▶' subst (_∶⊢ s) (sym (++-identityʳ S)) t

  _▶▶_ : ∀ {S₁ S₂} → Ctx S₁ → Ctx' S₁ S₂ → Ctx (S₁ ▷▷ S₂)
  _▶▶_ {S₁} {S₂} Γ₁ Γ₂ = Γ₁ ▶▶' subst (λ ■ → Ctx' ■ S₂) (sym (++-identityʳ S₁)) Γ₂

  lookup'' : ∀ {S₁ S₂} → Ctx' S₁ S₂ → ∀ {s} → (x : S₂ ∋ s) → drop-∈ x (S₁ ▷▷ S₂) ∶⊢ s
  lookup'' {S₁} {S₂} Γ {s} x = subst (_∶⊢ s) (sym (drop-∈-▷▷ x)) (lookup' Γ x)

  lookup : ∀ {S} → Ctx' [] S → ∀ {s} → (x : S ∋ s) → drop-∈ x S ∶⊢ s
  lookup {S} Γ {s} x = subst (_∶⊢ s) (++-identityʳ (drop-∈ x S)) (lookup' Γ x)

  cong-lookup : ∀ {S} {Γ₁ : Ctx S} {Γ₂ : Ctx S} {s} {x : S ∋ s} →
    lookup' Γ₁ x ≡ lookup' Γ₂ x → 
    lookup Γ₁ x ≡ lookup Γ₂ x
  cong-lookup {S} {Γ₁} {Γ₂} {s} {x} eq =
    let sub = subst (_∶⊢ s) (++-identityʳ (drop-∈ x S)) in
    cong sub eq

  lookup-▶-here : ∀ {S} (Γ : Ctx S) {s} (t : S ∶⊢ s) →
    lookup (Γ ▶ t) (here refl) ≡ t
  lookup-▶-here {S} Γ {s} t =
    let sub = subst (_∶⊢ s) (++-identityʳ S) in
    let sub⁻¹ = subst (_∶⊢ s) (sym (++-identityʳ S)) in
    lookup (Γ ▶ t) (here refl)               ≡⟨⟩
    sub (lookup' (Γ ▶' sub⁻¹ t) (here refl)) ≡⟨ cong sub (lookup-▶'-here Γ (sub⁻¹ t)) ⟩
    sub (sub⁻¹ t)                            ≡⟨ cancel-subst' _ (++-identityʳ S) t ⟩
    t                                        ∎

  lookup-▶-there : ∀ {S} (Γ : Ctx S) {s} (t : S ∶⊢ s) {sx} (x : S ∋ sx) →
    lookup (Γ ▶ t) (there x) ≡ lookup Γ x
  lookup-▶-there {S} Γ {s} t {sx} x =
    let sub = subst (_∶⊢ sx) (++-identityʳ (drop-∈ x S)) in
    let sub⁻¹ = subst (_∶⊢ s) (sym (++-identityʳ S)) in
    lookup (Γ ▶ t) (there x)               ≡⟨⟩
    sub (lookup' (Γ ▶' sub⁻¹ t) (there x)) ≡⟨ cong sub (lookup-▶'-there Γ (sub⁻¹ t) x) ⟩
    sub (lookup' Γ x)                      ≡⟨⟩
    lookup Γ x                             ∎

  lookup-↓ᶜ : ∀ {S₂ s₂} (Γ : Ctx (S₂ ▷ s₂)) {s} (x : S₂ ∋ s) →
    lookup (Γ ↓ᶜ) x ≡ lookup Γ (there x)
  lookup-↓ᶜ {S₂} {s₂} Γ {s} x =
    let sub = subst (_∶⊢ s) (++-identityʳ (drop-∈ x S₂)) in
    lookup (Γ ↓ᶜ) x           ≡⟨⟩
    sub (lookup' (Γ ↓ᶜ) x)    ≡⟨ cong sub (lookup'-↓ᶜ Γ x) ⟩
    sub (lookup' Γ (there x)) ≡⟨⟩
    lookup Γ (there x)        ∎
    
  ~ᶜ-refl : ∀ {S₁ S₂} {Γ : Ctx' S₁ S₂} → Γ ~ᶜ Γ 
  ~ᶜ-refl = λ s x → refl

  ~ᶜ-sym : ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx' S₁ S₂} → Γ₁ ~ᶜ Γ₂ → Γ₂ ~ᶜ Γ₁
  ~ᶜ-sym Γ₁~Γ₂ = λ s x → sym (Γ₁~Γ₂ s x)

  ~ᶜ-trans : ∀ {S₁ S₂} {Γ₁ Γ₂ Γ₃ : Ctx' S₁ S₂} → Γ₁ ~ᶜ Γ₂ → Γ₂ ~ᶜ Γ₃ → Γ₁ ~ᶜ Γ₃
  ~ᶜ-trans Γ₁~Γ₂ Γ₂~Γ₃ = λ s x → trans (Γ₁~Γ₂ s x) (Γ₂~Γ₃ s x)

  ≡ᶜ-refl : ∀ {S₁ S₂} {Γ : Ctx' S₁ S₂} → Γ ≡ᶜ Γ 
  ≡ᶜ-refl = ~ᶜ→≡ᶜ ~ᶜ-refl

  ≡ᶜ-sym : ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx' S₁ S₂} → Γ₁ ≡ᶜ Γ₂ → Γ₂ ≡ᶜ Γ₁
  ≡ᶜ-sym Γ₁≡Γ₂ = ~ᶜ→≡ᶜ (~ᶜ-sym (≡ᶜ→~ᶜ Γ₁≡Γ₂))

  ≡ᶜ-trans : ∀ {S₁ S₂} {Γ₁ Γ₂ Γ₃ : Ctx' S₁ S₂} → Γ₁ ≡ᶜ Γ₂ → Γ₂ ≡ᶜ Γ₃ → Γ₁ ≡ᶜ Γ₃
  ≡ᶜ-trans Γ₁≡Γ₂ Γ₂≡Γ₃ = ~ᶜ→≡ᶜ (~ᶜ-trans (≡ᶜ→~ᶜ Γ₁≡Γ₂) (≡ᶜ→~ᶜ Γ₂≡Γ₃))

  ~-cong-↓ᶜ :
    ∀ {S S' s'} {Γ₁' Γ₂' : Ctx' S (S' ▷ s')}
    → Γ₁' ~ᶜ Γ₂'
    → Γ₁' ↓ᶜ ~ᶜ Γ₂' ↓ᶜ
  ~-cong-↓ᶜ {S} {S'} {s'} {Γ₁'} {Γ₂'} Γ₁'~Γ₂' s x =
    lookup' (Γ₁' ↓ᶜ) x    ≡⟨ lookup'-↓ᶜ Γ₁' x ⟩
    lookup' Γ₁' (there x) ≡⟨ Γ₁'~Γ₂' _ (there x) ⟩
    lookup' Γ₂' (there x) ≡⟨ sym (lookup'-↓ᶜ Γ₂' x) ⟩
    lookup' (Γ₂' ↓ᶜ) x    ∎

  ≡ᶜ-cong-↓ᶜ :
    ∀ {S S' s'} {Γ₁' Γ₂' : Ctx' S (S' ▷ s')}
    → Γ₁' ≡ᶜ Γ₂'
    → Γ₁' ↓ᶜ ≡ᶜ Γ₂' ↓ᶜ
  ≡ᶜ-cong-↓ᶜ Γ₁'≡Γ₂' = ~ᶜ→≡ᶜ (~-cong-↓ᶜ (≡ᶜ→~ᶜ Γ₁'≡Γ₂'))

  ~-cong-▶' :
    ∀ {S₁ S₂ s} {Γ₁ Γ₂ : Ctx' S₁ S₂} {t₁ t₂ : S₁ ▷▷ S₂ ∶⊢ s}
    → Γ₁ ~ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶' t₁) ~ᶜ (Γ₂ ▶' t₂)
  ~-cong-▶' {S₁} {S₂} {s} {Γ₁} {Γ₂} {t₁} {.t₁} Γ₁~Γ₂ refl sx (here refl) =
    lookup' (Γ₁ ▶' t₁) (here refl) ≡⟨ lookup-▶'-here Γ₁ t₁ ⟩
    t₁                             ≡⟨ sym (lookup-▶'-here Γ₂ t₁) ⟩
    lookup' (Γ₂ ▶' t₁) (here refl) ∎
  ~-cong-▶' {S₁} {S₂} {s} {Γ₁} {Γ₂} {t₁} {.t₁} Γ₁~Γ₂ refl sx (there x) =
    lookup' (Γ₁ ▶' t₁) (there x) ≡⟨ lookup-▶'-there Γ₁ t₁ x ⟩
    lookup' Γ₁ x                 ≡⟨ Γ₁~Γ₂ _ x ⟩
    lookup' Γ₂ x                 ≡⟨ sym (lookup-▶'-there Γ₂ t₁ x) ⟩
    lookup' (Γ₂ ▶' t₁) (there x) ∎

  open import Data.List.Properties using (++-assoc; ++-identityʳ)
  ~-cong-▶ :
    ∀ {S₁ s} {Γ₁ Γ₂ : Ctx S₁} {t₁ t₂ : S₁ ∶⊢ s}
    → Γ₁ ~ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶ t₁) ~ᶜ (Γ₂ ▶ t₂)
  ~-cong-▶ {S₁} {s} {Γ₁} {Γ₂} {t₁} {t₂} Γ₁~Γ₂ refl sx x =
    let sub = subst (_∶⊢ s) (sym (++-identityʳ S₁)) in
    lookup' (Γ₁ ▶ t₁) x      ≡⟨⟩
    lookup' (Γ₁ ▶' sub t₁) x ≡⟨ ~-cong-▶' Γ₁~Γ₂ refl _ x ⟩
    lookup' (Γ₂ ▶' sub t₁) x ≡⟨⟩
    lookup' (Γ₂ ▶ t₁) x ∎

  ≡ᶜ-cong-▶' :
    ∀ {S₁ S₂ s} {Γ₁ Γ₂ : Ctx' S₁ S₂} {t₁ t₂ : S₁ ▷▷ S₂ ∶⊢ s}
    → Γ₁ ≡ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶' t₁) ≡ᶜ (Γ₂ ▶' t₂)
  ≡ᶜ-cong-▶' Γ₁≡Γ₂ t₁≡t₂ = ~ᶜ→≡ᶜ (~-cong-▶' (≡ᶜ→~ᶜ Γ₁≡Γ₂) t₁≡t₂)

  ≡ᶜ-cong-▶ :
    ∀ {S₁ s} {Γ₁ Γ₂ : Ctx S₁} {t₁ t₂ : S₁ ∶⊢ s}
    → Γ₁ ≡ᶜ Γ₂
    → t₁ ≡ t₂
    → (Γ₁ ▶ t₁) ≡ᶜ (Γ₂ ▶ t₂)
  ≡ᶜ-cong-▶ Γ₁≡Γ₂ t₁≡t₂ = ~ᶜ→≡ᶜ (~-cong-▶ (≡ᶜ→~ᶜ Γ₁≡Γ₂) t₁≡t₂)

  ~-cong-▶▶' :
    ∀ {S₁ S₂ S₃} {Γ₁ Γ₂ : Ctx' S₁ S₂} {Γ₁' Γ₂' : Ctx' (S₁ ▷▷ S₂) S₃}
    → Γ₁  ~ᶜ Γ₂
    → Γ₁' ~ᶜ Γ₂'
    → (Γ₁ ▶▶' Γ₁') ~ᶜ (Γ₂ ▶▶' Γ₂')
  ~-cong-▶▶' {S₁} {S₂} {[]}      {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' s x =
    lookup' (Γ₁ ▶▶' Γ₁') x ≡⟨ refl ⟩
    lookup' Γ₁           x ≡⟨  Γ₁~Γ₂ s x ⟩
    lookup' Γ₂           x ≡⟨ refl ⟩
    lookup' (Γ₂ ▶▶' Γ₂') x ∎
  ~-cong-▶▶' {S₁} {S₂} {S₃ ▷ s₃} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' .s₃ x@(here refl) =
    let sub = subst (_∶⊢ s₃) (sym (++-assoc S₃ S₂ S₁)) in
    lookup' (Γ₁ ▶▶' Γ₁') x                                     ≡⟨⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ ▶' sub (lookup' Γ₁' (here refl))) x ≡⟨ lookup-▶'-here (Γ₁ ▶▶' Γ₁' ↓ᶜ) _ ⟩
    sub (lookup' Γ₁' (here refl))                              ≡⟨ cong sub (Γ₁'~Γ₂' _ (here refl)) ⟩
    sub (lookup' Γ₂' (here refl))                              ≡⟨ sym (lookup-▶'-here (Γ₂ ▶▶' Γ₂' ↓ᶜ) _) ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ ▶' sub (lookup' Γ₂' (here refl))) x ≡⟨⟩
    lookup' (Γ₂ ▶▶' Γ₂') x                                     ∎
  ~-cong-▶▶' {S₁} {S₂} {S₃ ▷ s₃} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' s x@(there y) =
    let sub = subst (_∶⊢ s₃) (sym (++-assoc S₃ S₂ S₁)) in
    lookup' (Γ₁ ▶▶' Γ₁') x                                     ≡⟨⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ ▶' sub (lookup' Γ₁' (here refl))) x ≡⟨ lookup-▶'-there (Γ₁ ▶▶' Γ₁' ↓ᶜ) _ y ⟩
    lookup' (Γ₁ ▶▶' Γ₁' ↓ᶜ) y                                  ≡⟨ ~-cong-▶▶' Γ₁~Γ₂ (~-cong-↓ᶜ Γ₁'~Γ₂') _ y ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ) y                                  ≡⟨ sym (lookup-▶'-there (Γ₂ ▶▶' Γ₂' ↓ᶜ) _ y) ⟩
    lookup' (Γ₂ ▶▶' Γ₂' ↓ᶜ ▶' sub (lookup' Γ₂' (here refl))) x ≡⟨⟩
    lookup' (Γ₂ ▶▶' Γ₂') x                                     ∎

  ~-cong-subst :
    ∀ {S₁ S₂ S₁'} {Γ₁ Γ₂ : Ctx' S₁ S₂}
    → Γ₁ ~ᶜ Γ₂
    → (eq : S₁ ≡ S₁')
    → let sub = subst (λ ■ → Ctx' ■ S₂) eq in
      sub Γ₁ ~ᶜ sub Γ₂
  ~-cong-subst Γ₁~Γ₂ refl = Γ₁~Γ₂

  ~-cong-▶▶ :
    ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx S₁} {Γ₁' Γ₂' : Ctx' S₁ S₂}
    → Γ₁  ~ᶜ Γ₂
    → Γ₁' ~ᶜ Γ₂'
    → (Γ₁ ▶▶ Γ₁') ~ᶜ (Γ₂ ▶▶ Γ₂')
  ~-cong-▶▶ {S₁} {S₂} {Γ₁} {Γ₂} {Γ₁'} {Γ₂'} Γ₁~Γ₂ Γ₁'~Γ₂' s x =
    let sub = subst (λ ■ → Ctx' ■ S₂) (sym (++-identityʳ S₁)) in
    lookup' (Γ₁ ▶▶ Γ₁') x      ≡⟨⟩
    lookup' (Γ₁ ▶▶' sub Γ₁') x ≡⟨ ~-cong-▶▶' Γ₁~Γ₂ (~-cong-subst Γ₁'~Γ₂' _) _ x ⟩
    lookup' (Γ₂ ▶▶' sub Γ₂') x ≡⟨⟩
    lookup' (Γ₂ ▶▶ Γ₂') x      ∎

  ≡ᶜ-cong-▶▶ :
    ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx S₁} {Γ₁' Γ₂' : Ctx' S₁ S₂}
    → Γ₁  ≡ᶜ Γ₂
    → Γ₁' ≡ᶜ Γ₂'
    → (Γ₁ ▶▶ Γ₁') ≡ᶜ (Γ₂ ▶▶ Γ₂')
  ≡ᶜ-cong-▶▶ Γ₁≡Γ₂ Γ₁'≡Γ₂' = ~ᶜ→≡ᶜ (~-cong-▶▶ (≡ᶜ→~ᶜ Γ₁≡Γ₂) (≡ᶜ→~ᶜ Γ₁'≡Γ₂'))

  dist-↓-▶▶'-~ :
    ∀ {S₁ S₂ S₃ s} (Γ₁ : Ctx' S₁ S₂) (Γ₂ : Ctx' (S₁ ▷▷ S₂) (S₃ ▷ s)) 
    → (Γ₁ ▶▶' Γ₂) ↓ᶜ ~ᶜ Γ₁ ▶▶' (Γ₂ ↓ᶜ)
  dist-↓-▶▶'-~ {S₁} {S₂} {S₃} {s} Γ₁ Γ₂ sx x =
    let sub = subst (_∶⊢ s) (sym (++-assoc S₃ S₂ S₁)) in
    lookup' ((Γ₁ ▶▶' Γ₂) ↓ᶜ) x    ≡⟨ lookup'-↓ᶜ (Γ₁ ▶▶' Γ₂) x ⟩
    lookup' (Γ₁ ▶▶' Γ₂) (there x) ≡⟨⟩
    lookup' (Γ₁ ▶▶' Γ₂ ↓ᶜ ▶' sub (lookup' Γ₂ (here refl))) (there x) ≡⟨ lookup-▶'-there (Γ₁ ▶▶' Γ₂ ↓ᶜ) _ x ⟩
    lookup' (Γ₁ ▶▶' Γ₂ ↓ᶜ) x      ∎

  dist-↓-▶▶' :
    ∀ {S₁ S₂ S₃ s} (Γ₁ : Ctx' S₁ S₂) (Γ₂ : Ctx' (S₁ ▷▷ S₂) (S₃ ▷ s)) 
    → (Γ₁ ▶▶' Γ₂) ↓ᶜ ≡ᶜ Γ₁ ▶▶' (Γ₂ ↓ᶜ)
  dist-↓-▶▶' Γ₁ Γ₂ = ~ᶜ→≡ᶜ (dist-↓-▶▶'-~ Γ₁ Γ₂)

  dist-↓-▶▶-~ :
    ∀ {S₂ S₃ s} (Γ₁ : Ctx S₂) (Γ₂ : Ctx' S₂ (S₃ ▷ s)) 
    → (Γ₁ ▶▶ Γ₂) ↓ᶜ ~ᶜ Γ₁ ▶▶ (Γ₂ ↓ᶜ)
  dist-↓-▶▶-~ {S₂} {S₃} {s} Γ₁ Γ₂ sx x =
    let sub₁ = subst (λ ■ → Ctx' ■ (S₃ ▷ s)) (sym (++-identityʳ S₂)) in
    let sub₂ = subst (λ ■ → Ctx' ■ S₃) (sym (++-identityʳ S₂)) in
    lookup' ((Γ₁ ▶▶ Γ₂) ↓ᶜ) x       ≡⟨⟩
    lookup' ((Γ₁ ▶▶' sub₁ Γ₂) ↓ᶜ) x ≡⟨ dist-↓-▶▶'-~ Γ₁ (sub₁ Γ₂) _ x ⟩
    lookup' (Γ₁ ▶▶' (sub₁ Γ₂ ↓ᶜ)) x ≡⟨ cong (λ ■ → lookup' (Γ₁ ▶▶' ■) x) (dist-subst _↓ᶜ (sym (++-identityʳ S₂)) Γ₂) ⟩
    lookup' (Γ₁ ▶▶' sub₂ (Γ₂ ↓ᶜ)) x ≡⟨⟩
    lookup' (Γ₁ ▶▶ Γ₂ ↓ᶜ) x         ∎

  dist-↓-▶▶ :
    ∀ {S₂ S₃ s} (Γ₁ : Ctx S₂) (Γ₂ : Ctx' S₂ (S₃ ▷ s))
    → (Γ₁ ▶▶ Γ₂) ↓ᶜ ≡ᶜ Γ₁ ▶▶ (Γ₂ ↓ᶜ)
  dist-↓-▶▶ Γ₁ Γ₂ = ~ᶜ→≡ᶜ (dist-↓-▶▶-~ Γ₁ Γ₂)

  ▶▶-↓ : ∀ {S₁ S₂ s₂} (Γ : Ctx S₁) (Γ' : Ctx' S₁ (S₂ ▷ s₂)) →
    Γ ▶▶ Γ' ≡ Γ ▶▶ (Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)
  ▶▶-↓ {S₁} {S₂} {s₂} Γ Γ' =
    let sub = subst (λ ■ → Ctx' ■ (S₂ ▷ s₂)) (sym (++-identityʳ S₁)) in
    let subx = subst (_∶⊢ s₂) (cong (_▷▷ S₂) (sym (++-identityʳ S₁))) in
    let sub' = subst (_∶⊢ s₂) (sym (++-assoc S₂ S₁ [])) in
    let subx' = subst (_∶⊢ s₂) (trans (cong (_▷▷ S₂) (sym (++-identityʳ S₁))) (sym (++-assoc S₂ S₁ []))) in
    let sub'' = subst (λ ■ → Ctx' ■ S₂) (sym (++-identityʳ S₁)) in
    let sub''' = subst (_∶⊢ s₂) (sym (++-identityʳ (S₁ ▷▷ S₂))) in
    Γ ▶▶ Γ'                                                    ≡⟨⟩
    Γ ▶▶' sub Γ'                                               ≡⟨⟩
    Γ ▶▶' sub Γ' ↓ᶜ     ▶' sub' (lookup' (sub Γ') (here refl)) ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' sub' ■₂)
                                                                           (dist-subst _↓ᶜ _ Γ')
                                                                           (dist-subst' (_▷▷ S₂)
                                                                                        (λ Γ → lookup' Γ (here refl)) _
                                                                                        (cong (_▷▷ S₂)
                                                                                          (sym (++-identityʳ S₁))) Γ')
                                                                   ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' sub' (subx (lookup' Γ' (here refl))) ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' ■₂) refl
                                                                        (subst-merge (_∶⊢ s₂) _ (sym (++-assoc S₂ S₁ [])) (lookup' Γ' (here refl))) ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' subx' (lookup' Γ' (here refl))      ≡⟨ cong₂ (λ ■₁ ■₂ → Γ ▶▶' ■₁ ▶' ■₂) refl
                                                                      (subst-irrelevant _ (sym (++-identityʳ (S₁ ▷▷ S₂))) (lookup' Γ' (here refl))) ⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶' sub''' (lookup' Γ' (here refl))     ≡⟨⟩
    Γ ▶▶' sub'' (Γ' ↓ᶜ) ▶ lookup' Γ' (here refl)               ≡⟨⟩
    Γ ▶▶ Γ' ↓ᶜ ▶ lookup' Γ' (here refl)                        ∎

  dist-↓ᶜ-map : ∀ {S₁' S₁ S₂ s₂} (f : Ctx'-Map S₁ S₁' (S₂ ▷ s₂)) (Γ' : Ctx' S₁ (S₂ ▷ s₂)) →
    map-Ctx' (λ _ x → f _ (there x)) (Γ' ↓ᶜ) ~ᶜ (map-Ctx' f Γ') ↓ᶜ
  dist-↓ᶜ-map {S₁'} {S₁} {S₂} {s₂} f Γ' s x =
    lookup' (map-Ctx' (λ _ x → f _ (there x)) (Γ' ↓ᶜ)) x ≡⟨ lookup-map-Ctx' _ (Γ' ↓ᶜ) x ⟩
    f _ (there x) (lookup' (Γ' ↓ᶜ) x)                    ≡⟨ cong (f _ (there x)) (lookup'-↓ᶜ Γ' x) ⟩
    f _ (there x) (lookup' Γ' (there x))                 ≡⟨ sym (lookup-map-Ctx' f Γ' (there x)) ⟩
    lookup' (map-Ctx' f Γ') (there x)                    ≡⟨ sym (lookup'-↓ᶜ _ x) ⟩
    lookup' (map-Ctx' f Γ' ↓ᶜ) x                         ∎

  lookup-▶▶-here : ∀ {S₂ S₃ s₃} (Γ₁ : Ctx S₂) (Γ₂ : Ctx' S₂ (S₃ ▷ s₃)) →
    lookup (Γ₁ ▶▶ Γ₂) (here refl) ≡ lookup' Γ₂ (here refl)
  lookup-▶▶-here {S₂} {S₃} {s₃} Γ₁ Γ₂ =
    let sub = subst (_∶⊢ s₃) (++-identityʳ (S₂ ▷▷ S₃)) in
    let sub' = subst (λ ■ → Ctx' ■ (S₃ ▷ s₃)) (sym (++-identityʳ S₂)) in
    let sub'x = subst (_∶⊢ s₃) (cong (_▷▷ S₃) (sym (++-identityʳ S₂))) in
    let sub'' = subst (_∶⊢ s₃) (sym (++-assoc S₃ S₂ [])) in
    lookup (Γ₁ ▶▶ Γ₂) (here refl)              ≡⟨⟩
    sub (lookup' (Γ₁ ▶▶' sub' Γ₂) (here refl)) ≡⟨⟩
    sub (lookup' ((Γ₁ ▶▶' (sub' Γ₂ ↓ᶜ)) ▶' sub'' (lookup' (sub' Γ₂) (here refl))) (here refl))
                                               ≡⟨ cong sub (lookup-▶'-here (Γ₁ ▶▶' (sub' Γ₂ ↓ᶜ))
                                                                           (sub'' (lookup' (sub' Γ₂) (here refl)))) ⟩
    sub (sub'' (lookup' (sub' Γ₂) (here refl)))
      ≡⟨ cong (λ ■ → sub (sub'' ■))
              (dist-subst' (λ S → S ▷▷ S₃)
                           ((λ {S} (Γ : Ctx' S (S₃ ▷ s₃)) → lookup' Γ (here refl) ))
                           (sym (++-identityʳ S₂)) (cong (_▷▷ S₃) (sym (++-identityʳ S₂))) Γ₂) ⟩
    sub (sub'' (sub'x (lookup' Γ₂ (here refl))))
      ≡⟨ elim-subst₃ (_∶⊢ s₃)
                     (++-identityʳ (S₂ ▷▷ S₃))
                     (sym (++-assoc S₃ S₂ []))
                     (cong (_▷▷ S₃) (sym (++-identityʳ S₂)))
                     _ ⟩
    lookup' Γ₂ (here refl)                     ∎

  -- lookup-wk : ∀ {S} → Ctx' [] S → ∀ {s} → (x : S ∋ s) → S ∶⊢ s

  open import Kitty.Term.Kit 𝕋
  open import Kitty.Term.Traversal 𝕋
  open import Kitty.Term.Sub 𝕋
  open import Kitty.Term.KitHomotopy {𝕋 = 𝕋}

  module CtxReprSubst {ℓ} (𝕊 : SubWithLaws ℓ) (T : Traversal 𝕊) (H : KitHomotopy T) where
    private instance _ = 𝕊

    open TypeSorts TM
    open Traversal 𝕊 T
    open Kit ⦃ … ⦄
    open SubWithLaws 𝕊
    open Sub SubWithLaws-Sub
    open KitHomotopy T H
    open import Kitty.Term.KitT T

    wk*-Ctx' : ∀ {S₁ S₂} S₁' → Ctx' S₁ S₂ → Ctx' (S₁ ▷▷ S₁') S₂
    wk*-Ctx' {S₁} {S₂} S₁' Γ =
      map-Ctx' (λ sx x t → t ⋯ᵣ ((wkₖ* S₁' (id {S = S₁})) ↑* drop-∈ x S₂)) Γ
      where instance _ = kitᵣ

    wk*-Ctx : ∀ {S₂} S₁ → Ctx S₂ → Ctx' S₁ S₂
    wk*-Ctx {S₂} S₁ Γ =
      let sub = subst (λ ■ → Ctx' ■ S₂) (++-identityʳ S₁) in
      sub (wk*-Ctx' S₁ Γ)

    wk*-Ctx'-↓ :
      ∀ {S₁ S₁' S₂ s₂}
        (Γ : Ctx' S₁ (S₂ ▷ s₂)) →
      wk*-Ctx' S₁' (Γ ↓ᶜ) ≡ᶜ (wk*-Ctx' S₁' Γ) ↓ᶜ
    wk*-Ctx'-↓ {S₁} {S₁'} {S₂} {s₂} Γ = map-Ctx'-↓ Γ _

    wk*-Ctx-↓-~ :
      ∀ {S₁' S₂ s₂}
        (Γ : Ctx (S₂ ▷ s₂)) →
      wk*-Ctx S₁' (Γ ↓ᶜ) ~ᶜ (wk*-Ctx S₁' Γ) ↓ᶜ
    wk*-Ctx-↓-~ {S₁'} {S₂} {s₂} Γ s x =
      let sub₁ = subst (λ ■ → Ctx' ■ S₂) (++-identityʳ S₁') in
      let sub₂ = subst (λ ■ → Ctx' ■ (S₂ ▷ s₂)) (++-identityʳ S₁') in
      lookup' (wk*-Ctx S₁' (Γ ↓ᶜ)) x ≡⟨⟩
      lookup' (sub₁ (wk*-Ctx' S₁' (Γ ↓ᶜ))) x ≡⟨ ~-cong-subst (≡ᶜ→~ᶜ (wk*-Ctx'-↓ Γ)) (++-identityʳ S₁') _ x ⟩
      lookup' (sub₁ ((wk*-Ctx' S₁' Γ) ↓ᶜ)) x ≡⟨ cong (λ ■ → lookup' ■ x) (sym (dist-subst _↓ᶜ (++-identityʳ S₁') _)) ⟩
      lookup' (sub₂ (wk*-Ctx' S₁' Γ) ↓ᶜ) x ≡⟨⟩
      lookup' (wk*-Ctx S₁' Γ ↓ᶜ) x   ∎

    wk*-Ctx-↓ :
      ∀ {S₁' S₂ s₂}
        (Γ : Ctx (S₂ ▷ s₂)) →
      wk*-Ctx S₁' (Γ ↓ᶜ) ≡ᶜ (wk*-Ctx S₁' Γ) ↓ᶜ
    wk*-Ctx-↓ Γ = ~ᶜ→≡ᶜ (wk*-Ctx-↓-~ Γ)

    infixl  5  _⋯Ctx'_
    _⋯Ctx'_ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁ S₂ S'} → Ctx' S₁ S' → S₁ –[ 𝕂 ]→ S₂ → Ctx' S₂ S'
    _⋯Ctx'_ ⦃ 𝕂 ⦄ {S' = S'} Γ ϕ = map-Ctx' (λ _ x t → t ⋯ (ϕ ↑* drop-∈ x S')) Γ

    ~-cong-⋯Ctx' :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ 
        ⦃ K₁ : KitT 𝕂₁ ⦄ 
        ⦃ K₂ : KitT 𝕂₂ ⦄ 
        {S₁ S₁' S₂}
        {ϕ₁ : S₁ –[ 𝕂₁ ]→ S₁'}
        {ϕ₂ : S₁ –[ 𝕂₂ ]→ S₁'}
        {Γ₁ Γ₂ : Ctx' S₁ S₂} →
      Γ₁ ~ᶜ Γ₂ →
      ϕ₁ ~ ϕ₂ →
      (Γ₁ ⋯Ctx' ϕ₁) ~ᶜ (Γ₂ ⋯Ctx' ϕ₂)
    ~-cong-⋯Ctx' ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {S₁} {S₁'} {S₂} {ϕ₁} {ϕ₂} {Γ₁} {Γ₂} Γ₁~Γ₂ ϕ₁~ϕ₂ =
      ~-cong-map-Ctx' Γ₁~Γ₂ (λ s x t → ~-cong-⋯ t (~-cong-↑* ϕ₁~ϕ₂))

    ≡ᶜ-cong-⋯Ctx' :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ 
        ⦃ K₁ : KitT 𝕂₁ ⦄ 
        ⦃ K₂ : KitT 𝕂₂ ⦄ 
        {S₁ S₁' S₂}
        {ϕ₁ : S₁ –[ 𝕂₁ ]→ S₁'}
        {ϕ₂ : S₁ –[ 𝕂₂ ]→ S₁'}
        {Γ₁ Γ₂ : Ctx' S₁ S₂} →
      Γ₁ ≡ᶜ Γ₂ →
      ϕ₁ ~ ϕ₂ →
      (Γ₁ ⋯Ctx' ϕ₁) ≡ᶜ (Γ₂ ⋯Ctx' ϕ₂)
    ≡ᶜ-cong-⋯Ctx' Γ₁≡Γ₂ ϕ₁~ϕ₂ = ~ᶜ→≡ᶜ (~-cong-⋯Ctx' (≡ᶜ→~ᶜ Γ₁≡Γ₂) ϕ₁~ϕ₂)


module FunctionalCtx where
  Ctx' : SortCtx → SortCtx → Set
  Ctx' S₁ S₂ = ∀ s → (x : S₂ ∋ s) → (S₁ ▷▷ drop-∈ x S₂) ∶⊢ s

  ∅' : ∀ {S} → Ctx' S []
  ∅' _ ()

  _▶'_ : ∀ {S₁ S₂ s} → Ctx' S₁ S₂ → (S₁ ▷▷ S₂) ∶⊢ s → Ctx' S₁ (S₂ ▷ s)
  (Γ ▶' t) _ (here refl) = t
  (Γ ▶' t) _ (there x)   = Γ _ x

  lookup' : ∀ {S₁ S₂} → Ctx' S₁ S₂ → ∀ {s} → (x : S₂ ∋ s) → (S₁ ▷▷ drop-∈ x S₂) ∶⊢ s
  lookup' Γ x = Γ _ x

  _≡ᶜ_ : ∀ {S₁ S₂} → (Γ₁ Γ₂ : Ctx' S₁ S₂) → Set 
  Γ₁ ≡ᶜ Γ₂ = ∀ s (x : _ ∋ s) → Γ₁ _ x ≡ Γ₂ _ x 

  _↓ᶜ : ∀ {S₁ S₂ s} → Ctx' S₁ (S₂ ▷ s) → Ctx' S₁ S₂
  Γ ↓ᶜ = λ s x → Γ s (there x)

  map-Ctx' :
    ∀ {S₁ S₁' S₂} →
    (f : ∀ s → (x : S₂ ∋ s) → S₁ ▷▷ drop-∈ x S₂ ∶⊢ s → S₁' ▷▷ drop-∈ x S₂ ∶⊢ s) →
    Ctx' S₁ S₂ →
    Ctx' S₁' S₂
  map-Ctx' f Γ s x = f _ x (Γ s x)

  Functional-CtxRepr : CtxRepr
  Functional-CtxRepr = record
    { Ctx'            = Ctx'
    ; ∅'              = λ {S} → ∅' {S}
    ; _▶'_            = _▶'_
    ; lookup'         = lookup'
    ; lookup-▶'-here  = λ Γ t → refl
    ; lookup-▶'-there = λ Γ t x → refl
    ; invert-Ctx'-[]  = λ Γ s ()
    ; invert-Ctx'-▷   = λ Γ → (Γ ↓ᶜ) , Γ _ (here refl) , λ { s (here refl) → refl ; s (there x) → refl }
    ; lookup-map-Ctx' = λ f Γ x → refl
    ; _≡ᶜ_            = _≡ᶜ_
    ; ≡ᶜ→~ᶜ           = λ Γ₁≡Γ₂ → Γ₁≡Γ₂
    ; ~ᶜ→≡ᶜ           = λ Γ₁≡Γ₂ → Γ₁≡Γ₂
    ; _↓ᶜ             = _↓ᶜ
    ; lookup'-↓ᶜ      = λ Γ x → refl
    ; ↓ᶜ-▶'           = λ Γ t s x → refl
    ; map-Ctx'        = map-Ctx'
    }

open FunctionalCtx public using (Functional-CtxRepr)

module ListCtx where
  data Ctx' : SortCtx → SortCtx → Set where
    []   : ∀ {S₁} → Ctx' S₁ []
    _▶'_ : ∀ {S₁ S₂ s} → Ctx' S₁ S₂ → (S₁ ▷▷ S₂) ∶⊢ s → Ctx' S₁ (S₂ ▷ s)

  lookup' : ∀ {S₁ S₂} → Ctx' S₁ S₂ → ∀ {s} → (x : S₂ ∋ s) → (S₁ ▷▷ drop-∈ x S₂) ∶⊢ s
  lookup' (Γ ▶' t) (here refl) = t
  lookup' (Γ ▶' t) (there x)   = lookup' Γ x

  _↓ᶜ : ∀ {S₁ S₂ s} → Ctx' S₁ (S₂ ▷ s) → Ctx' S₁ S₂
  (Γ ▶' t) ↓ᶜ = Γ

  map-Ctx' :
    ∀ {S₁ S₁' S₂} →
    (f : ∀ s → (x : S₂ ∋ s) → S₁ ▷▷ drop-∈ x S₂ ∶⊢ s → S₁' ▷▷ drop-∈ x S₂ ∶⊢ s) →
    Ctx' S₁ S₂ →
    Ctx' S₁' S₂
  map-Ctx' f []       = []
  map-Ctx' f (Γ ▶' t) = map-Ctx' (λ _ x t' → f _ (there x) t') Γ ▶' f _ (here refl) t

  ~ᶜ→≡ᶜ : ∀ {S₁ S₂} {Γ₁ Γ₂ : Ctx' S₁ S₂} →
    (∀ s (x : S₂ ∋ s) → lookup' Γ₁ x ≡ lookup' Γ₂ x) →
    Γ₁ ≡ Γ₂
  ~ᶜ→≡ᶜ {Γ₁ = []} {Γ₂ = []} Γ₁~Γ₂ = refl
  ~ᶜ→≡ᶜ {Γ₁ = Γ₁ ▶' T₁} {Γ₂ = Γ₂ ▶' T₂} Γ₁~Γ₂
    rewrite ~ᶜ→≡ᶜ {Γ₁ = Γ₁} {Γ₂ = Γ₂} (λ s x → Γ₁~Γ₂ s (there x))
    = cong (Γ₂ ▶'_) (Γ₁~Γ₂ _ (here refl))

  Ctx'-Map : SortCtx → SortCtx → SortCtx → Set
  Ctx'-Map S₁ S₁' S₂ = ∀ s → (x : S₂ ∋ s) → S₁ ▷▷ drop-∈ x S₂ ∶⊢ s → S₁' ▷▷ drop-∈ x S₂ ∶⊢ s

  lookup-map-Ctx' :
    ∀ {S₁ S₁' S₂ s}
    (f : Ctx'-Map S₁ S₁' S₂) →
    (Γ : Ctx' S₁ S₂) →
    (x : S₂ ∋ s) →
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
    ; ≡ᶜ→~ᶜ           = λ { refl s x → refl }
    ; ~ᶜ→≡ᶜ           = ~ᶜ→≡ᶜ
    ; _↓ᶜ             = _↓ᶜ
    ; lookup'-↓ᶜ      = λ { (Γ ▶' t) x → refl }
    ; ↓ᶜ-▶'           = λ Γ t → refl
    ; map-Ctx'        = map-Ctx'
    }

open ListCtx public using (List-CtxRepr)
