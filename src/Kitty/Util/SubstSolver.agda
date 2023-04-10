module Kitty.Util.SubstSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Util.SubstProperties
open import Function using (id)

module Attempt₁ where
  data Term : (A : Set) → (a : A) → Set₁ where
    `_ : ∀ {A : Set} → (a : A) → Term A a
    _·_ : ∀ {A : Set} {B : A → Set} {f a} →
      Term (∀ (a : A) → B a) f →
      Term A a →
      Term (B a) (f a)
    `subst : ∀ {A : Set} {R : A → Set} {a b ra} →
      Term (R a) ra →
      (a≡b : a ≡ b) →
      Term (R b) (subst R a≡b ra)

  _~_ : ∀ {A a₁ a₂} →
    (t₁ : Term A a₁) →
    (t₂ : Term A a₂) →
    Set
  t₁ ~ t₂ = {!!}

  solve : ∀ {A a₁ a₂} →
    (t₁ : Term A a₁) →
    (t₂ : Term A a₂) →
    t₁ ~ t₂ →
    a₁ ≡ a₂
  solve = {!!}

module Attempt₂ where
  data Term : Set₁ where
    `_ : ∀ {A : Set} → (a : A) → Term
    _·_ : Term → Term → Term
    `subst : Term → Term → Term

  data _⊢_∋_ : Term → (A : Set) → A → Set₁ where
    ⊢` : ∀ (A : Set) (a : A) → (` a) ⊢ A ∋ a
    ⊢· : ∀ {A : Set} {B : A → Set} {tf f ta a} {Ba fa} →
      tf ⊢ (∀ (a : A) → B a) ∋ f →
      ta ⊢ A ∋ a →
      (Ba-eq : Ba ≡ B a) →
      fa ≡ f a →
      (tf · ta) ⊢ Ba ∋ subst id (sym Ba-eq) fa
    ⊢subst : ∀ {A : Set} {R : A → Set} {a b tra ra teq eq} →
      teq ⊢ (a ≡ b) ∋ eq →
      tra ⊢ (R a) ∋ ra →
      `subst teq tra ⊢ (R b) ∋ (subst R eq ra)

  normalize : Term → Term
  normalize (` a)          = ` a
  normalize (t₁ · t₂)      = (normalize t₁) · (normalize t₂)
  normalize (`subst teq t) = normalize t

  normalize-idem : ∀ t →
    normalize (normalize t) ≡ normalize t
  normalize-idem (` a)          = refl
  normalize-idem (t₁ · t₂)      = cong₂ _·_ (normalize-idem t₁) (normalize-idem t₂)
  normalize-idem (`subst t₁ t₂) = normalize-idem t₂

  open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)

  norm-· : ∀ {tf₁ ta₁ tf₂ ta₂} {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set} {a₁ a₂} {b₁ b₂} →
    normalize (tf₁ · ta₁) ≡ normalize (tf₂ · ta₂) →
    (tf₁ · ta₁) ⊢ B₁ a₁ ∋ b₁ →
    (tf₂ · ta₂) ⊢ B₂ a₂ ∋ b₂ →
    Σ[ eq ∈ A₁ ≡ A₂ ]
      subst (λ A → A → Set) eq B₁ ≡ B₂ ×
      subst (λ A → A)       eq a₁ ≡ a₂
  norm-· norm-eq (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁) (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂) = {!!}

  ·-injective : ∀ {tf₁ ta₁ tf₂ ta₂} →
    (tf₁ · ta₁) ≡ (tf₂ · ta₂) →
    (tf₁ ≡ tf₂) × (ta₁ ≡ ta₂)
  ·-injective refl = refl , refl

  eq-∀ : ∀ {A : Set} {B₁ B₂ : A → Set} →
    ((a : A) → B₁ a) ≡ ((a : A) → B₂ a) →
    ∀ {a} → B₁ a ≡ B₂ a
  eq-∀ eq = {!!}

  -- norm-eq : ∀ {t₁ t₂} →
  --   normalize t₁ ≡ normalize t₂ →
  --   t₁ ⊢ ∀ (a : A) → B a  ∋ a₁ →
  --   t₂ ⊢ A₂ ∋ a₂ →

  open import Level renaming (suc to lsuc) using (_⊔_; Setω)

  data Is-∀ : ∀ {ℓ} (A : Set ℓ) → Setω where 
    is-∀ :
      ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
      Is-∀ (∀ (a : A') → B a)
  -- data Is-∀ {ℓ} (A : Set ℓ) : Setω where 
  --   is-∀ :
  --     ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
  --     (leq : ℓ ≡ ℓ₁ ⊔ ℓ₂) →
  --     {!∀ (A : Set ℓ₁) → Set ℓ₂!} →
  --     -- subst {!(λ ℓ → Set ℓ)!} leq A ≡ (∀ (a : A') → B a) →
  --     Is-∀ A

  data Invert-∀ : ∀ {ℓ} (A B : Set ℓ) → Setω where 
    invert-∀ :
      ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B₁ : A → Set ℓ₂} {B₂ : A → Set ℓ₂} →
      (∀ a → B₁ a ≡ B₂ a) →
      Invert-∀ (∀ (a : A) → B₁ a) (∀ (a : A) → B₂ a)

  open import Relation.Nullary using (¬_)
  open import Data.Empty using (⊥; ⊥-elim)
  -- data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Setω where
  --   refl : ∀ {ℓ} {A : Set ℓ} → (Is-∀ A → ⊥) → A ≡ᵗ A
  --   ≡-∀  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → (∀ (a : A) → B a) ≡ᵗ (∀ (a : A) → B a)
  data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Setω where
    refl : ∀ {ℓ} {A : Set ℓ} → (Is-∀ A → Invert-∀ A A) → A ≡ᵗ A
    -- ≡-∀  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → (∀ (a : A) → B a) ≡ᵗ (∀ (a : A) → B a)

  ≡ᵗ→≡ : ∀ {ℓ} {A B : Set ℓ} → A ≡ᵗ B → A ≡ B
  ≡ᵗ→≡ (refl x) = refl
  -- ≡ᵗ→≡ ≡-∀      = refl
  ≡ᵗ-∀ : ∀ {ℓ} {A B : Set ℓ} →
    A ≡ᵗ B →
    Is-∀ A →
    Invert-∀ A B
  ≡ᵗ-∀ (refl x) isall = x isall

  -- data Is-∀ {ℓ} (A : Set ℓ) : Set ℓ where 
  --   is-∀ :
  --     ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
  --     (leq : ℓ ≡ ℓ₁ ⊔ ℓ₂) →
  --     subst id leq A ≡ (∀ (a : A') → B a) →
  --     Is-∀ A 

  -- open import Relation.Nullary using (¬_)
  -- data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ where
  --   refl : ∀ {ℓ} {A : Set } → ¬ (∃[ A' ] ∃[ ℓ' ] Σ[ B ∈ (A' → Set ℓ') ] A ≡ ∀ (a : A') → B a) → A ≡ᵗ A

  record Σω (A : Setω) {ℓ} (B : A → Set ℓ) : Setω where
    constructor _,_
    field
      fst : A
      snd : B fst

  solve : ∀ {A₁ A₂ a₁ a₂ t₁ t₂} →
    t₁ ⊢ A₁ ∋ a₁ →
    t₂ ⊢ A₂ ∋ a₂ →
    normalize t₁ ≡ normalize t₂ →
    Σω (A₁ ≡ᵗ A₂) (λ eq → subst id (≡ᵗ→≡ eq) a₁ ≡ a₂)
  solve {A₁} {A₂} {a₁} {a₂} {.(` a₁)} {.(` a₂)} (⊢` .A₁ .a₁) (⊢` .A₂ .a₂) refl = refl (λ { x → {!x!} }) , {!!}
  solve {A₁} {A₂} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
  solve {A₁} {A₂} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
  solve = {!!}

  -- solve : ∀ {A₁ A₂ a₁ a₂ t₁ t₂} →
  --   t₁ ⊢ A₁ ∋ a₁ →
  --   t₂ ⊢ A₂ ∋ a₂ →
  --   normalize t₁ ≡ normalize t₂ →
  --   Σ[ eq ∈ A₁ ≡ A₂ ] subst id eq a₁ ≡ a₂
  -- solve {A₁} {A₂} {a₁} {a₂} {.(` a₁)} {.(` a₂)} (⊢` .A₁ .a₁) (⊢` .A₂ .a₂) refl = refl , refl
  -- solve {A₁} {A₂} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
  -- solve {A₁} {A₂} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
  -- solve {A₁} {A₂} {.(subst id (sym refl) _)}
  --                 {.(subst id (sym Ba-eq₂) _)}
  --                 {tf₁ · ta₁} {tf₂ · ta₂}
  --                 (⊢· {A = A} {B = B} {f = f} {a = a} ⊢tf₁ ⊢ta₁ refl refl)
  --                 (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
  --                 norm-eq
  --   with ·-injective norm-eq                   
  -- ... | norm-eq-tf , norm-eq-ta
  --   with solve ⊢ta₁ ⊢ta₂ norm-eq-ta
  -- ... | refl , refl
  --   with solve ⊢tf₁ ⊢tf₂ norm-eq-tf
  -- ... | eq-f , refl
  --   with Ba-eq₂ | fa-eq₂
  -- ... | refl | refl
  --   = {!!} , {!!}
  --   -- = eq-∀ eq-f , sym ((subst id eq-f f) a        ≡⟨ {!!} ⟩
  --   --                    subst id (eq-∀ eq-f) (f a) ∎)




  -- solve : ∀ {A a₁ a₂ t₁ t₂} →
  --   t₁ ⊢ A ∋ a₁ →
  --   t₂ ⊢ A ∋ a₂ →
  --   normalize t₁ ≡ normalize t₂ →
  --   a₁ ≡ a₂
  -- solve {A} {.a₁} {.a₂} {` a₁} {` a₂} (⊢` .A .a₁) (⊢` .A .a₂) refl = refl
  -- -- solve {_} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂} ⊢t₁ ⊢t₂ eq
  -- --   = {!⊢t₁!}
  -- solve {A} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂}
  --   (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁)
  --   (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂) eq
  --   = {!!}
  -- -- solve {_} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂} (⊢· {B = B} {a = a₁} ⊢tf₁ ⊢ta₁) ⊢t₂ eq
  -- --   with invert-⊢· ⊢t₂
  -- -- ... | A' , B' , a₂ , f , eqB , refl , ⊢tf₂ , ⊢ta₂
  -- -- --   with solve ⊢tf₁ {!subst₂ (t₂₁ ⊢_∋_) ? ? ⊢t₂₁!} {!!}
  -- -- -- ... | xx 
  -- --   = {!⊢t₂!}
  -- solve {A} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) eq = solve ⊢t₁ ⊢tra eq
  -- solve {_} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ eq' = solve ⊢tra ⊢t₂ eq'
