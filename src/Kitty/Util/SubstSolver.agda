module Kitty.Util.SubstSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Util.SubstProperties
open import Function using (id)
open import Level renaming (suc to lsuc; zero to 0ℓ) using (Level; _⊔_; Setω; Lift; lift; lower)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

variable ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ : Level

-- module Attempt₁ where
--   data Term {ℓ} : ∀ (A : Set ℓ) → (a : A) → Set (lsuc ℓ) where
--     `_ : ∀ {A : Set ℓ} → (a : A) → Term A a
--     _·_ : ∀ {A : Set ℓ} {B : A → Set ℓ} {f a} →
--       Term (∀ (a : A) → B a) f →
--       Term A a →
--       Term (B a) (f a)
--     `subst : ∀ {A : Set ℓ} {R : A → Set ℓ} {a b ra} →
--       Term (R a) ra →
--       (a≡b : a ≡ b) →
--       Term (R b) (subst R a≡b ra)

-- --   _~_ : ∀ {A a₁ a₂} →
-- --     (t₁ : Term A a₁) →
-- --     (t₂ : Term A a₂) →
-- --     Set
-- --   t₁ ~ t₂ = {!!}

-- --   solve : ∀ {A a₁ a₂} →
-- --     (t₁ : Term A a₁) →
-- --     (t₂ : Term A a₂) →
-- --     t₁ ~ t₂ →
-- --     a₁ ≡ a₂
-- --   solve = {!!}

-- module Attempt₂ where
--   data Term ℓ : Set (lsuc ℓ) where
--     `_ : ∀ {A : Set ℓ} → (a : A) → Term ℓ
--     _·_ : Term ℓ → Term ℓ → Term ℓ
--     `subst : Term ℓ → Term ℓ → Term ℓ

--   data _⊢_∋_ {ℓ} : Term ℓ → (A : Set ℓ) → A → Set (lsuc ℓ) where
--     ⊢` : ∀ (A : Set ℓ) (a : A) → (` a) ⊢ A ∋ a
--     ⊢· : ∀ {A : Set ℓ} {B : A → Set ℓ} {tf f ta a} {Ba fa} →
--       tf ⊢ (∀ (a : A) → B a) ∋ f →
--       ta ⊢ A ∋ a →
--       (Ba-eq : Ba ≡ B a) →
--       fa ≡ f a →
--       (tf · ta) ⊢ Ba ∋ subst id (sym Ba-eq) fa
--     ⊢subst : ∀ {A : Set ℓ} {R : A → Set ℓ} {a b tra ra teq eq} →
--       teq ⊢ (a ≡ b) ∋ eq →
--       tra ⊢ (R a) ∋ ra →
--       `subst teq tra ⊢ (R b) ∋ (subst R eq ra)

--   normalize : Term ℓ → Term ℓ
--   normalize (` a)          = ` a
--   normalize (t₁ · t₂)      = (normalize t₁) · (normalize t₂)
--   normalize (`subst teq t) = normalize t

--   normalize-idem : ∀ (t : Term ℓ) →
--     normalize (normalize t) ≡ normalize t
--   normalize-idem (` a)          = refl
--   normalize-idem (t₁ · t₂)      = cong₂ _·_ (normalize-idem t₁) (normalize-idem t₂)
--   normalize-idem (`subst t₁ t₂) = normalize-idem t₂

-- --   norm-· : ∀ {tf₁ ta₁ tf₂ ta₂} {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set} {a₁ a₂} {b₁ b₂} →
-- --     normalize (tf₁ · ta₁) ≡ normalize (tf₂ · ta₂) →
-- --     (tf₁ · ta₁) ⊢ B₁ a₁ ∋ b₁ →
-- --     (tf₂ · ta₂) ⊢ B₂ a₂ ∋ b₂ →
-- --     Σ[ eq ∈ A₁ ≡ A₂ ]
-- --       subst (λ A → A → Set) eq B₁ ≡ B₂ ×
-- --       subst (λ A → A)       eq a₁ ≡ a₂
-- --   norm-· norm-eq (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁) (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂) = {!!}

--   ·-injective : ∀ {tf₁ ta₁ tf₂ ta₂ : Term ℓ} →
--     (tf₁ · ta₁) ≡ (tf₂ · ta₂) →
--     (tf₁ ≡ tf₂) × (ta₁ ≡ ta₂)
--   ·-injective refl = refl , refl

--   eq-∀ : ∀ {A : Set} {B₁ B₂ : A → Set} →
--     ((a : A) → B₁ a) ≡ ((a : A) → B₂ a) →
--     ∀ {a} → B₁ a ≡ B₂ a
--   eq-∀ eq = {!!}

--   -- norm-eq : ∀ {t₁ t₂} →
--   --   normalize t₁ ≡ normalize t₂ →
--   --   t₁ ⊢ ∀ (a : A) → B a  ∋ a₁ →
--   --   t₂ ⊢ A₂ ∋ a₂ →

--   record Σω (A : Setω) {ℓ} (B : A → Set ℓ) : Setω where
--     constructor _,_
--     field
--       fst : A
--       snd : B fst

--   record Σω₁ {ℓ} (A : Set ℓ) (B : A → Setω) : Setω where
--     constructor _,_
--     field
--       fst : A
--       snd : B fst

--   data Is-∀ : ∀ {ℓ} (A : Set ℓ) → Setω where 
--     is-∀ :
--       ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
--       Is-∀ (∀ (a : A') → B a)

--   data Is-∀' : ∀ {ℓ ℓ₁ ℓ₂} (A : Set ℓ) (A' : Set ℓ₁) (B : A' → Set ℓ₂) → Setω where 
--     is-∀' :
--       ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
--       Is-∀' (∀ (a : A') → B a) A' B
--   -- data Is-∀ {ℓ} (A : Set ℓ) : Setω where 
--   --   is-∀ :
--   --     ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
--   --     (leq : ℓ ≡ ℓ₁ ⊔ ℓ₂) →
--   --     {!∀ (A : Set ℓ₁) → Set ℓ₂!} →
--   --     -- subst {!(λ ℓ → Set ℓ)!} leq A ≡ (∀ (a : A') → B a) →
--   --     Is-∀ A

--   data Invert-∀ : ∀ {ℓ} (A B : Set ℓ) → Setω where 
--     invert-∀ :
--       ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B₁ : A → Set ℓ₂} {B₂ : A → Set ℓ₂} →
--       (∀ a → (B₁ a ≡ B₂ a)) →
--       Invert-∀ (∀ (a : A) → B₁ a) (∀ (a : A) → B₂ a)

--   data Invert-∀' : ∀ {ℓ} (A B : Set ℓ) → Setω where 
--     invert-∀' :
--       ∀ {ℓ} {A : Set ℓ} {B₁ : A → Set ℓ} {B₂ : A → Set ℓ} →
--       (∀ a → (B₁ a ≡ B₂ a)) →
--       Invert-∀' (∀ (a : A) → B₁ a) (∀ (a : A) → B₂ a)

--   data Invert-∀'' : ∀ {ℓ} (F₁ F₂ : Set ℓ) (A : Set ℓ) (B₁ B₂ : A → Set ℓ) → Setω where 
--     invert-∀'' :
--       ∀ {ℓ} {A : Set ℓ} {B₁ : A → Set ℓ} {B₂ : A → Set ℓ} →
--       (∀ a → (B₁ a ≡ B₂ a)) →
--       Invert-∀'' (∀ (a : A) → B₁ a) (∀ (a : A) → B₂ a) A B₁ B₂

--   open import Relation.Nullary using (¬_)
--   open import Data.Empty using (⊥; ⊥-elim)
--   -- data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Setω where
--   --   refl : ∀ {ℓ} {A : Set ℓ} → (Is-∀ A → ⊥) → A ≡ᵗ A
--   --   ≡-∀  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → (∀ (a : A) → B a) ≡ᵗ (∀ (a : A) → B a)
--   data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Setω where
--     -- refl : ∀ {ℓ} {A : Set ℓ} → (Is-∀ A → Invert-∀ A A) → A ≡ᵗ A
--     refl : ∀ {ℓ} {A : Set ℓ} → (∀ (A' : Set ℓ) (B : A' → Set ℓ) →
--                                 (Is-∀' A A' B → Invert-∀'' A A A' B B)) → A ≡ᵗ A
--     -- refl : ∀ {ℓ} {A : Set ℓ} → (Σω₁ (Set ℓ) λ A' →
--     --                             Σω₁ (∀ A' → Set ℓ) λ B →
--     --                             (Is-∀' A A' B → Invert-∀'' A A A' B B)) → A ≡ᵗ A
--     -- ≡-∀  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → (∀ (a : A) → B a) ≡ᵗ (∀ (a : A) → B a)

--   data _≡ᵗ'_ {ℓ} (T₁ T₂ : Set ℓ) : Set (lsuc ℓ) where
--     ≡-all :
--       (∀ (A : Set ℓ) (B₁ B₂ : A → Set ℓ) →
--         T₁ ≡ (∀ (a : A) → B₁ a) →
--         T₂ ≡ (∀ (a : A) → B₂ a) →
--         (∀ a → B₁ a ≡ B₂ a)) →
--       T₁ ≡ᵗ' T₂

--   ≡ᵗ'-refl : ∀ {T : Set ℓ} → T ≡ᵗ' T
--   ≡ᵗ'-refl = ≡-all (λ A B₁ B₂ x x₁ a → {!!})

--   data _≡ᵗ''_ {ℓ} (T₁ T₂ : Set ℓ) : Set (lsuc ℓ) where
--     ≡-all :
--       (∀ (A : Set ℓ) (B : A → Set ℓ) →
--         T₁ ≡ (∀ (a : A) → B a) →
--         T₂ ≡ (∀ (a : A) → B a)) →
--       T₁ ≡ᵗ'' T₂

--   ≡ᵗ''-refl : ∀ {T : Set ℓ} → T ≡ᵗ'' T
--   ≡ᵗ''-refl = ≡-all λ A B x → x

--   ≡ᵗ→≡ : ∀ {ℓ} {A B : Set ℓ} → A ≡ᵗ B → A ≡ B
--   ≡ᵗ→≡ (refl x) = refl
--   -- ≡ᵗ→≡ ≡-∀      = refl

--   -- ≡ᵗ-∀ : ∀ {ℓ} {A B : Set ℓ} →
--   --   A ≡ᵗ B →
--   --   Is-∀ A →
--   --   Invert-∀ A B
--   --   -- ∀ a → (B₁ a ≡ B₂ a)
--   -- ≡ᵗ-∀ (refl x) isall = x isall

--   ≡ᵗ-∀ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B₁ B₂ : A → Set ℓ₂} →
--     ((a : A) → B₁ a) ≡ᵗ ((a : A) → B₂ a) →
--     ∀ a → (B₁ a ≡ B₂ a)
--   ≡ᵗ-∀ eq = {!eq!}

--   ≡ᵗ-∀' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B₁ B₂ : A → Set ℓ₂} {T U} →
--     T ≡ ((a : A) → B₁ a) →
--     U ≡ ((a : A) → B₁ a) →
--     Invert-∀ T U →
--     ∀ a → (B₁ a ≡ B₂ a)
--   ≡ᵗ-∀' eqT eqU eq = {!eq!}

--   ≡ᵗ-∀'' : ∀ {ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} {T U} →
--     T ≡ ((a : A) → B₁ a) →
--     U ≡ ((a : A) → B₁ a) →
--     Invert-∀ T U →
--     ∀ a → (B₁ a ≡ B₂ a)
--   ≡ᵗ-∀'' eqT eqU (invert-∀ x) = {!!}

--   ≡ᵗ-∀''' : ∀ {ℓ} {F₁ F₂ : Set (lsuc ℓ)} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} →
--     Is-∀' F₁ A B₁ →
--     Is-∀' F₂ A B₂ →
--     Invert-∀' F₁ F₂ →
--     ∀ a → (B₁ a ≡ B₂ a)
--   ≡ᵗ-∀''' is₁ is₂ (invert-∀' x) = {!!}

--   inv-is-all : ∀ {ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} {T} →
--     T ≡ ((a : A) → B₁ a) →
--     Is-∀' T A B₂ →
--     B₁ ≡ B₂
--   inv-is-all eq is-∀' = {!!}

--   inv-≡ᵗ-∀ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B₁ B₂ : A → Set ℓ₂} →
--     ((a : A) → B₁ a) ≡ᵗ ((a : A) → B₂ a) →
--     ∀ a → (B₁ a ≡ B₂ a)
--   inv-≡ᵗ-∀ eq = {!eq!}

--   inv-∀ : ∀ {ℓ} {F₁ F₂ : Set ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} →
--     Invert-∀'' F₁ F₂ A B₁ B₂ →
--     ∀ a → (B₁ a ≡ B₂ a)
--   inv-∀ (invert-∀'' x) = x

--   ≡ᵗ-∀'''' : ∀ {ℓ} {F₁ F₂ : Set ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} →
--     F₁ ≡ᵗ F₂ →
--     Is-∀' F₁ A B₁ →
--     Is-∀' F₂ A B₂ →
--     -- Σ[ A ∈ Set ℓ ] Σ[ B₁ ∈ (A → Set ℓ) ] Σ[ B₂ ∈ (A → Set ℓ) ]
--       -- F₁ ≡ (∀ (a : A) → B₁ a) ×
--       -- F₂ ≡ (∀ (a : A) → B₂ a) ×
--       (∀ a → (B₁ a ≡ B₂ a))
--   ≡ᵗ-∀'''' (refl x) all₁ all₂ with x _ _ all₁
--   ≡ᵗ-∀'''' (refl x) is-∀' all₂ | invert-∀'' x₁ = {!!}

--   -- ≡ᵗ-∀x : ∀ {ℓ} {A : Set ℓ₁} {B₁ B₂ : A → Set ℓ₂} →
--   --   ((a : A) → B₁ a) ≡ᵗ ((a : A) → B₂ a) →
--   --   ∀ a → (B₁ a ≡ B₂ a)
--   -- ≡ᵗ-∀x eq = {!eq!}

-- -- Have: Invert-∀ ((a₁ : A) → B a₁) ((a₁ : A) → B₁ a₁)

--   -- data Is-∀ {ℓ} (A : Set ℓ) : Set ℓ where 
--   --   is-∀ :
--   --     ∀ {ℓ₁ ℓ₂} {A' : Set ℓ₁} {B : A' → Set ℓ₂} →
--   --     (leq : ℓ ≡ ℓ₁ ⊔ ℓ₂) →
--   --     subst id leq A ≡ (∀ (a : A') → B a) →
--   --     Is-∀ A 

--   -- open import Relation.Nullary using (¬_)
--   -- data _≡ᵗ_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ where
--   --   refl : ∀ {ℓ} {A : Set } → ¬ (∃[ A' ] ∃[ ℓ' ] Σ[ B ∈ (A' → Set ℓ') ] A ≡ ∀ (a : A') → B a) → A ≡ᵗ A

--   -- solve : ∀ {A₁ A₂ a₁ a₂} {t₁ t₂ : Term ℓ} →
--   --   t₁ ⊢ A₁ ∋ a₁ →
--   --   t₂ ⊢ A₂ ∋ a₂ →
--   --   normalize t₁ ≡ normalize t₂ →
--   --   Σ[ eq ∈ (A₁ ≡ A₂) ] A₁ ≡ᵗ'' A₂ × subst id eq a₁ ≡ a₂
--   -- solve {ℓ} {A₁} {A₂} {a₁} {a₂} {.(` a₁)} {.(` a₂)} (⊢` .A₁ .a₁) (⊢` .A₂ .a₂) refl =
--   --   refl , ≡ᵗ''-refl , refl
--   -- solve {ℓ} {A₁} {A₂} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
--   -- solve {ℓ} {A₁} {A₂} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
--   -- solve {ℓ} {A₁} {A₂} {.(subst id (sym refl) _)}
--   --                 {.(subst id (sym Ba-eq₂) _)}
--   --                 {tf₁ · ta₁} {tf₂ · ta₂}
--   --                 (⊢· {A = A} {B = B} {f = f} {a = a} ⊢tf₁ ⊢ta₁ refl refl)
--   --                 (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
--   --                 norm-eq
--   --   with ·-injective norm-eq                   
--   -- ... | norm-eq-tf , norm-eq-ta
--   --   with solve ⊢ta₁ ⊢ta₂ norm-eq-ta
--   -- ... | refl , inv-a₁ , refl
--   --   with solve ⊢tf₁ ⊢tf₂ norm-eq-tf
--   -- ... | eq-f , inv-f'@(≡-all inv-f) , refl
--   --   with Ba-eq₂ | fa-eq₂
--   -- ... | refl | refl
--   -- --   with ≡ᵗ-∀ eq-f is-∀
--   -- -- ... | xx 
--   --   = {!inv-f _ _ refl !} , {!!}




--   -- solve : ∀ {A₁ A₂ a₁ a₂ t₁ t₂} →
--   --   t₁ ⊢ A₁ ∋ a₁ →
--   --   t₂ ⊢ A₂ ∋ a₂ →
--   --   normalize t₁ ≡ normalize t₂ →
--   --   Σ[ eq ∈ A₁ ≡ A₂ ] subst id eq a₁ ≡ a₂
--   -- solve {A₁} {A₂} {a₁} {a₂} {.(` a₁)} {.(` a₂)} (⊢` .A₁ .a₁) (⊢` .A₂ .a₂) refl = refl , refl
--   -- solve {A₁} {A₂} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
--   -- solve {A₁} {A₂} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
--   -- solve {A₁} {A₂} {.(subst id (sym refl) _)}
--   --                 {.(subst id (sym Ba-eq₂) _)}
--   --                 {tf₁ · ta₁} {tf₂ · ta₂}
--   --                 (⊢· {A = A} {B = B} {f = f} {a = a} ⊢tf₁ ⊢ta₁ refl refl)
--   --                 (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
--   --                 norm-eq
--   --   with ·-injective norm-eq                   
--   -- ... | norm-eq-tf , norm-eq-ta
--   --   with solve ⊢ta₁ ⊢ta₂ norm-eq-ta
--   -- ... | refl , refl
--   --   with solve ⊢tf₁ ⊢tf₂ norm-eq-tf
--   -- ... | eq-f , refl
--   --   with Ba-eq₂ | fa-eq₂
--   -- ... | refl | refl
--   --   = {!!} , {!!}
--   --   -- = eq-∀ eq-f , sym ((subst id eq-f f) a        ≡⟨ {!!} ⟩
--   --   --                    subst id (eq-∀ eq-f) (f a) ∎)


--   ⊢-unique : ∀ {t : Term ℓ} {A A' : Set ℓ} {a : A} {a' : A'} →
--     t ⊢ A ∋ a →
--     t ⊢ A' ∋ a' →
--     Σ[ eq ∈ A ≡ A' ] subst id eq a ≡ a' 
--   ⊢-unique (⊢` _ _) (⊢` _ _) = refl , refl
--   ⊢-unique (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁) (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
--     with ⊢-unique ⊢ta₁ ⊢ta₂
--   ... | refl , refl
--     with ⊢-unique ⊢tf₁ ⊢tf₂
--   ... | eq-B , eq-b
--     = {!!} , {!!}
--   ⊢-unique (⊢subst ⊢a ⊢a₁) ⊢a' = {!!}

--   norm-eq' : ∀ {t₁ t₂ : Term ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} {b₁ b₂} →
--     t₁ ⊢ (∀ (a : A) → B₁ a) ∋ b₁ →
--     t₂ ⊢ (∀ (a : A) → B₂ a) ∋ b₂ →
--     normalize t₁ ≡ normalize t₂ →
--     B₁ ≡ B₂
--   -- norm-eq' {ℓ} {` a}          {` a₁}         (⊢` _ .a) (⊢` _ .a₁) norm-eq = {!!}
--   norm-eq' {ℓ} {` a}          {` .a}         ⊢t₁@(⊢` _ .a) ⊢t₂ refl = {!!}
--   norm-eq' {ℓ} {` a}          {`subst t₂ t₃} ⊢t₁ ⊢t₂ norm-eq =      {!!}
--   norm-eq' {ℓ} {t₁ · t₃}      {t₂}           ⊢t₁ ⊢t₂ norm-eq =                {!!}
--   norm-eq' {ℓ} {`subst t₁ t₃} {t₂}           ⊢t₁ ⊢t₂ norm-eq =                {!!}


--   solve : ∀ {A a₁ a₂} {t₁ t₂ : Term ℓ} →
--     t₁ ⊢ A ∋ a₁ →
--     t₂ ⊢ A ∋ a₂ →
--     normalize t₁ ≡ normalize t₂ →
--     a₁ ≡ a₂
--   solve {ℓ} {A} {.a₁} {.a₂} {` a₁} {` a₂} (⊢` .A .a₁) (⊢` .A .a₂) refl = refl
--   -- solve {_} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂} ⊢t₁ ⊢t₂ eq
--   --   = {!⊢t₁!}
--   solve {ℓ} {A} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂}
--     (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁)
--     (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂) norm-eq
--     with ·-injective norm-eq                   
--   ... | norm-eq-tf , norm-eq-ta
--     with solve ⊢ta₁ {!⊢ta₂!} norm-eq-ta
--   ... | xx 
--     = {!!}
--   -- solve {_} {_} {_} {tf₁ · ta₁} {tf₂ · ta₂} (⊢· {B = B} {a = a₁} ⊢tf₁ ⊢ta₁) ⊢t₂ eq
--   --   with invert-⊢· ⊢t₂
--   -- ... | A' , B' , a₂ , f , eqB , refl , ⊢tf₂ , ⊢ta₂
--   -- --   with solve ⊢tf₁ {!subst₂ (t₂₁ ⊢_∋_) ? ? ⊢t₂₁!} {!!}
--   -- -- ... | xx 
--   --   = {!⊢t₂!}
--   solve {ℓ} {A} {a₁} {_} {t₁} {`subst teq tra} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) eq = solve ⊢t₁ ⊢tra eq
--   solve {ℓ} {_} {_} {a₂} {`subst teq tra} {t₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ eq' = solve ⊢tra ⊢t₂ eq'


module Attempt₃ where
  data Term ℓ : Set (lsuc ℓ) where
    `_ : ∀ {A : Set ℓ} → (a : A) → Term ℓ
    _·_ : Term ℓ → Term ℓ → Term ℓ
    `subst : Term ℓ → Term ℓ → Term ℓ

  mutual
    data Type ℓ : Set (lsuc ℓ) where
      `ᵗ : (A : Set ℓ) → Type ℓ
      `∀ : (A : Type ℓ) → (⟦ A ⟧ → Type ℓ) → Type ℓ

    ⟦_⟧ : Type ℓ → Set ℓ
    ⟦ `ᵗ A   ⟧ = A
    ⟦ `∀ A B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B a ⟧

  data _⊢_∋_ {ℓ} : Term ℓ → (A : Type ℓ) → ⟦ A ⟧ → Set (lsuc ℓ) where
    ⊢` : ∀ (A : Set ℓ) (a : A) → (` a) ⊢ `ᵗ A ∋ a
    ⊢· : ∀ {A : Type ℓ} {B : ⟦ A ⟧ → Type ℓ} {tf f ta a} {Ba fa} →
      tf ⊢ `∀ A B ∋ f →
      ta ⊢ A ∋ a →
      (Ba-eq : Ba ≡ B a) →
      fa ≡ f a →
      (tf · ta) ⊢ Ba ∋ subst id (sym (cong ⟦_⟧ Ba-eq)) fa
    ⊢subst : ∀ {A : Type ℓ} {R : ⟦ A ⟧ → Type ℓ} {a b tra ra teq eq} →
      teq ⊢ `ᵗ (a ≡ b) ∋ eq →
      tra ⊢ (R a) ∋ ra →
      `subst teq tra ⊢ (R b) ∋ (subst (λ a → ⟦ R a ⟧) eq ra)

  normalize : Term ℓ → Term ℓ
  normalize (` a)          = ` a
  normalize (t₁ · t₂)      = (normalize t₁) · (normalize t₂)
  normalize (`subst teq t) = normalize t

  ·-injective : ∀ {tf₁ ta₁ tf₂ ta₂ : Term ℓ} →
    (tf₁ · ta₁) ≡ (tf₂ · ta₂) →
    (tf₁ ≡ tf₂) × (ta₁ ≡ ta₂)
  ·-injective refl = refl , refl

  solve : ∀ {A₁ A₂ : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧} →
    t₁ ⊢ A₁ ∋ a₁ →
    t₂ ⊢ A₂ ∋ a₂ →
    normalize t₁ ≡ normalize t₂ →
    Σ[ eq ∈ (A₁ ≡ A₂) ] subst id (cong ⟦_⟧ eq) a₁ ≡ a₂
  solve {ℓ} {A₁} {A₂} {.(` a₁)} {.(` a₂)} {.a₁} {.a₂} (⊢` _ a₁) (⊢` _ a₂) refl = refl , refl
  solve {ℓ} {_} {A₂} {_} {t₂} {_} {a₂} (⊢subst {eq = refl} ⊢teq ⊢tra) ⊢t₂ norm-eq = solve ⊢tra ⊢t₂ norm-eq
  solve {ℓ} {_} {A₂} {_} {t₂} {_} {a₂} ⊢t₁ (⊢subst {eq = refl} ⊢teq ⊢tra) norm-eq = solve ⊢t₁ ⊢tra norm-eq
  solve {ℓ} {A₁} {A₂}
        {.(_ · _)} {.(_ · _)}
        {.(subst id (sym (cong ⟦_⟧ Ba-eq₁)) _)}
        {.(subst id (sym (cong ⟦_⟧ Ba-eq₂)) _)}
        (⊢· ⊢tf₁ ⊢ta₁ Ba-eq₁ fa-eq₁)
        (⊢· ⊢tf₂ ⊢ta₂ Ba-eq₂ fa-eq₂)
        norm-eq
    with ·-injective norm-eq                   
  ... | norm-eq-tf , norm-eq-ta
    with solve ⊢ta₁ ⊢ta₂ norm-eq-ta
  ... | refl , refl
    with solve ⊢tf₁ ⊢tf₂ norm-eq-tf
  ... | refl , refl
    with Ba-eq₂ | fa-eq₂
  ... | refl | refl
    with Ba-eq₁ | fa-eq₁
  ... | refl | refl
    =  refl , refl

  solve' : ∀ {A : Type ℓ} {t₁ t₂ : Term ℓ} {a₁ a₂ : ⟦ A ⟧} →
    t₁ ⊢ A ∋ a₁ →
    t₂ ⊢ A ∋ a₂ →
    normalize t₁ ≡ normalize t₂ →
    a₁ ≡ a₂
  solve' ⊢t₁ ⊢t₂ norm-eq with solve ⊢t₁ ⊢t₂ norm-eq
  ... | refl , eqa = eqa

  module Example where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Data.Vec
    open import Data.Vec.Properties

    data Index : ℕ → Set where
      index : ∀ n → Index n 

    test₁ : ∀ m n (i : Index (m + n)) →
      subst Index (+-comm n m) (subst Index (+-comm m n) i) ≡ i
    test₁ m n i = solve'
      {t₁ = `subst (` (+-comm n m)) (`subst (` (+-comm m n)) (` i))}
      {t₂ = ` i}
      (⊢subst {A = `ᵗ ℕ} {R = λ n → `ᵗ (Index n)} (⊢` _ (+-comm n m))
        (⊢subst {A = `ᵗ ℕ} {R = λ n → `ᵗ (Index n)} (⊢` _ (+-comm m n))
          (⊢` (Index (m + n)) i)))
      (⊢` (Index (m + n)) i)
      refl

    -- test₂ : ∀ m n p (u : Vec ℕ m) (v : Vec ℕ n) (w : Vec ℕ p) →
    --   (u ++ (v ++ w)) ≡ subst (Vec ℕ) (+-assoc m n p) ((u ++ v) ++ w)
    -- test₂ m n p u v w = solve' {t₁ = (` _++_ {0ℓ} {ℕ} {m} {n}) · {!(` u)!}} (⊢· {!!} {!!} refl refl) {!!} {!!}


