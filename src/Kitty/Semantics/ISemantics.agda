open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)
open import Kitty.Typing.ITerms using (ITerms)

module Kitty.Semantics.ISemantics {𝕄 : Modes} {𝕋 : Terms 𝕄} {ℓ} {𝕊 : SubWithLaws 𝕋 ℓ} {T : Traversal 𝕋 𝕊} {H : KitHomotopy 𝕋 𝕊 T}
                         {𝕊C : SubCompose 𝕋 𝕊 T H} (C : ComposeTraversal 𝕋 𝕊 T H 𝕊C) (KT : KitType 𝕋)
                         where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_; proj₁; proj₂)
open import Function using () renaming (_∋_ to _by_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude
open import Kitty.Util.SubstProperties
open import Kitty.Util.Closures

open Modes 𝕄
open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.Sub 𝕋
open Kitty.Term.Sub.SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open Kitty.Term.Traversal.Traversal T
open Kitty.Term.KitHomotopy.KitHomotopy H
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open Kitty.Term.ComposeTraversal.ComposeTraversal C
open Kitty.Typing.Types.KitType KT
open import Kitty.Typing.OPE C KT

open ~-Reasoning

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m
    𝕂 : Kit
    𝔸₁ : ComposeKit 𝕂 kitᵣ 𝕂
    𝔸₂ : ComposeKit kitᵣ 𝕂 𝕂
    -- WK : WkDistKit ⦃ 𝕂 ⦄ ⦃ 𝔸₁ ⦄ ⦃ 𝔸₂ ⦄

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kittᵣ
private instance _ = kittₛ
private instance _ = ckitᵣ
private instance _ = ckitₛᵣ
private instance _ = ckitₛₛ

open ReflexiveTransitiveClosure using (step; refl)

record Semantics : Set₁ where
  infix 3 _↪_
  field
    _↪_ : µ ⊢ M → µ ⊢ M → Set

  open ReflexiveTransitiveClosure₂ (_⊢_) _↪_ renaming
    ( ReflTrans to _↪*_
    ; map-ReflTrans to map-↪*
    ; _⟨_⟩_ to _↪⟨_⟩_
    ; _*⟨_⟩_ to _↪*⟨_⟩_
    ; _≡R⟨_⟩_ to _↪*-≡⟨_⟩_
    ; _∎ to _↪∎
    ; trans to ↪*-trans
    ; embed to ↪*-embed
    ) hiding (refl; step; module Symmetric) public

  infix   3 _↪σ_ _↪*σ_  _≣_ _≣σ_

  _↪σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
  σ₁ ↪σ σ₂ = ∀ {m} (x : _ ∋ m) → x & σ₁ ↪ x & σ₂

  ↪σ-ext : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
    σ₁ ↪σ σ₂ →
    t₁ ↪ t₂ →
    (σ₁ ,ₛ t₁) ↪σ (σ₂ ,ₛ t₂)
  ↪σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (here refl) =
    subst₂ (_↪_) (sym (&-,ₖ-here σ₁ t₁))
                 (sym (&-,ₖ-here σ₂ t₂))
                 t₁≣t₂
  ↪σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (there x) =
    subst₂ (_↪_) (sym (&-,ₖ-there σ₁ t₁ x))
                 (sym (&-,ₖ-there σ₂ t₂ x))
                 (σ₁≣σ₂ x)

  _↪*σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
  σ₁ ↪*σ σ₂ = ∀ {m} (x : _ ∋ m) → x & σ₁ ↪* x & σ₂

  ↪*σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
    σ ↪*σ σ
  ↪*σ-refl {m = 𝕖} x = refl

  ↪*σ-ext : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
    σ₁ ↪*σ σ₂ →
    t₁ ↪* t₂ →
    (σ₁ ,ₛ t₁) ↪*σ (σ₂ ,ₛ t₂)
  ↪*σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (here refl) =
    subst₂ (_↪*_) (sym (&-,ₖ-here σ₁ t₁))
                 (sym (&-,ₖ-here σ₂ t₂))
                 t₁≣t₂
  ↪*σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (there x) =
    subst₂ (_↪*_) (sym (&-,ₖ-there σ₁ t₁ x))
                 (sym (&-,ₖ-there σ₂ t₂ x))
                 (σ₁≣σ₂ x)

  ↪*σ-⦅_⦆ : ∀ {µ m} {t₁ t₂ : µ ⊢ m→M m} →
    t₁ ↪* t₂ →
    ⦅ t₁ ⦆ₛ ↪*σ ⦅ t₂ ⦆ₛ
  ↪*σ-⦅_⦆ {t₁ = t₁} {t₂}  t₁≣t₂  = λ x →
    subst₂ (_↪*_) (sym (~→~' (⦅⦆-,ₖ t₁) _ x))
                 (sym (~→~' (⦅⦆-,ₖ t₂) _ x))
                 (↪*σ-ext (↪*σ-refl {σ = idₛ}) t₁≣t₂ x)

  open ReflexiveTransitiveClosure₂ (_→ₛ_) _↪σ_ renaming
    ( ReflTrans to _↪σ*_
    ; map-ReflTrans to map-↪σ*
    ; _⟨_⟩_ to _↪σ⟨_⟩_
    ; _*⟨_⟩_ to _↪σ*⟨_⟩_
    ; _≡R⟨_⟩_ to _↪σ*-≡⟨_⟩_
    ; _∎ to _↪σ∎
    ; trans to ↪σ*-trans
    ; embed to ↪σ*-embed
    ) hiding (refl; step; module Symmetric) public

  data _≣_ (t₁ t₂ : µ ⊢ M) : Set where
    mk-≣ : ∀ t → (t₁↪*t : t₁ ↪* t) → (t₂↪*t : t₂ ↪* t) → t₁ ≣ t₂

  ≣-refl : ∀ {µ M} {t : µ ⊢ M} → t ≣ t
  ≣-refl = mk-≣ _ refl refl

  ≣-sym : ∀ {µ M} {t₁ t₂ : µ ⊢ M} → t₁ ≣ t₂ → t₂ ≣ t₁
  ≣-sym (mk-≣ t t₁↪*t t₂↪*t) = mk-≣ t t₂↪*t t₁↪*t

  module WithConfluence (confluence : ∀ {µ M} {t t₁ t₂ : µ ⊢ M} → t ↪* t₁ → t ↪* t₂ → ∃[ t' ] t₁ ↪* t' × t₂ ↪* t') where
    ≣-trans : ∀ {µ M} {t₁ t₂ t₃ : µ ⊢ M} → t₁ ≣ t₂ → t₂ ≣ t₃ → t₁ ≣ t₃
    ≣-trans (mk-≣ e e₁↪*e e₂↪*e) (mk-≣ e' e₂↪*e' e₃↪*e') with confluence e₂↪*e e₂↪*e'
    ... | e'' , e↪*e'' , e'↪*e'' = mk-≣ e'' (↪*-trans e₁↪*e e↪*e'') (↪*-trans e₃↪*e' e'↪*e'')

    infixr  2  _≣⟨_⟩_

    _≣⟨_⟩_ : ∀ {µ M} (a₁ : µ ⊢ M) {a₂ a₃ : µ ⊢ M}
      → a₁ ≣ a₂
      → a₂ ≣ a₃
      → a₁ ≣ a₃
    a₁ ≣⟨ p ⟩ q = ≣-trans p q

  infixr  2  _≣-≡⟨_⟩_
  infix   3  _≣∎

  _≣-≡⟨_⟩_ : ∀ {µ M} (a₁ : µ ⊢ M) {a₂ a₃ : µ ⊢ M}
    → a₁ ≡ a₂
    → a₂ ≣ a₃
    → a₁ ≣ a₃
  a₁ ≣-≡⟨ refl ⟩ q = q

  _≣∎ : ∀ {µ M} (a : µ ⊢ M) → a ≣ a
  a ≣∎ = ≣-refl

  map-≣ :
    ∀ {µ} {µ'} {M}
      {f : µ ⊢ M → µ' ⊢ M}
      (F : ∀ {t t' : µ ⊢ M} → t ↪ t' → f t ↪ f t')
      {t t' : µ ⊢ M}
    → t ≣ t'
    → f t ≣ f t'
  map-≣ {f = f} F (mk-≣ t t₁↪*t t₂↪*t) = mk-≣ (f t) (map-↪* F t₁↪*t) (map-↪* F t₂↪*t)

  ≣-↪ : ∀ {µ M} {t t' : µ ⊢ M} → t ↪ t' → t ≣ t'
  ≣-↪ t↪t' = mk-≣ _ (↪*-embed t↪t') refl

  ≣-↩ : ∀ {µ M} {t t' : µ ⊢ M} → t' ↪ t → t ≣ t'
  ≣-↩ t'↪t = mk-≣ _ refl (↪*-embed t'↪t)

  _≣σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
  σ₁ ≣σ σ₂ = ∀ {m} (x : _ ∋ m) → (x & σ₁) ≣ (x & σ₂)

  -- Are Ctx's basically Substitutions which don't weaken automatically?
  -- Can we represent them as such or even generalize our substitutions?
  ≣σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
    σ ≣σ σ
  ≣σ-refl {m = 𝕖} x = ≣-refl

  ≣σ-ext : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
    σ₁ ≣σ σ₂ →
    t₁ ≣ t₂ →
    (σ₁ ,ₛ t₁) ≣σ (σ₂ ,ₛ t₂)
  ≣σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (here refl) =
    subst₂ (_≣_) (sym (&-,ₖ-here σ₁ t₁))
                 (sym (&-,ₖ-here σ₂ t₂))
                 t₁≣t₂
  ≣σ-ext {µ₁} {µ₂} {m} {σ₁} {σ₂} {t₁} {t₂} σ₁≣σ₂ t₁≣t₂ (there x) =
    subst₂ (_≣_) (sym (&-,ₖ-there σ₁ t₁ x))
                 (sym (&-,ₖ-there σ₂ t₂ x))
                 (σ₁≣σ₂ x)

  ≣σ-⦅_⦆ : ∀ {µ m} {t₁ t₂ : µ ⊢ m→M m} →
    t₁ ≣ t₂ →
    ⦅ t₁ ⦆ₛ ≣σ ⦅ t₂ ⦆ₛ
  ≣σ-⦅_⦆ {t₁ = t₁} {t₂}  t₁≣t₂  = λ x →
    subst₂ (_≣_) (sym (~→~' (⦅⦆-,ₖ t₁) _ x))
                 (sym (~→~' (⦅⦆-,ₖ t₂) _ x))
                 (≣σ-ext (≣σ-refl {σ = idₛ}) t₁≣t₂ x)

  ≣→Σ : ∀ {µ M} {t₁ t₂ : µ ⊢ M} → t₁ ≣ t₂ → ∃[ t ] t₁ ↪* t × t₂ ↪* t 
  ≣→Σ (mk-≣ t t₁↪*t t₂↪*t) = t , t₁↪*t , t₂↪*t

  open Kit ⦃ … ⦄
  to-ϕ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂} → (∀ m → (µ₁ ∋ m) → µ₂ ∋/⊢[ 𝕂 ] id/m→M m) → µ₁ –[ 𝕂 ]→ µ₂
  to-ϕ {µ₁ = []}      f = []*
  to-ϕ {µ₁ = µ₁ ▷ m₁} f = to-ϕ (λ _ x → f _ (there x)) ,ₖ f m₁ (here refl)

  &-to-ϕ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂ m} →
    (f : ∀ m → (µ₁ ∋ m) → µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
    (x : µ₁ ∋ m) →
    x & to-ϕ f ≡ f m x
  &-to-ϕ f (here refl) = &-,ₖ-here (to-ϕ (λ _ x → f _ (there x))) (f _ (here refl))
  &-to-ϕ f (there x) = trans (&-,ₖ-there (to-ϕ (λ _ x → f _ (there x))) (f _ (here refl)) x)
                             (&-to-ϕ (λ _ x → f _ (there x)) x)

  ≣σ→↪*σ : ∀ {µ₁ µ₂} {σ σ' : µ₁ →ₛ µ₂} →
    σ ≣σ σ' →
    ∃[ σ'' ] σ ↪*σ σ'' × σ' ↪*σ σ''
  ≣σ→↪*σ {σ = σ} {σ'} σ≣σ' = to-ϕ (λ m x → proj₁ (≣→Σ (σ≣σ' x)))
              , (λ x → subst (x & σ  ↪*_) (sym (&-to-ϕ _ x)) (proj₁ (proj₂ (≣→Σ (σ≣σ' x)))))
              , (λ x → subst (x & σ' ↪*_) (sym (&-to-ϕ _ x)) (proj₂ (proj₂ (≣→Σ (σ≣σ' x)))))

  _≣*_ : ∀ {µ} (Γ₁ Γ₂ : Ctx µ) → Set
  Γ₁ ≣* Γ₂ = ∀ {m} (x : _ ∋ m) → Γ₁ x ≣ Γ₂ x

  ≣*-refl : ∀ {µ} {Γ : Ctx µ} →
    Γ ≣* Γ
  ≣*-refl {m = 𝕖} x = ≣-refl

  ≣*-ext : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {m} {t₁ t₂ : µ ∶⊢ m→M m} →
    Γ₁ ≣* Γ₂ →
    t₁ ≣ t₂ →
    (Γ₁ ▶ t₁) ≣* (Γ₂ ▶ t₂)
  ≣*-ext Γ₁≣Γ₂ t₁≣t₂ (here refl) = t₁≣t₂
  ≣*-ext Γ₁≣Γ₂ t₁≣t₂ (there x)   = Γ₁≣Γ₂ x

  ≣*-↑ : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {m} {t : µ ∶⊢ m→M m} →
    Γ₁ ≣* Γ₂ →
    (Γ₁ ▶ t) ≣* (Γ₂ ▶ t)
  ≣*-↑ ≣Γ = ≣*-ext ≣Γ ≣-refl

  module Valued (Value : ∀ {µ M} → µ ⊢ M → Set) where
    data _⇓_ (e₁ e₂ : µ ⊢ M) : Set where
      ⇓[_,_] :
          e₁ ↪* e₂  
        → Value e₂
        → e₁ ⇓ e₂

record ReflexiveSemantics (Sem : Semantics) : Set₁ where
  open Semantics Sem

  field
    ↪-refl : ∀ {µ m} {t : µ ⊢ m} →
      t ↪ t

  ↪σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
    σ ↪σ σ
  ↪σ-refl {m = 𝕖} x = ↪-refl

  ↪σ-⦅_⦆ : ∀ {µ m} {t₁ t₂ : µ ⊢ m→M m} →
    t₁ ↪ t₂ →
    ⦅ t₁ ⦆ₛ ↪σ ⦅ t₂ ⦆ₛ
  ↪σ-⦅_⦆ {t₁ = t₁} {t₂}  t₁≣t₂  = λ x →
    subst₂ (_↪_) (sym (~→~' (⦅⦆-,ₖ t₁) _ x))
                 (sym (~→~' (⦅⦆-,ₖ t₂) _ x))
                 (↪σ-ext (↪σ-refl {σ = idₛ}) t₁≣t₂ x)

  to''' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} {t₂' t₁'} →
    σ₁ ↓ₛ ~ σ₂ ↓ₛ →
    t₁' ≡ here refl & σ₁ →
    t₂' ≡ here refl & σ₂ →
    t₁' ↪* t₂' →
    σ₁ ↪σ* σ₂
  to''' {σ₁ = σ₁} {σ₂ = σ₂} p refl q refl =
    step (λ { (here refl) → subst (here refl & σ₁ ↪_) q ↪-refl
            ; (there x)   → subst (there x & σ₁ ↪_)
                                  (there x & σ₁ ≡⟨ sym (&-↓ σ₁ x) ⟩
                                   x & σ₁ ↓ₛ    ≡⟨ ~→~' p _ x ⟩
                                   x & σ₂ ↓ₛ    ≡⟨ &-↓ σ₂ x ⟩
                                   there x & σ₂ ∎)
                                  ↪-refl})
          refl
  to''' {σ₁ = σ₁} {σ₂ = σ₂} p refl refl (step {a₂ = t'} t₁↪t' t'↪*t₂) =
    step {a₂ = (σ₁ ↓ₛ) ,ₛ t'}
        (λ { (here refl) → subst (here refl & σ₁ ↪_)
                                 (t'                          ≡⟨ sym (&-,ₖ-here (σ₁ ↓ₛ) t') ⟩
                                  here refl & ((σ₁ ↓ₛ) ,ₛ t') ∎)
                                 t₁↪t'
           ; (there x)   → subst (there x & σ₁ ↪_)
                                 (there x & σ₁            ≡⟨ sym (&-↓ σ₁ x) ⟩
                                  x & σ₁ ↓ₛ               ≡⟨ sym (&-,ₖ-there (σ₁ ↓ₛ) t' x) ⟩
                                  there x & (σ₁ ↓ₛ) ,ₛ t' ∎)
                                 ↪-refl
           })
        (to''' ((((σ₁ ↓ₛ) ,ₛ t') ↓ₛ) ~⟨ ↓-,ₖ (σ₁ ↓ₛ) t' ⟩
                (σ₁ ↓ₛ)              ~⟨ p ⟩
                (σ₂ ↓ₛ)              ~∎)
               (sym (&-,ₖ-here (σ₁ ↓ₛ) t'))
               refl
               t'↪*t₂)

  ≡→~ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂} {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂} →
    ϕ₁ ≡ ϕ₂ →
    ϕ₁ ~ ϕ₂
  ≡→~ refl = ~-refl

  to'' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} {t₁' t₂'} {σ₁' σ₂'} →
    σ₁' ~ σ₁ ↓ₛ →
    σ₂' ≡ σ₂ ↓ₛ →
    t₁' ≡ here refl & σ₁ →
    t₂' ≡ here refl & σ₂ →
    σ₁' ↪σ* σ₂' →
    t₁' ↪* t₂' →
    σ₁ ↪σ* σ₂
  to'' b p refl q refl t₁↪*t₂ = to''' (~-trans (~-sym b) (≡→~ p)) refl q t₁↪*t₂
  to'' {σ₁ = σ₁} b refl refl q (step {a₂ = σ'} σ₁↪*σ' σ'↪*σ₂) t₁↪*t₂ =
    step {a₂ = σ' ,ₛ (here refl & σ₁)}
        (λ { (here refl) → subst (here refl & σ₁ ↪_)
                                 (sym (&-,ₖ-here σ' (here refl & σ₁)))
                                 ↪-refl
           ; (there x)   → subst₂ (_↪_)
                                  (&-↓ σ₁ x)
                                  (sym (&-,ₖ-there σ' (here refl & σ₁) x))
                                  (subst (_↪ x & σ') (~→~' b _ x) (σ₁↪*σ' x))
           })
        (to'' (~-sym (↓-,ₖ σ' (here refl & σ₁)))
              refl
              (sym (&-,ₖ-here σ' (here refl & σ₁))) q σ'↪*σ₂ t₁↪*t₂)

  to' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} →
    σ₁ ↓ₛ ↪σ* σ₂ ↓ₛ →
    here refl & σ₁ ↪* here refl & σ₂ →
    σ₁ ↪σ* σ₂
  to' = to'' ~-refl refl refl refl

  [↪*σ]→[↪σ*] : ∀ {µ₁ µ₂} {σ₁ σ₂ : µ₁ →ₛ µ₂} →
    σ₁ ↪*σ σ₂ →
    σ₁ ↪σ* σ₂
  [↪*σ]→[↪σ*] {[]}     σ₁↪*σ₂ = step (λ ()) refl
  [↪*σ]→[↪σ*] {µ₁ ▷ m} σ₁↪*σ₂ with [↪*σ]→[↪σ*] (λ x → subst₂ (_↪*_) (sym (&-↓ _ x)) (sym (&-↓ _ x)) (σ₁↪*σ₂ (there x)))
  ... | σ₁↪*σ₂' = to' σ₁↪*σ₂' (σ₁↪*σ₂ (here refl))

record SemKit (Sem : Semantics)
    (𝕂 : Kit)
    (K : KitT 𝕂)
    (C₁ : ComposeKit 𝕂 kitᵣ 𝕂)
    (C₂ : ComposeKit 𝕂 𝕂 𝕂)
    : Set₁ where

  open Semantics Sem
  open Kit 𝕂

  infix 3 _≡/↪_

  field
    _≡/↪_ : ∀ {µ M} (t₁ t₂ : µ ∋/⊢ M) → Set
    ≡/↪-wk : ∀ {µ M m} {t₁ t₂ : µ ∋/⊢ M} →
      t₁ ≡/↪ t₂ →
      wk m t₁ ≡/↪ wk m t₂

record SemTraversal (Sem : Semantics) : Set (lsuc ℓ) where
  open Semantics Sem
  open SemKit ⦃ … ⦄

  _↪ϕ_ :
    ∀ ⦃ 𝕂 : Kit ⦄
      ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ SK : SemKit Sem 𝕂 K C₁ C₂ ⦄
      {µ₁ µ₂}
      (ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂) → Set
  ϕ₁ ↪ϕ ϕ₂ = ∀ {m} (x : _ ∋ m) → (x & ϕ₁) ≡/↪ (x & ϕ₂)

  field
    ↪-⋯ :
      ∀ ⦃ 𝕂 : Kit ⦄
        ⦃ K : KitT 𝕂 ⦄
        ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄
        ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
        ⦃ SK : SemKit Sem 𝕂 K C₁ C₂ ⦄
        {µ₁ µ₂ M} {t t' : µ₁ ⊢ M} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂}
      → t ↪ t'
      → ϕ ↪ϕ ϕ'
      → t ⋯ ϕ ↪ t' ⋯ ϕ'

  semkitᵣ : SemKit Sem kitᵣ kittᵣ ckitᵣ ckitᵣ
  semkitᵣ = record
    { _≡/↪_ = _≡_
    ; ≡/↪-wk  = λ { refl → refl }
    }

  private instance _ = semkitᵣ

  ↪-⋯ᵣ : ∀ {µ₁ µ₂ M} {t t' : µ₁ ⊢ M} {ϕ : µ₁ →ᵣ µ₂} →
    t ↪ t' →
    t ⋯ᵣ ϕ ↪ t' ⋯ᵣ ϕ
  ↪-⋯ᵣ t↪t' = ↪-⋯ t↪t' λ x → refl where instance _ = kitᵣ; _ = kittᵣ; _ = ckitₛᵣ; _ = ckitᵣ

  semkitₛ : SemKit Sem kitₛ kittₛ ckitₛᵣ ckitₛₛ
  semkitₛ = record
    { _≡/↪_ = _↪_
    ; ≡/↪-wk  = ↪-⋯ᵣ
    }

  private instance _ = semkitₛ

  ↪-⋯ₛ : ∀ {µ₁ µ₂ M} {t t' : µ₁ ⊢ M} {ϕ ϕ' : µ₁ →ₛ µ₂}
    → t ↪ t'
    → ϕ ↪ϕ ϕ'
    → t ⋯ ϕ ↪ t' ⋯ ϕ'
  ↪-⋯ₛ = ↪-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛᵣ; _ = ckitₛₛ

  open SemKit semkitₛ using () renaming (≡/↪-wk to ↪-wk) public

  ≣-wk : {t₁ t₂ : µ ⊢ M} →
    t₁ ≣ t₂ →
    wkₛ m t₁ ≣ wkₛ m t₂
  ≣-wk = map-≣ ↪-wk

  ≣*-wk-telescope :
    Γ₁ x ≣ Γ₂ x →
    wk-telescope Γ₁ x ≣ wk-telescope Γ₂ x
  ≣*-wk-telescope {x = here refl} eq = ≣-wk eq
  ≣*-wk-telescope {Γ₁ = Γ₁} {x = there x} {Γ₂ = Γ₂}  eq = ≣-wk (≣*-wk-telescope {Γ₁ = λ x → Γ₁ (there x)}
                                                                                {Γ₂ = λ x → Γ₂ (there x)}
                                                                                eq)
