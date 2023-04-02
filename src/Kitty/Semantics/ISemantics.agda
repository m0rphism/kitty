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
                         (IT : ITerms C KT) where

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
open Kitty.Typing.ITerms C KT
open Kitty.Typing.ITerms.ITerms IT

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

record Semantics : Set₁ where
  infix 3 _↪_
  field
    _↪_ : µ ⊢ M → µ ⊢ M → Set

    ↪-refl : ∀ {µ m} {t : µ ⊢ m} →
      t ↪ t

  open ReflexiveTransitiveClosure using (step; refl)

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

  _↪σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
  σ₁ ↪σ σ₂ = ∀ {m} (x : _ ∋ m) → x & σ₁ ↪ x & σ₂

  _↪*σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
  σ₁ ↪*σ σ₂ = ∀ {m} (x : _ ∋ m) → x & σ₁ ↪* x & σ₂

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

  module Valued (Value : ∀ {µ M} → µ ⊢ M → Set) where
    data _⇓_ (e₁ e₂ : µ ⊢ M) : Set where
      ⇓[_,_] :
          e₁ ↪* e₂  
        → Value e₂
        → e₁ ⇓ e₂

  open ~-Reasoning
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

-- record ISemKit
--     (𝕂 : Kit)
--     (K : KitT 𝕂)
--     (C₁ : ComposeKit 𝕂 kitᵣ 𝕂)
--     (C₂ : ComposeKit 𝕂 𝕂 𝕂)
--     : Set₁ where

--   infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
--   infixl  6  _∋↑/⊢↑_
--   -- infixl  5  _,ₖ_
--   -- infixl  6  _↑_  _↑*_

--   private instance _ = kitᵣ
--   private instance _ = kitₛ
--   private instance _ = kittᵣ
--   private instance _ = kittₛ
--   private instance _ = ckitᵣ
--   private instance _ = 𝕂
--   private instance _ = K
--   private instance _ = C₁
--   private instance _ = C₂

--   open Kit 𝕂
--   open KitT K

--   field
--     -- Variable/Term Typing
--     _∋/⊢_∶_  : ∀ {m/M} → Ctx µ → µ ∋/⊢ m/M → µ ∶⊢ m→M/id m/M → Set

--     ∋/⊢∶-lookup : ∀ {m} x → Γ ∋/⊢ id/` x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) (wk-telescope Γ x)

--     -- Conditional Applications of Variable-Typing-Rule
--     id/⊢`    : ∀ {x : µ ∋ m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
--                → Γ ∋ x ∶ t
--                →  Γ ∋/⊢ id/` x ∶ subst (µ ∶⊢_) (sym (id/m→M/id m)) t
--     ⊢`/id    : ∀ {e : µ ∋/⊢ id/m→M m} {t : µ ∶⊢ m→M m} {Γ : Ctx µ}
--                → Γ ∋/⊢ e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t
--                → Γ ⊢ `/id e ∶ t
--     ⊢`/id'   : ∀ {m/M} {e : µ ∋/⊢ m/M} {t : µ ∶⊢ m→M/id m/M} {Γ : Ctx µ}
--                → Γ ∋/⊢ e ∶ t
--                → Γ ⊢ `/id' e ∶ t

--     -- Weakening preserveres variable/term typings.
--     ∋wk/⊢wk  : ∀ {m/M} (Γ : Ctx µ) (t' : µ ∶⊢ m→M m) (e : µ ∋/⊢ m/M) (t : µ ∶⊢ m→M/id m/M)
--                → Γ ∋/⊢ e ∶ t
--                → (Γ ▶ t') ∋/⊢ wk _ e ∶ Kit.wk kitₛ _ t
--     -- ⊢wk-vr : ∀ {x : µ ∋ m} {t : µ ∶⊢ M} (⊢x : Γ ∋ x ∶ t) →
--     --          ⊢wk (⊢vr ⊢x) ≡ ⊢vr (there x)
--     -- wk-vr     : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (vr _ x) ≡ vr _ (there x)
--     -- id/`/id     : ∀ x → subst (µ ⊢_) (m→m/M→M m) (tm _ (vr _ x)) ≡ ` x

--   -- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
--   -- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
--   -- _∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
--   -- _∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ (x : µ₁ ∋ 𝕖) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ
--   -- TODO: IS THIS EQUIVALENT TO OPE?

--   _∋*/⊢*_∶_ : Ctx µ₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
--   _∋*/⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ ϕ Γ₁ =
--     -- ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ◆ f _ x ∶ subst (µ₂ ∶⊢_) (sym (m→m/M→M m₁)) (wk-telescope Γ₁ x ⋯ f)
--     ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m→M m₁) (⊢x : Γ₁ ∋ x ∶ t)
--     → Γ₂ ∋/⊢ (x & ϕ) ∶ subst (µ₂ ∶⊢_) (sym (id/m→M/id m₁)) (t ⋯ ϕ)

--   _∋↑/⊢↑_ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
--     Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
--     ∀ t →
--     (Γ₂ ▶ (t ⋯ ϕ)) ∋*/⊢* (ϕ ↑ m) ∶ (Γ₁ ▶ t)
--   _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} ⊢ϕ t' (here refl) .(t' ⋯ᵣ wknᵣ) refl =
--     Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ (here refl & ϕ ↑ _) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (t' ⋯ᵣ wknᵣ ⋯ ϕ ↑ _)
--       by subst₂ (λ ■₁ ■₂ → Γ₂ ▶ (t' ⋯ ϕ) ∋/⊢ ■₁ ∶ ■₂)
--         (sym (&-↑-here ϕ))
--         (cong (subst _ _) (sym (dist-↑-f t' ϕ))) (
--     Γ₂ ▶ t' ⋯ ϕ ∋/⊢ id/` (here refl) ∶ subst (_∶⊢_ (µ₂ ▷ _)) (sym (id/m→M/id _)) (t' ⋯ ϕ ⋯ᵣ wknᵣ)
--       by id/⊢` {x = here refl} {Γ = Γ₂ ▶ (t' ⋯ ϕ)} refl)
--   _∋↑/⊢↑_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} ⊢ϕ t (there x) _ refl =
--     Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ (there x & ϕ ↑ _) ∶ subst ((µ₂ ▷ _) ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
--       by subst₂ (λ ■₁ ■₂ → Γ₂ ▶ (t ⋯ ϕ) ∋/⊢ ■₁ ∶ ■₂)
--         (sym (&-↑-there ϕ x))
--         (
--          begin
--            subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ) ⋯ᵣ wknᵣ
--          ≡⟨ dist-subst (_⋯ᵣ wknᵣ) ((sym (id/m→M/id _))) (wk-telescope Γ₁ x ⋯ ϕ) ⟩
--            subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ ⋯ᵣ wknᵣ)
--          ≡⟨ cong (subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _))) (sym (dist-↑-f (wk-telescope Γ₁ x) ϕ)) ⟩
--            subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ ϕ ↑ _)
--          ≡⟨⟩
--            subst (µ₂ ▷ _ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ ϕ ↑ _)
--          ∎
--         )
--       (∋wk/⊢wk _ _ _ _ (⊢ϕ x _ refl) )

--   _,*_ : ∀ {m} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {e : µ₂ ∋/⊢ id/m→M m} {t : µ₁ ∶⊢ m→M m} →
--     Γ₂ ∋*/⊢* ϕ ∶ Γ₁ →
--     Γ₂ ∋/⊢   e ∶ subst (_ ∶⊢_) (sym (id/m→M/id m)) t ⋯ ϕ →
--     Γ₂ ∋*/⊢* ϕ ,ₖ e ∶ Γ₁ ▶ t
--   _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (here refl) _ refl =
--     Γ₂ ∋/⊢ (here refl & ϕ ,ₖ e) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
--     by subst₂ (Γ₂ ∋/⊢_∶_) (sym (&-,ₖ-here ϕ e)) (
--       begin
--         subst (µ₁ ∶⊢_) (sym (id/m→M/id _)) t ⋯ ϕ
--       ≡⟨ sym (wk-cancels-,ₖ (subst (_ ∶⊢_) (sym (id/m→M/id _)) t) ϕ e) ⟩
--         (subst (µ₁ ∶⊢_) (sym (id/m→M/id _)) t) ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)
--       ≡⟨ dist-subst (λ ■ → ■ ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)) (sym (id/m→M/id _)) t ⟩
--         subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (t ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e))
--       ≡⟨⟩
--         subst (µ₂ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (here refl) ⋯ (ϕ ,ₖ e))
--       ∎
--     ) ⊢e
--   _,*_ {µ₁ = µ₁} {µ₂ = µ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} {e = e} {t = t} ⊢ϕ ⊢e (there x) _ eq@refl =
--     Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope (Γ₁ ▶ t) (there x) ⋯ (ϕ ,ₖ e)) by (
--     Γ₂ ∋/⊢ (there x & ϕ ,ₖ e) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e)) by
--     subst₂ (λ ■₁ ■₂ → Γ₂ ∋/⊢ ■₁ ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) ■₂)
--       (sym (&-,ₖ-there ϕ e x))
--       (wk-telescope Γ₁ x ⋯ ϕ                ≡⟨ sym (wk-cancels-,ₖ (wk-telescope Γ₁ x) ϕ e) ⟩
--        wk-telescope Γ₁ x ⋯ᵣ wknᵣ ⋯ (ϕ ,ₖ e) ∎)
--     (Γ₂ ∋/⊢ x & ϕ ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (wk-telescope Γ₁ x ⋯ ϕ) by ⊢ϕ x _ refl ))

--   ⊢id : ∀ {µ} {Γ : Ctx µ} → Γ ∋*/⊢* id ∶ Γ
--   ⊢id {Γ = Γ} x _ refl =
--     Γ ∋/⊢ x & id ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ x ⋯ id)
--       by subst₂ (λ ■₁ ■₂ → Γ ∋/⊢ ■₁ ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) ■₂)
--          (sym (&-id x))
--          (sym (⋯-id (wk-telescope Γ x)))
--          (
--     Γ ∋/⊢ id/` x ∶ subst (_ ∶⊢_) (sym (id/m→M/id _)) (wk-telescope Γ x)
--       by ∋/⊢∶-lookup x)

--   ⊢*~ :
--     ∀ {µ₁} {µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂} 
--     → ϕ ~ ϕ'
--     → Γ₂ ∋*/⊢* ϕ ∶ Γ₁
--     → Γ₂ ∋*/⊢* ϕ' ∶ Γ₁
--   ⊢*~ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {ϕ'} ϕ~ϕ' ⊢ϕ {m₁} x t ⊢x =
--     Γ₂ ∋/⊢ (x & ϕ') ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (t ⋯ ϕ')
--       by subst₂
--            (λ ■₁ ■₂ → Γ₂ ∋/⊢ ■₁ ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) ■₂)
--            (`/id-injective (ϕ~ϕ' _ x))
--            (~-cong-⋯ t ϕ~ϕ') (
--     Γ₂ ∋/⊢ (x & ϕ ) ∶ subst (_∶⊢_ µ₂) (sym (id/m→M/id _)) (t ⋯ ϕ )
--       by ⊢ϕ x t ⊢x)

--   ⊢⦅_⦆ : ∀ {m} {Γ : Ctx µ} {t : µ ∋/⊢ id/m→M m} {T : µ ∶⊢ m→M/id (id/m→M m)}
--     → Γ ∋/⊢ t ∶ T 
--     → Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
--   ⊢⦅_⦆ {µ} {m} {Γ} {t} {T} ⊢t =
--     let ⊢t' = subst (Γ ∋/⊢ t ∶_) (sym (
--                 begin
--                   subst
--                     (µ ∶⊢_)
--                     (sym (id/m→M/id _))
--                     (subst (µ ∶⊢_) (id/m→M/id _) T)
--                   ⋯ id
--                 ≡⟨ cong (_⋯ id) (cancel-subst (µ ∶⊢_) (id/m→M/id _) T) ⟩
--                   T ⋯ id
--                 ≡⟨ ⋯-id T ⟩
--                   T
--                 ∎
--               )) ⊢t in
--     Γ ∋*/⊢* ⦅ t ⦆ ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
--       by ⊢*~ (~-sym (⦅⦆-,ₖ t)) (
--     Γ ∋*/⊢* (id ,ₖ t) ∶ Γ ▶ subst (µ ∶⊢_) (id/m→M/id m) T
--       by (⊢id ,* ⊢t')
--     )

-- open ISemKit ⦃ ... ⦄

-- infixl  5  _∋*/⊢*[_]_∶_
-- _∋*/⊢*[_]_∶_ :
--   ∀ {𝕂} {K : KitT 𝕂} {C₁ : ComposeKit 𝕂 kitᵣ 𝕂} {C₂ : ComposeKit 𝕂 𝕂 𝕂}
--   → Ctx µ₂ → ISemKit 𝕂 K C₁ C₂ → µ₁ –[ 𝕂 ]→ µ₂ → Ctx µ₁ → Set
-- Γ₂ ∋*/⊢*[ IK ] f ∶ Γ₁ = Γ₂ ∋*/⊢* f ∶ Γ₁ where instance _ = IK

-- open Kit ⦃ ... ⦄
-- open ComposeKit ⦃ ... ⦄

-- private instance _ = kitᵣ
-- private instance _ = kitₛ
-- private instance _ = kittᵣ
-- private instance _ = kittₛ
-- private instance _ = ckitᵣ
-- private instance _ = ckitₛᵣ
-- private instance _ = ckitₛₛ

-- record ITraversal : Set (lsuc ℓ) where
--   infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_

--   field
--     -- Substitution/Renaming preserves typing
--     _⊢⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
--              ⦃ IK : ISemKit 𝕂 K C₁ C₂ ⦄
--              ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
--              ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
--              {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
--            Γ₁ ⊢ e ∶ t →
--            Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
--            Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ

--     -- ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
--     --         (` x) ⋯ f ≡ subst (µ₂ ⊢_) (id/m→M/id m) (tm _ (f _ x))

--   instance
--     ikitᵣ : ISemKit kitᵣ kittᵣ ckitᵣ ckitᵣ
--     IKit._∋/⊢_∶_ ikitᵣ = _∋_∶_
--     IKit.∋/⊢∶-lookup ikitᵣ = λ _ → refl
--     IKit.id/⊢`   ikitᵣ = λ ⊢x → ⊢x
--     IKit.⊢`/id   ikitᵣ = ⊢`
--     IKit.⊢`/id'  ikitᵣ = ⊢`
--     IKit.∋wk/⊢wk ikitᵣ _ _ _ _ refl = refl

--     ikitₛ : IKit kitₛ kittₛ ckitₛᵣ ckitₛₛ
--     IKit._∋/⊢_∶_ ikitₛ = _⊢_∶_
--     IKit.∋/⊢∶-lookup ikitₛ = λ _ → ⊢` refl
--     IKit.id/⊢`   ikitₛ = ⊢`
--     IKit.⊢`/id   ikitₛ = λ ⊢t → ⊢t
--     IKit.⊢`/id'  ikitₛ = λ ⊢t → ⊢t
--     IKit.∋wk/⊢wk ikitₛ Γ t' x t ⊢e = ⊢e ⊢⋯ λ x₁ t₁ ⊢x₁ →
--       (Γ ▶ t') ∋ (x₁ & wknᵣ) ∶ (t₁ ⋯ wknᵣ)
--         by subst (λ ■ → (Γ ▶ t') ∋ ■ ∶ (t₁ ⋯ wknᵣ))
--                 (sym (trans (&-wkₖ-wk id x₁) (cong there (&-id x₁)))) (
--       (Γ ▶ t') ∋ (there x₁) ∶ (t₁ ⋯ wknᵣ)
--         by (∋wk/⊢wk Γ t' x₁ t₁ ⊢x₁))

--   open IKit ikitᵣ public using () renaming (∋wk/⊢wk to ⊢wk; _∋↑/⊢↑_ to _∋↑_; _,*_ to _,*ᵣ_; ⊢id to ⊢idᵣ; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
--   open IKit ikitₛ public using () renaming (∋wk/⊢wk to ∋wk; _∋↑/⊢↑_ to _⊢↑_; _,*_ to _,*ₛ_; ⊢id to ⊢idₛ; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

--   -- Renaming preserves typing

--   _⊢⋯ᵣ_ : ∀ {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ρ : µ₁ →ᵣ µ₂} →
--           Γ₁ ⊢ e ∶ t →
--           Γ₂ ∋* ρ ∶ Γ₁ →
--           Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
--   _⊢⋯ᵣ_ = _⊢⋯_

--   -- Substitution preserves typing

--   _⊢⋯ₛ_ : ∀ {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {σ : µ₁ →ₛ µ₂} →
--           Γ₁ ⊢ e ∶ t →
--           Γ₂ ⊢* σ ∶ Γ₁ →
--           Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
--   _⊢⋯ₛ_ = _⊢⋯_

