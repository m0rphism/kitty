module Kitty.Examples.LambdaPi-Derive.Confluence where

open import Data.Product using (∃-syntax; _×_ ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using () renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; module ≡-Reasoning)

open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Util.Closures
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open TypingKit ⦃ … ⦄

↪*-trans : e₁ ↪* e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
↪*-trans ↪*-refl         q = q
↪*-trans (↪*-step p₁ p₂) q = ↪*-step p₁ (↪*-trans p₂ q)

↪*-map :
  {f : S ⊢ 𝕖 → S' ⊢ 𝕖} →
  (F : ∀ {e₁ e₂ : S ⊢ 𝕖} → e₁ ↪ e₂ → f e₁ ↪ f e₂) →
  e₁ ↪* e₂ →
  f e₁ ↪* f e₂
↪*-map F ↪*-refl = ↪*-refl
↪*-map F (↪*-step p q) = ↪*-step (F p) (↪*-map F q)

module ↪*-Reasoning where
  infix 1 begin_
  infixr 2 _↪⟨_⟩_ _↪*⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {e₁ e₂ : S ⊢ 𝕖} → e₁ ↪* e₂ → e₁ ↪* e₂
  begin p = p

  _↪⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ 𝕖) → e₁ ↪ e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ↪⟨ p ⟩ q = ↪*-step p q

  _↪*⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ 𝕖) → e₁ ↪* e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ↪*⟨ p ⟩ q = ↪*-trans p q

  _≡⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ 𝕖) → e₁ ≡ e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ 𝕖) → e₁ ↪* e₂ → e₁ ↪* e₂
  _ ≡⟨⟩ q = q

  _∎ : ∀ (e : S ⊢ 𝕖) → e ↪* e
  _ ∎ = ↪*-refl

infix   3  _↪ₚ_
data _↪ₚ_ : S ⊢ s → S ⊢ s → Set where

  -- Variables

  ξ-` : ∀ {x : S ∋ s} →
    ` x ↪ₚ ` x

  -- Pi Types

  β-λ : ∀ {e₁ e₁' : (S ▷ 𝕖) ⊢ 𝕖} {e₂ e₂' : S ⊢ 𝕖} →
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    (λx e₁) · e₂ ↪ₚ e₁' ⋯ ⦅ e₂' ⦆ₛ

  ξ-∀ :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ₚ ∀[x∶ t₁' ] t₂'

  ξ-λ :
    e ↪ₚ e' →
    λx e ↪ₚ λx e'

  ξ-· :
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    e₁ · e₂ ↪ₚ e₁' · e₂'

  -- Sigma Types

  β-proj₁ :
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    `proj₁ (e₁ `, e₂) ↪ₚ e₁'
  β-proj₂ :
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    `proj₂ (e₁ `, e₂) ↪ₚ e₂'
  ξ-∃ :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    ∃[x∶ t₁ ] t₂ ↪ₚ ∃[x∶ t₁' ] t₂'
  ξ-, :
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    e₁ `, e₂ ↪ₚ e₁' `, e₂'
  ξ-proj₁ :
    e ↪ₚ e' →
    `proj₁ e ↪ₚ `proj₁ e'
  ξ-proj₂ :
    e ↪ₚ e' →
    `proj₂ e ↪ₚ `proj₂ e'

  -- Equality Types

  β-J :
    e ↪ₚ e' →
    `J t `refl e ↪ₚ e'
  ξ-≡ :
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    (e₁ `≡ e₂) ↪ₚ (e₁' `≡ e₂')
  ξ-refl :
    `refl {S = S} ↪ₚ `refl
  ξ-J :
    t ↪ₚ t' →
    e₁ ↪ₚ e₁' →
    e₂ ↪ₚ e₂' →
    `J t e₁ e₂ ↪ₚ `J t' e₁' e₂'

  -- Universe Type

  ξ-Set :
    `Set ↪ₚ (`Set {S = S})

↪ₚ-refl : t ↪ₚ t
↪ₚ-refl {t = ` x}          = ξ-`
↪ₚ-refl {t = ∀[x∶ t₁ ] t₂} = ξ-∀ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = λx t}         = ξ-λ ↪ₚ-refl
↪ₚ-refl {t = t₁ · t₂}      = ξ-· ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = ∃[x∶ t₁ ] t₂} = ξ-∃ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = t₁ `, t₂}     = ξ-, ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = `proj₁ t}     = ξ-proj₁ ↪ₚ-refl
↪ₚ-refl {t = `proj₂ t}     = ξ-proj₂ ↪ₚ-refl
↪ₚ-refl {t = e₁ `≡ e₂}     = ξ-≡ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = `refl}        = ξ-refl
↪ₚ-refl {t = `J t e₁ e₂}   = ξ-J ↪ₚ-refl ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = `Set}         = ξ-Set

data _↪ₚ*_ : S ⊢ s → S ⊢ s → Set where
  ↪ₚ*-refl : e ↪ₚ* e
  ↪ₚ*-step : e₁ ↪ₚ e₂ → e₂ ↪ₚ* e₃ → e₁ ↪ₚ* e₃

↪ₚ*-trans : e₁ ↪ₚ* e₂ → e₂ ↪ₚ* e₃ → e₁ ↪ₚ* e₃
↪ₚ*-trans ↪ₚ*-refl         q = q
↪ₚ*-trans (↪ₚ*-step p₁ p₂) q = ↪ₚ*-step p₁ (↪ₚ*-trans p₂ q)

↪ₚ*-map :
  {f : S ⊢ 𝕖 → S' ⊢ 𝕖} →
  (F : ∀ {e₁ e₂ : S ⊢ 𝕖} → e₁ ↪ₚ e₂ → f e₁ ↪ₚ f e₂) →
  e₁ ↪ₚ* e₂ →
  f e₁ ↪ₚ* f e₂
↪ₚ*-map F ↪ₚ*-refl = ↪ₚ*-refl
↪ₚ*-map F (↪ₚ*-step p q) = ↪ₚ*-step (F p) (↪ₚ*-map F q)

↪→↪ₚ : t ↪ t' → t ↪ₚ t'
↪→↪ₚ β-λ            = β-λ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-λ t↪t')     = ξ-λ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-∀₁ t₁↪t₁')  = ξ-∀ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ t₂↪t₂')  = ξ-∀ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-·₁ t₁↪t₁')  = ξ-· (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ t₂↪t₂')  = ξ-· ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ β-proj₁        = β-proj₁ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ β-proj₂        = β-proj₂ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-∃₁ t↪t')    = ξ-∃ (↪→↪ₚ t↪t') ↪ₚ-refl
↪→↪ₚ (ξ-∃₂ t↪t')    = ξ-∃ ↪ₚ-refl (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-proj₁ t↪t') = ξ-proj₁ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-proj₂ t↪t') = ξ-proj₂ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-,₁ t↪t')    = ξ-, (↪→↪ₚ t↪t') ↪ₚ-refl
↪→↪ₚ (ξ-,₂ t↪t')    = ξ-, ↪ₚ-refl (↪→↪ₚ t↪t')
↪→↪ₚ β-J            = β-J ↪ₚ-refl
↪→↪ₚ (ξ-≡₁ t↪t')    = ξ-≡ (↪→↪ₚ t↪t') ↪ₚ-refl
↪→↪ₚ (ξ-≡₂ t↪t')    = ξ-≡ ↪ₚ-refl (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-J₁ t↪t')    = ξ-J (↪→↪ₚ t↪t') ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-J₂ t↪t')    = ξ-J ↪ₚ-refl (↪→↪ₚ t↪t') ↪ₚ-refl
↪→↪ₚ (ξ-J₃ t↪t')    = ξ-J ↪ₚ-refl ↪ₚ-refl (↪→↪ₚ t↪t')

↪*→↪ₚ* : t ↪* t' → t ↪ₚ* t'
↪*→↪ₚ* ↪*-refl                = ↪ₚ*-refl
↪*→↪ₚ* (↪*-step t↪t' t'↪*t'') = ↪ₚ*-step (↪→↪ₚ t↪t') (↪*→↪ₚ* t'↪*t'')

↪ₚ→↪* :
  t ↪ₚ t' →
  t ↪* t'
↪ₚ→↪* ξ-`                    = ↪*-refl
↪ₚ→↪* (β-λ {e₁ = e₁} {e₁'} {e₂} {e₂'} e₁↪ₚe₁' e₂↪ₚe₂'') =
  let open ↪*-Reasoning in
  begin
    (λx e₁) · e₂
  ↪*⟨ ↪*-map ξ-·₁ (↪*-map ξ-λ (↪ₚ→↪* e₁↪ₚe₁')) ⟩
    (λx e₁') · e₂
  ↪*⟨ ↪*-map ξ-·₂ (↪ₚ→↪* e₂↪ₚe₂'') ⟩
    (λx e₁') · e₂'
  ↪⟨ β-λ ⟩
    e₁' ⋯ₛ ⦅ e₂' ⦆ₛ
  ∎
↪ₚ→↪* (ξ-λ t↪ₚt')            = ↪*-map ξ-λ (↪ₚ→↪* t↪ₚt')
↪ₚ→↪* (ξ-∀ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  let open ↪*-Reasoning in
  begin
    ∀[x∶ t₁  ] t₂
  ↪*⟨ ↪*-map ξ-∀₁ (↪ₚ→↪* t₁↪ₚt₁') ⟩
    ∀[x∶ t₁' ] t₂
  ↪*⟨ ↪*-map ξ-∀₂ (↪ₚ→↪* t₂↪ₚt₂') ⟩
    ∀[x∶ t₁' ] t₂'
  ∎
↪ₚ→↪* (ξ-· {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  let open ↪*-Reasoning in
  begin
    e₁  · e₂
  ↪*⟨ ↪*-map ξ-·₁ (↪ₚ→↪* t₁↪ₚt₁') ⟩
    e₁' · e₂
  ↪*⟨ ↪*-map ξ-·₂ (↪ₚ→↪* t₂↪ₚt₂') ⟩
    e₁' · e₂'
  ∎
↪ₚ→↪* ξ-Set                     = ↪*-refl
↪ₚ→↪* (β-proj₁ {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂') = 
  let open ↪*-Reasoning in
  begin
    `proj₁ (e₁ `, e₂)
  ↪*⟨ ↪*-map ξ-proj₁ (↪*-map ξ-,₁ (↪ₚ→↪* e₁↪ₚe₁')) ⟩
    `proj₁ (e₁' `, e₂)
  ↪*⟨ ↪*-map ξ-proj₁ (↪*-map ξ-,₂ (↪ₚ→↪* e₂↪ₚe₂')) ⟩
    `proj₁ (e₁' `, e₂')
  ↪⟨ β-proj₁ ⟩
    e₁'
  ∎
↪ₚ→↪* (β-proj₂ {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂') =
  let open ↪*-Reasoning in
  begin
    `proj₂ (e₁ `, e₂)
  ↪*⟨ ↪*-map ξ-proj₂ (↪*-map ξ-,₁ (↪ₚ→↪* e₁↪ₚe₁')) ⟩
    `proj₂ (e₁' `, e₂)
  ↪*⟨ ↪*-map ξ-proj₂ (↪*-map ξ-,₂ (↪ₚ→↪* e₂↪ₚe₂')) ⟩
    `proj₂ (e₁' `, e₂')
  ↪⟨ β-proj₂ ⟩
    e₂'
  ∎
↪ₚ→↪* (β-J {e = e} {e' = e'} {t = t} e↪ₚe') =
  let open ↪*-Reasoning in
  begin
    `J t `refl e
  ↪*⟨ ↪*-map ξ-J₃ (↪ₚ→↪* e↪ₚe') ⟩
    `J t `refl e'
  ↪⟨ β-J ⟩
    e'
  ∎
↪ₚ→↪* (ξ-∃ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  let open ↪*-Reasoning in
  begin
    ∃[x∶ t₁  ] t₂
  ↪*⟨ ↪*-map ξ-∃₁ (↪ₚ→↪* t₁↪ₚt₁') ⟩
    ∃[x∶ t₁' ] t₂
  ↪*⟨ ↪*-map ξ-∃₂ (↪ₚ→↪* t₂↪ₚt₂') ⟩
    ∃[x∶ t₁' ] t₂'
  ∎
↪ₚ→↪* (ξ-, {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂')     =
  let open ↪*-Reasoning in
  begin
    e₁  `, e₂
  ↪*⟨ ↪*-map ξ-,₁ (↪ₚ→↪* e₁↪ₚe₁') ⟩
    e₁' `, e₂
  ↪*⟨ ↪*-map ξ-,₂ (↪ₚ→↪* e₂↪ₚe₂') ⟩
    e₁' `, e₂'
  ∎
↪ₚ→↪* (ξ-proj₁ e↪ₚe')           = ↪*-map ξ-proj₁ (↪ₚ→↪* e↪ₚe')
↪ₚ→↪* (ξ-proj₂ e↪ₚe')           = ↪*-map ξ-proj₂ (↪ₚ→↪* e↪ₚe')
↪ₚ→↪* (ξ-≡ {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂')     =
  let open ↪*-Reasoning in
  begin
    e₁  `≡ e₂
  ↪*⟨ ↪*-map ξ-≡₁ (↪ₚ→↪* e₁↪ₚe₁') ⟩
    e₁' `≡ e₂
  ↪*⟨ ↪*-map ξ-≡₂ (↪ₚ→↪* e₂↪ₚe₂') ⟩
    e₁' `≡ e₂'
  ∎
↪ₚ→↪* ξ-refl                    = ↪*-refl
↪ₚ→↪* (ξ-J {t = t} {t' = t'} {e₁ = e₁} {e₁' = e₁'} {e₂ = e₂} {e₂' = e₂'} t↪ₚt' e₁↪ₚe₁' e₂↪ₚe₂')  =
  let open ↪*-Reasoning in
  begin
    `J t e₁ e₂
  ↪*⟨ ↪*-map ξ-J₁ (↪ₚ→↪* t↪ₚt') ⟩
    `J t' e₁ e₂
  ↪*⟨ ↪*-map ξ-J₂ (↪ₚ→↪* e₁↪ₚe₁') ⟩
    `J t' e₁' e₂
  ↪*⟨ ↪*-map ξ-J₃ (↪ₚ→↪* e₂↪ₚe₂') ⟩
    `J t' e₁' e₂'
  ∎

↪ₚ*→↪* : ∀ {t t' : S ⊢ 𝕖}
  → t ↪ₚ* t'
  → t ↪* t'
↪ₚ*→↪* ↪ₚ*-refl                  = ↪*-refl
↪ₚ*→↪* (↪ₚ*-step t↪ₚt' t'↪ₚ*t'') = ↪*-trans (↪ₚ→↪* t↪ₚt') (↪ₚ*→↪* t'↪ₚ*t'')

open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (SortTy; Var; NoVar)

private variable
  _∋/⊢_ : List (Sort Var) → Sort Var → Set

↪ₚ-⋯ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ 𝕖} →
  e ↪ₚ e' →
  e ⋯ ϕ ↪ₚ e' ⋯ ϕ
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ ξ-`                         = ↪ₚ-refl
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ {ϕ = ϕ} (β-λ {e₁ = e₁} {e₁'} {e₂} {e₂'} e₁↪ₚe₁' e₂↪ₚe₂')
                                             = subst (((λx e₁) · e₂) ⋯ ϕ ↪ₚ_)
                                                     (sym (dist-⦅⦆ₛ-⋯ ⦃ C₁ = C₂ ⦄ e₁' e₂' ϕ))
                                                     (β-λ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁')
                                                          (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂'))
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂')       = ξ-∀ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t₁↪ₚt₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t₂↪ₚt₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-λ t↪ₚt')                 = ξ-λ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t↪ₚt')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-· e₁↪ₚe₁' e₂↪ₚe₂')       = ξ-· (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (β-proj₁ e₁↪ₚe₁' e₂↪ₚe₂')   = β-proj₁ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (β-proj₂ e₁↪ₚe₁' e₂↪ₚe₂')   = β-proj₂ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-∃ t₁↪ₚt₁' t₂↪ₚt₂')       = ξ-∃ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t₁↪ₚt₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t₂↪ₚt₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-, e₁↪ₚe₁' e₂↪ₚe₂')       = ξ-, (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-proj₁ e↪ₚe')             = ξ-proj₁ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e↪ₚe')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-proj₂ e↪ₚe')             = ξ-proj₂ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e↪ₚe')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (β-J e↪ₚe')                 = β-J (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e↪ₚe')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-≡ e₁↪ₚe₁' e₂↪ₚe₂')       = ξ-≡ (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁') (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ ξ-refl                      = ξ-refl
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (ξ-J t↪ₚt' e₁↪ₚe₁' e₂↪ₚe₂') = ξ-J (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ t↪ₚt')
                                                    (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₁↪ₚe₁')
                                                    (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ e₂↪ₚe₂')
↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ ξ-Set                       = ξ-Set

↪ₚ-⋯ₛ : ∀ {σ : S₁ →ₛ S₂} →
  e ↪ₚ e' →
  e ⋯ₛ σ ↪ₚ e' ⋯ₛ σ
↪ₚ-⋯ₛ = ↪ₚ-⋯

↪ₚ-⋯ᵣ : ∀ {ρ : S₁ →ᵣ S₂} →
  e ↪ₚ e' →
  e ⋯ᵣ ρ ↪ₚ e' ⋯ᵣ ρ
↪ₚ-⋯ᵣ = ↪ₚ-⋯

_↪ₚσ_ : ∀ (σ₁ σ₂ : S₁ →ₛ S₂) → Set
σ₁ ↪ₚσ σ₂ = ∀ {s} (x : _ ∋ s) → σ₁ _ x ↪ₚ σ₂ _ x

↪ₚσ-refl : ∀ {σ : S₁ →ₛ S₂} →
  σ ↪ₚσ σ
↪ₚσ-refl {s = 𝕖} x = ↪ₚ-refl

↪ₚσ-ext : ∀ {σ₁ σ₂ : S₁ →ₛ S₂} {e₁ e₂ : S₂ ⊢ s} →
  σ₁ ↪ₚσ σ₂ →
  e₁ ↪ₚ e₂ →
  (σ₁ ,ₛ e₁) ↪ₚσ (σ₂ ,ₛ e₂)
↪ₚσ-ext σ₁↪σ₂ e₁↪e₂ (here refl) = e₁↪e₂
↪ₚσ-ext σ₁↪σ₂ e₁↪e₂ (there x)   = σ₁↪σ₂ x

↪ₚσ-wk : ∀ {σ₁ σ₂ : S₁ →ₛ S₂} →
  σ₁ ↪ₚσ σ₂ →
  wk→ₛ s σ₁ ↪ₚσ wk→ₛ s σ₂
↪ₚσ-wk {s = 𝕖} σ₁↪σ₂ x = ↪ₚ-⋯ᵣ (σ₁↪σ₂ x)

-- ↪ₚσ-↑ : ∀ {S₁ S₂} {σ₁ σ₂ : S₁ →ₛ S₂} {m'} →
--   σ₁ ↪ₚσ σ₂ →
--   (σ₁ ↑ₛ m') ↪ₚσ (σ₂ ↑ₛ m')
-- ↪ₚσ-↑ {m' = 𝕖} σ₁↪σ₂ = ↪ₚσ-ext (↪ₚσ-wk σ₁↪σ₂) ↪ₚ-refl

-- -- ↪σ-⋯ : ∀ {S₁ S₂ m} {σ σ' : S₁ →ₛ S₂} (t : S₁ ⊢ m) →
-- --   σ ↪ₚσ σ' →
-- --   t ⋯ σ ↪ₚ t ⋯ σ'
-- -- ↪σ-⋯ (` x)          σ↪σ' = σ↪σ' x
-- -- ↪σ-⋯ (λx t)         σ↪σ' = ξ-λ (↪σ-⋯ t (↪ₚσ-↑ σ↪σ'))
-- -- ↪σ-⋯ (∀[x∶ t₁ ] t₂) σ↪σ' = ξ-∀ (↪σ-⋯ t₁ σ↪σ') (↪σ-⋯ t₂ (↪ₚσ-↑ σ↪σ'))
-- -- ↪σ-⋯ (t₁ · t₂)      σ↪σ' = ξ-· (↪σ-⋯ t₁ σ↪σ') (↪σ-⋯ t₂ σ↪σ')
-- -- ↪σ-⋯ `Set              σ↪σ' = ξ-`Set

-- ↪ₚσ-⋯ : ∀ {S₁ S₂ m} {t t' : S₁ ⊢ m} {σ σ' : S₁ →ₛ S₂} →
--   t ↪ₚ t' →
--   σ ↪ₚσ σ' →
--   t ⋯ σ ↪ₚ t' ⋯ σ'
-- ↪ₚσ-⋯ ξ-`                   σ↪σ' = σ↪σ' _
-- ↪ₚσ-⋯ {σ = σ} {σ'} (β-λ {t₁' = t₁'} {t₂' = t₂'} t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ₛ t₁' t₂' σ'))
--                                                                               (β-λ (↪ₚσ-⋯ t₁↪ₚt₁' (↪ₚσ-↑ σ↪σ'))
--                                                                                    (↪ₚσ-⋯ t₂↪ₚt₂' σ↪σ'))
-- ↪ₚσ-⋯ (ξ-λ t↪ₚt')           σ↪σ' = ξ-λ (↪ₚσ-⋯ t↪ₚt' (↪ₚσ-↑ σ↪σ'))
-- ↪ₚσ-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = ξ-∀ (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' (↪ₚσ-↑ σ↪σ'))
-- ↪ₚσ-⋯ (ξ-· t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = ξ-· (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' σ↪σ')
-- ↪ₚσ-⋯ ξ-`Set                   σ↪σ' = ξ-`Set

-- ↪ₚσ-⦅_⦆ : ∀ {S m} {t₁ t₂ : S ⊢ m→M m} →
--   t₁ ↪ₚ t₂ →
--   ⦅ t₁ ⦆ ↪ₚσ ⦅ t₂ ⦆
-- ↪ₚσ-⦅ t₁↪ₚt₂ ⦆ = ↪ₚσ-ext (↪ₚσ-refl {σ = idₛ}) t₁↪ₚt₂ 

-- ↪ₚσ-⋯-⦅⦆ : ∀ {S M} {t₁ t₁' : (S ▷ 𝕖) ⊢ M}  {t₂ t₂' : S ⊢ 𝕖} →
--   t₁ ↪ₚ t₁' →
--   t₂ ↪ₚ t₂' →
--   t₁ ⋯ ⦅ t₂ ⦆ₛ ↪ₚ t₁' ⋯ ⦅ t₂' ⦆ₛ
-- ↪ₚσ-⋯-⦅⦆ t₁↪ₚt₁' t₂↪ₚt₂' = ↪ₚσ-⋯ t₁↪ₚt₁' ↪ₚσ-⦅ t₂↪ₚt₂' ⦆

-- diamond :
--   t ↪ₚ t₁ →
--   t ↪ₚ t₂ →
--   ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
-- diamond ξ-`             ξ-`               = _ , ξ-` , ξ-`
-- diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
--   with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ ↪ₚσ-⦅ t₂'↪T₂ ⦆ , ↪ₚσ-⋯ t₁''↪T₁ ↪ₚσ-⦅ t₂''↪T₂ ⦆
-- diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (ξ-· (ξ-λ t₁↪t₁'') t₂↪t₂'')
--   with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ ↪ₚσ-⦅ t₂'↪T₂ ⦆ , (β-λ t₁''↪T₁ t₂''↪T₂)
-- diamond (ξ-λ t↪t') (ξ-λ t↪t'')
--   with diamond t↪t' t↪t''
-- ...  | T , t'↪T , t''↪T
--   = λx T , ξ-λ t'↪T , ξ-λ t''↪T
-- diamond (ξ-∀ t₁↪t₁' t₂↪t₂') (ξ-∀ t₁↪t₁'' t₂↪t₂'')
--   with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = ∀[x∶ T₁ ] T₂ , ξ-∀ t₁'↪T₁ t₂'↪T₂ , ξ-∀ t₁''↪T₁ t₂''↪T₂
-- diamond (ξ-· (ξ-λ t₁↪t₁') t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
--   with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , β-λ t₁'↪T₁ t₂'↪T₂ , ↪ₚσ-⋯ t₁''↪T₁ ↪ₚσ-⦅ t₂''↪T₂ ⦆
-- diamond (ξ-· t₁↪t₁' t₂↪t₂') (ξ-· t₁↪t₁'' t₂↪t₂'')
--   with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ · T₂ , ξ-· t₁'↪T₁ t₂'↪T₂ , ξ-· t₁''↪T₁ t₂''↪T₂
-- diamond ξ-`Set ξ-`Set = `Set , ξ-`Set , ξ-`Set

-- strip :
--   t ↪ₚ t₁ →
--   t ↪ₚ* t₂ →
--   ∃[ t' ] (t₁ ↪ₚ* t') × (t₂ ↪ₚ t')
-- strip {t = t} {t₁} {t₂} t↪ₚt₁ refl = t₁ , refl , t↪ₚt₁
-- strip {t = t} {t₁} {t₂} t↪ₚt₁ (step t↪ₚt₂' t₂'↪ₚ*t₂)
--   with diamond t↪ₚt₁ t↪ₚt₂'
-- ... | T , t₁↪ₚT , t₂'↪ₚT
--   with strip t₂'↪ₚT t₂'↪ₚ*t₂
-- ... | U , T↪ₚ*U , t₂↪U
--   = U , step t₁↪ₚT T↪ₚ*U , t₂↪U

-- confluenceₚ : 
--   t ↪ₚ* t₁ →
--   t ↪ₚ* t₂ →
--   ∃[ t' ] (t₁ ↪ₚ* t') × (t₂ ↪ₚ* t')
-- confluenceₚ refl                   t↪ₚ*t₂ = _ , t↪ₚ*t₂ , refl
-- confluenceₚ (step t↪ₚt₁' t₁'↪ₚ*t₁) t↪ₚ*t₂
--   with strip t↪ₚt₁' t↪ₚ*t₂
-- ... | T , t₁'↪ₚ*T , t₂↪ₚT
--   with confluenceₚ t₁'↪ₚ*t₁ t₁'↪ₚ*T
-- ... | U , t₁↪ₚ*U , T↪ₚ*U
--   = U , t₁↪ₚ*U , step t₂↪ₚT T↪ₚ*U 

-- confluence : 
--   t ↪* t₁ →
--   t ↪* t₂ →
--   ∃[ t' ] (t₁ ↪* t') × (t₂ ↪* t')
-- confluence t↪*t₁ t↪*t₂
--   with confluenceₚ (↪*→↪ₚ* t↪*t₁) (↪*→↪ₚ* t↪*t₂)
-- ... | t' , t₁↪ₚ*t' , t₂↪ₚ*t'
--   = t' , ↪ₚ*→↪* t₁↪ₚ*t' , ↪ₚ*→↪* t₂↪ₚ*t'
