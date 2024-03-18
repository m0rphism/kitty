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
  {f : S ⊢ s → S' ⊢ s} →
  (F : ∀ {e₁ e₂ : S ⊢ s} → e₁ ↪ e₂ → f e₁ ↪ f e₂) →
  e₁ ↪* e₂ →
  f e₁ ↪* f e₂
↪*-map F ↪*-refl = ↪*-refl
↪*-map F (↪*-step p q) = ↪*-step (F p) (↪*-map F q)

module ↪*-Reasoning where
  infix 1 begin_
  infixr 2 _↪⟨_⟩_ _↪*⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {e₁ e₂ : S ⊢ s} → e₁ ↪* e₂ → e₁ ↪* e₂
  begin p = p

  _↪⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ s) → e₁ ↪ e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ↪⟨ p ⟩ q = ↪*-step p q

  _↪*⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ s) → e₁ ↪* e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ↪*⟨ p ⟩ q = ↪*-trans p q

  _≡⟨_⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ s) → e₁ ≡ e₂ → e₂ ↪* e₃ → e₁ ↪* e₃
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (e₁ {e₂} {e₃} : S ⊢ s) → e₁ ↪* e₂ → e₁ ↪* e₂
  _ ≡⟨⟩ q = q

  _∎ : ∀ (e : S ⊢ s) → e ↪* e
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

↪ₚ-refl : e ↪ₚ e
↪ₚ-refl {e = ` x}          = ξ-`
↪ₚ-refl {e = ∀[x∶ e₁ ] e₂} = ξ-∀ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = λx e}         = ξ-λ ↪ₚ-refl
↪ₚ-refl {e = e₁ · e₂}      = ξ-· ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = ∃[x∶ e₁ ] e₂} = ξ-∃ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = e₁ `, e₂}     = ξ-, ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = `proj₁ e}     = ξ-proj₁ ↪ₚ-refl
↪ₚ-refl {e = `proj₂ e}     = ξ-proj₂ ↪ₚ-refl
↪ₚ-refl {e = e₁ `≡ e₂}     = ξ-≡ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = `refl}        = ξ-refl
↪ₚ-refl {e = `J e e₁ e₂}   = ξ-J ↪ₚ-refl ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {e = `Set}         = ξ-Set

data _↪ₚ*_ : S ⊢ s → S ⊢ s → Set where
  ↪ₚ*-refl : e ↪ₚ* e
  ↪ₚ*-step : e₁ ↪ₚ e₂ → e₂ ↪ₚ* e₃ → e₁ ↪ₚ* e₃

↪ₚ*-trans : e₁ ↪ₚ* e₂ → e₂ ↪ₚ* e₃ → e₁ ↪ₚ* e₃
↪ₚ*-trans ↪ₚ*-refl         q = q
↪ₚ*-trans (↪ₚ*-step p₁ p₂) q = ↪ₚ*-step p₁ (↪ₚ*-trans p₂ q)

↪ₚ*-map :
  {f : S ⊢ s → S' ⊢ s} →
  (F : ∀ {e₁ e₂ : S ⊢ s} → e₁ ↪ₚ e₂ → f e₁ ↪ₚ f e₂) →
  e₁ ↪ₚ* e₂ →
  f e₁ ↪ₚ* f e₂
↪ₚ*-map F ↪ₚ*-refl = ↪ₚ*-refl
↪ₚ*-map F (↪ₚ*-step p q) = ↪ₚ*-step (F p) (↪ₚ*-map F q)

↪→↪ₚ : e ↪ e' → e ↪ₚ e'
↪→↪ₚ β-λ            = β-λ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-λ e↪e')     = ξ-λ (↪→↪ₚ e↪e')
↪→↪ₚ (ξ-∀₁ e₁↪e₁')  = ξ-∀ (↪→↪ₚ e₁↪e₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ e₂↪e₂')  = ξ-∀ ↪ₚ-refl (↪→↪ₚ e₂↪e₂')
↪→↪ₚ (ξ-·₁ e₁↪e₁')  = ξ-· (↪→↪ₚ e₁↪e₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ e₂↪e₂')  = ξ-· ↪ₚ-refl (↪→↪ₚ e₂↪e₂')
↪→↪ₚ β-proj₁        = β-proj₁ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ β-proj₂        = β-proj₂ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-∃₁ e↪e')    = ξ-∃ (↪→↪ₚ e↪e') ↪ₚ-refl
↪→↪ₚ (ξ-∃₂ e↪e')    = ξ-∃ ↪ₚ-refl (↪→↪ₚ e↪e')
↪→↪ₚ (ξ-proj₁ e↪e') = ξ-proj₁ (↪→↪ₚ e↪e')
↪→↪ₚ (ξ-proj₂ e↪e') = ξ-proj₂ (↪→↪ₚ e↪e')
↪→↪ₚ (ξ-,₁ e↪e')    = ξ-, (↪→↪ₚ e↪e') ↪ₚ-refl
↪→↪ₚ (ξ-,₂ e↪e')    = ξ-, ↪ₚ-refl (↪→↪ₚ e↪e')
↪→↪ₚ β-J            = β-J ↪ₚ-refl
↪→↪ₚ (ξ-≡₁ e↪e')    = ξ-≡ (↪→↪ₚ e↪e') ↪ₚ-refl
↪→↪ₚ (ξ-≡₂ e↪e')    = ξ-≡ ↪ₚ-refl (↪→↪ₚ e↪e')
↪→↪ₚ (ξ-J₁ e↪e')    = ξ-J (↪→↪ₚ e↪e') ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-J₂ e↪e')    = ξ-J ↪ₚ-refl (↪→↪ₚ e↪e') ↪ₚ-refl
↪→↪ₚ (ξ-J₃ e↪e')    = ξ-J ↪ₚ-refl ↪ₚ-refl (↪→↪ₚ e↪e')

↪*→↪ₚ* : e ↪* e' → e ↪ₚ* e'
↪*→↪ₚ* ↪*-refl                = ↪ₚ*-refl
↪*→↪ₚ* (↪*-step e↪e' e'↪*e'') = ↪ₚ*-step (↪→↪ₚ e↪e') (↪*→↪ₚ* e'↪*e'')

↪ₚ→↪* :
  e ↪ₚ e' →
  e ↪* e'
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

↪ₚ*→↪* :
  e ↪ₚ* e' →
  e ↪* e'
↪ₚ*→↪* ↪ₚ*-refl                  = ↪*-refl
↪ₚ*→↪* (↪ₚ*-step t↪ₚt' t'↪ₚ*t'') = ↪*-trans (↪ₚ→↪* t↪ₚt') (↪ₚ*→↪* t'↪ₚ*t'')

open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (SortTy; Var; NoVar)

private variable
  _∋/⊢_ : List (Sort Var) → Sort Var → Set

↪ₚ-⋯ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ s} →
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
↪ₚσ-wk σ₁↪σ₂ x = ↪ₚ-⋯ᵣ (σ₁↪σ₂ x)

↪ₚσ-↑ : ∀ {σ₁ σ₂ : S₁ →ₛ S₂} →
  σ₁ ↪ₚσ σ₂ →
  (σ₁ ↑ₛ s) ↪ₚσ (σ₂ ↑ₛ s)
↪ₚσ-↑ σ₁↪σ₂ = ↪ₚσ-ext (↪ₚσ-wk σ₁↪σ₂) ↪ₚ-refl

↪ₚσ-⋯ : ∀ {σ σ' : S₁ →ₛ S₂} →
  e ↪ₚ e' →
  σ ↪ₚσ σ' →
  e ⋯ σ ↪ₚ e' ⋯ σ'
↪ₚσ-⋯ ξ-`                         σ↪σ' = σ↪σ' _
↪ₚσ-⋯ {σ' = σ'} (β-λ {e₁' = e₁'} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂')
                                  σ↪σ' = subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ₛ e₁' e₂' σ'))
                                               (β-λ (↪ₚσ-⋯ e₁↪ₚe₁' (↪ₚσ-↑ σ↪σ')) (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ'))
↪ₚσ-⋯ (ξ-λ e↪ₚe')                 σ↪σ' = ξ-λ (↪ₚσ-⋯ e↪ₚe' (↪ₚσ-↑ σ↪σ'))
↪ₚσ-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂')       σ↪σ' = ξ-∀ (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' (↪ₚσ-↑ σ↪σ'))
↪ₚσ-⋯ (ξ-· e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ξ-· (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚσ-⋯ ξ-Set                       σ↪σ' = ξ-Set
↪ₚσ-⋯ (β-proj₁ e₁↪ₚe₁' e₂↪ₚe₂')   σ↪σ' = β-proj₁ (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚσ-⋯ (β-proj₂ e₁↪ₚe₁' e₂↪ₚe₂')   σ↪σ' = β-proj₂ (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚσ-⋯ (ξ-∃ t₁↪ₚt₁' t₂↪ₚt₂')       σ↪σ' = ξ-∃ (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' (↪ₚσ-↑ σ↪σ'))
↪ₚσ-⋯ (ξ-, e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ξ-, (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚσ-⋯ (ξ-proj₁ e↪ₚe')             σ↪σ' = ξ-proj₁ (↪ₚσ-⋯ e↪ₚe' σ↪σ')
↪ₚσ-⋯ (ξ-proj₂ e↪ₚe')             σ↪σ' = ξ-proj₂ (↪ₚσ-⋯ e↪ₚe' σ↪σ')
↪ₚσ-⋯ (β-J e↪ₚe')                 σ↪σ' = β-J (↪ₚσ-⋯ e↪ₚe' σ↪σ')
↪ₚσ-⋯ (ξ-≡ e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ξ-≡ (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚσ-⋯ ξ-refl                      σ↪σ' = ξ-refl
↪ₚσ-⋯ (ξ-J t↪ₚt' e₁↪ₚe₁' e₂↪ₚe₂') σ↪σ' = ξ-J (↪ₚσ-⋯ t↪ₚt' (↪ₚσ-↑ σ↪σ'))
                                             (↪ₚσ-⋯ e₁↪ₚe₁' σ↪σ')
                                             (↪ₚσ-⋯ e₂↪ₚe₂' σ↪σ')

↪ₚσ-⦅_⦆ : ∀ {e₁ e₂ : S ⊢ s} →
  e₁ ↪ₚ e₂ →
  ⦅ e₁ ⦆ ↪ₚσ ⦅ e₂ ⦆
↪ₚσ-⦅ e₁↪ₚe₂ ⦆ = ↪ₚσ-ext (↪ₚσ-refl {σ = idₛ}) e₁↪ₚe₂ 

↪ₚσ-⋯-⦅⦆ : ∀ {e₁ e₁' : (S ▷ s) ⊢ s'}  {e₂ e₂' : S ⊢ s} →
  e₁ ↪ₚ e₁' →
  e₂ ↪ₚ e₂' →
  e₁ ⋯ ⦅ e₂ ⦆ₛ ↪ₚ e₁' ⋯ ⦅ e₂' ⦆ₛ
↪ₚσ-⋯-⦅⦆ e₁↪ₚe₁' e₂↪ₚe₂' = ↪ₚσ-⋯ e₁↪ₚe₁' ↪ₚσ-⦅ e₂↪ₚe₂' ⦆

diamond :
  e ↪ₚ e₁ →
  e ↪ₚ e₂ →
  ∃[ e' ] e₁ ↪ₚ e' × e₂ ↪ₚ e'
diamond ξ-`             ξ-`               = _ , ξ-` , ξ-`
diamond (β-λ {e₁' = e₁'} e₁↪e₁' e₂↪e₂') (β-λ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ ⋯ₛ ⦅ E₂ ⦆ₛ , ↪ₚσ-⋯ e₁'↪E₁ ↪ₚσ-⦅ e₂'↪E₂ ⦆ , ↪ₚσ-⋯ e₁''↪E₁ ↪ₚσ-⦅ e₂''↪E₂ ⦆
diamond (β-λ {e₁' = e₁'} e₁↪e₁' e₂↪e₂') (ξ-· (ξ-λ e₁↪e₁'') e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ ⋯ₛ ⦅ E₂ ⦆ₛ , ↪ₚσ-⋯ e₁'↪E₁ ↪ₚσ-⦅ e₂'↪E₂ ⦆ , (β-λ e₁''↪E₁ e₂''↪E₂)
diamond (ξ-λ e↪e') (ξ-λ e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E
  = λx E , ξ-λ e'↪E , ξ-λ e''↪E
diamond (ξ-∀ t₁↪t₁' t₂↪t₂') (ξ-∀ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = ∀[x∶ T₁ ] T₂ , ξ-∀ t₁'↪T₁ t₂'↪T₂ , ξ-∀ t₁''↪T₁ t₂''↪T₂
diamond (ξ-· (ξ-λ e₁↪e₁') e₂↪e₂') (β-λ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ ⋯ₛ ⦅ E₂ ⦆ₛ , β-λ e₁'↪E₁ e₂'↪E₂ , ↪ₚσ-⋯ e₁''↪E₁ ↪ₚσ-⦅ e₂''↪E₂ ⦆
diamond (ξ-· e₁↪e₁' e₂↪e₂') (ξ-· e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ · E₂ , ξ-· e₁'↪E₁ e₂'↪E₂ , ξ-· e₁''↪E₁ e₂''↪E₂
diamond (β-proj₁ e₁↪e₁' e₂↪e₂') (β-proj₁ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ , e₁'↪E₁ , e₁''↪E₁
diamond (β-proj₁ e₁↪e₁' e₂↪e₂') (ξ-proj₁ (ξ-, e₁↪e₁'' e₂↪e₂''))
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ , e₁'↪E₁ , β-proj₁ e₁''↪E₁ ↪ₚ-refl
diamond (β-proj₂ e₁↪e₁' e₂↪e₂') (β-proj₂ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₂ , e₂'↪E₂ , e₂''↪E₂
diamond (β-proj₂ e₁↪e₁' e₂↪e₂') (ξ-proj₂ (ξ-, e₁↪e₁'' e₂↪e₂''))
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₂ , e₂'↪E₂ , β-proj₂ ↪ₚ-refl e₂''↪E₂
diamond (ξ-∃ t₁↪t₁' t₂↪t₂') (ξ-∃ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = ∃[x∶ T₁ ] T₂ , ξ-∃ t₁'↪T₁ t₂'↪T₂ , ξ-∃ t₁''↪T₁ t₂''↪T₂
diamond (ξ-, e₁↪e₁' e₂↪e₂') (ξ-, e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ `, E₂ , ξ-, e₁'↪E₁ e₂'↪E₂ , ξ-, e₁''↪E₁ e₂''↪E₂
diamond (ξ-proj₁ (ξ-, e₁↪e₁' e₂↪e₂')) (β-proj₁ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ , β-proj₁ e₁'↪E₁ ↪ₚ-refl , e₁''↪E₁
diamond (ξ-proj₁ e↪e') (ξ-proj₁ e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E 
  = `proj₁ E , ξ-proj₁ e'↪E , ξ-proj₁ e''↪E
diamond (ξ-proj₂ (ξ-, e₁↪e₁' e₂↪e₂')) (β-proj₂ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₂ , β-proj₂ ↪ₚ-refl e₂'↪E₂ , e₂''↪E₂
diamond (ξ-proj₂ e↪e') (ξ-proj₂ e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E 
  = `proj₂ E , ξ-proj₂ e'↪E , ξ-proj₂ e''↪E
diamond (β-J e↪e') (β-J e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E 
  = E , e'↪E , e''↪E
diamond (β-J e↪e') (ξ-J t↪t'' ξ-refl e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E 
  = E , e'↪E , β-J e''↪E
diamond (ξ-≡ e₁↪e₁' e₂↪e₂') (ξ-≡ e₁↪e₁'' e₂↪e₂'')
  with diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂''
...  | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = E₁ `≡ E₂ , ξ-≡ e₁'↪E₁ e₂'↪E₂ , ξ-≡ e₁''↪E₁ e₂''↪E₂
diamond ξ-refl ξ-refl = `refl , ξ-refl , ξ-refl
diamond (ξ-J t↪t' ξ-refl e↪e') (β-J e↪e'')
  with diamond e↪e' e↪e''
...  | E , e'↪E , e''↪E 
  = E , β-J e'↪E , e''↪E
diamond (ξ-J t↪t' e₁↪e₁' e₂↪e₂') (ξ-J t↪t'' e₁↪e₁'' e₂↪e₂'')
  with diamond t↪t' t↪t'' | diamond e₁↪e₁' e₁↪e₁'' | diamond e₂↪e₂' e₂↪e₂'' 
...  | T , t'↪T , t''↪T   | E₁ , e₁'↪E₁ , e₁''↪E₁  | E₂ , e₂'↪E₂ , e₂''↪E₂
  = `J T E₁ E₂ , ξ-J t'↪T e₁'↪E₁ e₂'↪E₂ , ξ-J t''↪T e₁''↪E₁ e₂''↪E₂
diamond ξ-Set ξ-Set = `Set , ξ-Set , ξ-Set

strip :
  e ↪ₚ e₁ →
  e ↪ₚ* e₂ →
  ∃[ e' ] (e₁ ↪ₚ* e') × (e₂ ↪ₚ e')
strip {e = e} {e₁} {e₂} e↪ₚe₁ ↪ₚ*-refl = e₁ , ↪ₚ*-refl , e↪ₚe₁
strip {e = e} {e₁} {e₂} e↪ₚe₁ (↪ₚ*-step e↪ₚe₂' e₂'↪ₚ*e₂)
  with diamond e↪ₚe₁ e↪ₚe₂'
... | E , e₁↪ₚE , e₂'↪ₚE
  with strip e₂'↪ₚE e₂'↪ₚ*e₂
... | U , E↪ₚ*U , e₂↪U
  = U , ↪ₚ*-step e₁↪ₚE E↪ₚ*U , e₂↪U

confluenceₚ : 
  e ↪ₚ* e₁ →
  e ↪ₚ* e₂ →
  ∃[ e' ] (e₁ ↪ₚ* e') × (e₂ ↪ₚ* e')
confluenceₚ ↪ₚ*-refl                   e↪ₚ*e₂ = _ , e↪ₚ*e₂ , ↪ₚ*-refl
confluenceₚ (↪ₚ*-step e↪ₚe₁' e₁'↪ₚ*e₁) e↪ₚ*e₂
  with strip e↪ₚe₁' e↪ₚ*e₂
... | E , e₁'↪ₚ*E , e₂↪ₚE
  with confluenceₚ e₁'↪ₚ*e₁ e₁'↪ₚ*E
... | U , e₁↪ₚ*U , E↪ₚ*U
  = U , e₁↪ₚ*U , ↪ₚ*-step e₂↪ₚE E↪ₚ*U 

confluence : 
  e ↪* e₁ →
  e ↪* e₂ →
  ∃[ e' ] (e₁ ↪* e') × (e₂ ↪* e')
confluence e↪*e₁ e↪*e₂
  with confluenceₚ (↪*→↪ₚ* e↪*e₁) (↪*→↪ₚ* e↪*e₂)
... | e' , e₁↪ₚ*e' , e₂↪ₚ*e'
  = e' , ↪ₚ*→↪* e₁↪ₚ*e' , ↪ₚ*→↪* e₂↪ₚ*e'
