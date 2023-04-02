module Kitty.Examples.LambdaPi-Derive.Confluence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Util.Closures
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_ ; _,_)

ξ-λ* :
  e ↪* e' →
  λx e ↪* λx e'
ξ-λ* = map-↪* ξ-λ

ξ-∀₁* :
  t₁ ↪* t₁' →
  ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁' ] t₂
ξ-∀₁* = map-↪* ξ-∀₁

ξ-∀₂* :
  t₂ ↪* t₂' →
  ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁ ] t₂'
ξ-∀₂* = map-↪* ξ-∀₂

ξ-·₁* :
  e₁ ↪* e₁' →
  e₁ · e₂ ↪* e₁' · e₂
ξ-·₁* = map-↪* ξ-·₁

ξ-·₂* :
  e₂ ↪* e₂' →
  e₁ · e₂ ↪* e₁ · e₂'
ξ-·₂* = map-↪* ξ-·₂

infix   3  _↪ₚ_
data _↪ₚ_ : µ ⊢ M → µ ⊢ M → Set where
  ξ-` : ∀ {x : µ ∋ m} →
    ` x ↪ₚ ` x
  β-λ : ∀ {t₁ t₁' : (µ ▷ 𝕖) ⊢ 𝕖} {t₂ t₂' : µ ⊢ 𝕖} →
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    (λx t₁) · t₂ ↪ₚ t₁' ⋯ ⦅ t₂' ⦆ₛ
  ξ-λ :
    t ↪ₚ t' →
    λx t ↪ₚ λx t'
  ξ-∀ :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ₚ ∀[x∶ t₁' ] t₂'
  ξ-· :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    t₁ · t₂ ↪ₚ t₁' · t₂'
  ξ-★ :
    ★ ↪ₚ (★ {µ = µ})

↪ₚ-refl : t ↪ₚ t
↪ₚ-refl {t = ` x}          = ξ-`
↪ₚ-refl {t = λx t}         = ξ-λ ↪ₚ-refl
↪ₚ-refl {t = ∀[x∶ t₁ ] t₂} = ξ-∀ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = t₁ · t₂}      = ξ-· ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = ★}            = ξ-★

open ReflexiveTransitiveClosure₂ (_⊢_) _↪ₚ_ renaming
  ( ReflTrans to _↪ₚ*_
  ; map-ReflTrans to map-↪ₚ*
  ; _⟨_⟩_ to _↪ₚ⟨_⟩_
  ; _*⟨_⟩_ to _↪ₚ*⟨_⟩_
  ; _∎ to _↪ₚ∎
  ; trans to ↪ₚ*-trans
  ; embed to ↪ₚ*-embed
  ) hiding (refl; step) public

↪→↪ₚ : t ↪ t' → t ↪ₚ t'
↪→↪ₚ β-λ           = β-λ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ (ξ-λ t↪t')    = ξ-λ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-∀₁ t₁↪t₁') = ξ-∀ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ t₂↪t₂') = ξ-∀ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-·₁ t₁↪t₁') = ξ-· (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ t₂↪t₂') = ξ-· ↪ₚ-refl (↪→↪ₚ t₂↪t₂')

↪*→↪ₚ* : t ↪* t' → t ↪ₚ* t'
↪*→↪ₚ* refl                = refl
↪*→↪ₚ* (step t↪t' t'↪*t'') = step (↪→↪ₚ t↪t') (↪*→↪ₚ* t'↪*t'')

↪ₚ→↪* : t ↪ₚ t' → t ↪* t'
↪ₚ→↪* ξ-`                    = refl
↪ₚ→↪* (β-λ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂'') =
  ((λx t₁) · t₂)   ↪*⟨ ξ-·₁* (ξ-λ* (↪ₚ→↪* t₁↪ₚt₁')) ⟩
  ((λx t₁') · t₂)  ↪*⟨ ξ-·₂* (↪ₚ→↪* t₂↪ₚt₂'') ⟩
  ((λx t₁') · t₂') ↪⟨ β-λ ⟩
  (t₁' ⋯ ⦅ t₂' ⦆ₛ) ↪∎
↪ₚ→↪* (ξ-λ t↪ₚt')            = ξ-λ* (↪ₚ→↪* t↪ₚt')
↪ₚ→↪* (ξ-∀ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  ∀[x∶ t₁  ] t₂  ↪*⟨ ξ-∀₁* (↪ₚ→↪* t₁↪ₚt₁') ⟩
  ∀[x∶ t₁' ] t₂  ↪*⟨ ξ-∀₂* (↪ₚ→↪* t₂↪ₚt₂') ⟩
  ∀[x∶ t₁' ] t₂' ↪∎
↪ₚ→↪* (ξ-· {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  t₁  · t₂  ↪*⟨ ξ-·₁* (↪ₚ→↪* t₁↪ₚt₁') ⟩
  t₁' · t₂  ↪*⟨ ξ-·₂* (↪ₚ→↪* t₂↪ₚt₂') ⟩
  t₁' · t₂' ↪∎
↪ₚ→↪* ξ-★                    = refl

↪ₚ*→↪* : t ↪ₚ* t' → t ↪* t'
↪ₚ*→↪* refl                  = refl
↪ₚ*→↪* (step t↪ₚt' t'↪ₚ*t'') = ↪*-trans (↪ₚ→↪* t↪ₚt') (↪ₚ*→↪* t'↪ₚ*t'')

_↪ₚσ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ↪ₚσ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ↪ₚ σ₂ _ x

-- Are Ctx's basically Substitutions which don't weaken automatically?
-- Can be represent them as such or even generalize our substitutions?
↪ₚσ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
  σ ↪ₚσ σ
↪ₚσ-refl {m = 𝕖} x = ↪ₚ-refl

↪ₚσ-ext : ∀ {µ₁ µ₂} {σ₁ σ₂ : µ₁ →ₛ µ₂} {m} {t₁ t₂ : µ₂ ⊢ m→M m} →
  σ₁ ↪ₚσ σ₂ →
  t₁ ↪ₚ t₂ →
  (σ₁ ,ₛ t₁) ↪ₚσ (σ₂ ,ₛ t₂)
↪ₚσ-ext σ₁↪σ₂ t₁↪t₂ (here refl) = t₁↪t₂
↪ₚσ-ext σ₁↪σ₂ t₁↪t₂ (there x)   = σ₁↪σ₂ x

↪ₚ-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ₚ t' →
  t ⋯ ϕ ↪ₚ t' ⋯ ϕ
↪ₚ-⋯ ξ-`                = ↪ₚ-refl
↪ₚ-⋯ (ξ-λ t↪ₚt')        = ξ-λ (↪ₚ-⋯ t↪ₚt')
↪ₚ-⋯ (ξ-∀ t↪ₚt' t↪ₚt'') = ξ-∀ (↪ₚ-⋯ t↪ₚt') (↪ₚ-⋯ t↪ₚt'')
↪ₚ-⋯ (ξ-· t↪ₚt' t↪ₚt'') = ξ-· (↪ₚ-⋯ t↪ₚt') (↪ₚ-⋯ t↪ₚt'')
↪ₚ-⋯ ξ-★                = ξ-★
↪ₚ-⋯ {ϕ = ϕ} (β-λ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  subst (((λx t₁) · t₂) ⋯ ϕ ↪ₚ_)
        (sym (dist-⦅⦆ₛ-⋯ t₁' t₂' ϕ))
        (β-λ (↪ₚ-⋯ t₁↪ₚt₁') (↪ₚ-⋯ t₂↪ₚt₂'))

↪ₚ-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ₚ t' →
  t ⋯ₛ ϕ ↪ₚ t' ⋯ₛ ϕ
↪ₚ-⋯ₛ = ↪ₚ-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

↪ₚ-⋯ᵣ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ᵣ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ₚ t' →
  t ⋯ᵣ ϕ ↪ₚ t' ⋯ᵣ ϕ
↪ₚ-⋯ᵣ = ↪ₚ-⋯ where instance _ = kitᵣ; _ = kittᵣ; _ = ckitₛᵣ; _ = ckitᵣ

↪ₚσ-wk : ∀ {µ₁ µ₂} {σ₁ σ₂ : µ₁ →ₛ µ₂} {m'} →
  σ₁ ↪ₚσ σ₂ →
  wk→ₛ m' σ₁ ↪ₚσ wk→ₛ m' σ₂
↪ₚσ-wk {m' = 𝕖} σ₁↪σ₂ x = ↪ₚ-⋯ᵣ (σ₁↪σ₂ x)

↪ₚσ-↑ : ∀ {µ₁ µ₂} {σ₁ σ₂ : µ₁ →ₛ µ₂} {m'} →
  σ₁ ↪ₚσ σ₂ →
  (σ₁ ↑ₛ m') ↪ₚσ (σ₂ ↑ₛ m')
↪ₚσ-↑ {m' = 𝕖} σ₁↪σ₂ = ↪ₚσ-ext (↪ₚσ-wk σ₁↪σ₂) ↪ₚ-refl

-- ↪σ-⋯ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} (t : µ₁ ⊢ m) →
--   σ ↪ₚσ σ' →
--   t ⋯ σ ↪ₚ t ⋯ σ'
-- ↪σ-⋯ (` x)          σ↪σ' = σ↪σ' x
-- ↪σ-⋯ (λx t)         σ↪σ' = ξ-λ (↪σ-⋯ t (↪ₚσ-↑ σ↪σ'))
-- ↪σ-⋯ (∀[x∶ t₁ ] t₂) σ↪σ' = ξ-∀ (↪σ-⋯ t₁ σ↪σ') (↪σ-⋯ t₂ (↪ₚσ-↑ σ↪σ'))
-- ↪σ-⋯ (t₁ · t₂)      σ↪σ' = ξ-· (↪σ-⋯ t₁ σ↪σ') (↪σ-⋯ t₂ σ↪σ')
-- ↪σ-⋯ ★              σ↪σ' = ξ-★

↪ₚσ-⋯ : ∀ {µ₁ µ₂ m} {t t' : µ₁ ⊢ m} {σ σ' : µ₁ →ₛ µ₂} →
  t ↪ₚ t' →
  σ ↪ₚσ σ' →
  t ⋯ σ ↪ₚ t' ⋯ σ'
↪ₚσ-⋯ ξ-`                   σ↪σ' = σ↪σ' _
↪ₚσ-⋯ {σ = σ} {σ'} (β-λ {t₁' = t₁'} {t₂' = t₂'} t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ₛ t₁' t₂' σ'))
                                                                              (β-λ (↪ₚσ-⋯ t₁↪ₚt₁' (↪ₚσ-↑ σ↪σ'))
                                                                                   (↪ₚσ-⋯ t₂↪ₚt₂' σ↪σ'))
↪ₚσ-⋯ (ξ-λ t↪ₚt')           σ↪σ' = ξ-λ (↪ₚσ-⋯ t↪ₚt' (↪ₚσ-↑ σ↪σ'))
↪ₚσ-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = ξ-∀ (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' (↪ₚσ-↑ σ↪σ'))
↪ₚσ-⋯ (ξ-· t₁↪ₚt₁' t₂↪ₚt₂') σ↪σ' = ξ-· (↪ₚσ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚσ-⋯ t₂↪ₚt₂' σ↪σ')
↪ₚσ-⋯ ξ-★                   σ↪σ' = ξ-★

↪ₚσ-⦅_⦆ : ∀ {µ m} {t₁ t₂ : µ ⊢ m→M m} →
  t₁ ↪ₚ t₂ →
  ⦅ t₁ ⦆ ↪ₚσ ⦅ t₂ ⦆
↪ₚσ-⦅ t₁↪ₚt₂ ⦆ = ↪ₚσ-ext (↪ₚσ-refl {σ = idₛ}) t₁↪ₚt₂ 

↪ₚσ-⋯-⦅⦆ : ∀ {µ M} {t₁ t₁' : (µ ▷ 𝕖) ⊢ M}  {t₂ t₂' : µ ⊢ 𝕖} →
  t₁ ↪ₚ t₁' →
  t₂ ↪ₚ t₂' →
  t₁ ⋯ ⦅ t₂ ⦆ₛ ↪ₚ t₁' ⋯ ⦅ t₂' ⦆ₛ
↪ₚσ-⋯-⦅⦆ t₁↪ₚt₁' t₂↪ₚt₂' = ↪ₚσ-⋯ t₁↪ₚt₁' ↪ₚσ-⦅ t₂↪ₚt₂' ⦆

diamond :
  t ↪ₚ t₁ →
  t ↪ₚ t₂ →
  ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
diamond ξ-`             ξ-`               = _ , ξ-` , ξ-`
diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ ↪ₚσ-⦅ t₂'↪T₂ ⦆ , ↪ₚσ-⋯ t₁''↪T₁ ↪ₚσ-⦅ t₂''↪T₂ ⦆
diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (ξ-· (ξ-λ t₁↪t₁'') t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ ↪ₚσ-⦅ t₂'↪T₂ ⦆ , (β-λ t₁''↪T₁ t₂''↪T₂)
diamond (ξ-λ t↪t') (ξ-λ t↪t'')
  with diamond t↪t' t↪t''
...  | T , t'↪T , t''↪T
  = λx T , ξ-λ t'↪T , ξ-λ t''↪T
diamond (ξ-∀ t₁↪t₁' t₂↪t₂') (ξ-∀ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = ∀[x∶ T₁ ] T₂ , ξ-∀ t₁'↪T₁ t₂'↪T₂ , ξ-∀ t₁''↪T₁ t₂''↪T₂
diamond (ξ-· (ξ-λ t₁↪t₁') t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , β-λ t₁'↪T₁ t₂'↪T₂ , ↪ₚσ-⋯ t₁''↪T₁ ↪ₚσ-⦅ t₂''↪T₂ ⦆
diamond (ξ-· t₁↪t₁' t₂↪t₂') (ξ-· t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ · T₂ , ξ-· t₁'↪T₁ t₂'↪T₂ , ξ-· t₁''↪T₁ t₂''↪T₂
diamond ξ-★ ξ-★ = ★ , ξ-★ , ξ-★

strip :
  t ↪ₚ t₁ →
  t ↪ₚ* t₂ →
  ∃[ t' ] (t₁ ↪ₚ* t') × (t₂ ↪ₚ t')
strip {t = t} {t₁} {t₂} t↪ₚt₁ refl = t₁ , refl , t↪ₚt₁
strip {t = t} {t₁} {t₂} t↪ₚt₁ (step t↪ₚt₂' t₂'↪ₚ*t₂)
  with diamond t↪ₚt₁ t↪ₚt₂'
... | T , t₁↪ₚT , t₂'↪ₚT
  with strip t₂'↪ₚT t₂'↪ₚ*t₂
... | U , T↪ₚ*U , t₂↪U
  = U , step t₁↪ₚT T↪ₚ*U , t₂↪U

confluenceₚ : 
  t ↪ₚ* t₁ →
  t ↪ₚ* t₂ →
  ∃[ t' ] (t₁ ↪ₚ* t') × (t₂ ↪ₚ* t')
confluenceₚ refl                   t↪ₚ*t₂ = _ , t↪ₚ*t₂ , refl
confluenceₚ (step t↪ₚt₁' t₁'↪ₚ*t₁) t↪ₚ*t₂
  with strip t↪ₚt₁' t↪ₚ*t₂
... | T , t₁'↪ₚ*T , t₂↪ₚT
  with confluenceₚ t₁'↪ₚ*t₁ t₁'↪ₚ*T
... | U , t₁↪ₚ*U , T↪ₚ*U
  = U , t₁↪ₚ*U , step t₂↪ₚT T↪ₚ*U 

confluence : 
  t ↪* t₁ →
  t ↪* t₂ →
  ∃[ t' ] (t₁ ↪* t') × (t₂ ↪* t')
confluence t↪*t₁ t↪*t₂
  with confluenceₚ (↪*→↪ₚ* t↪*t₁) (↪*→↪ₚ* t↪*t₂)
... | t' , t₁↪ₚ*t' , t₂↪ₚ*t'
  = t' , ↪ₚ*→↪* t₁↪ₚ*t' , ↪ₚ*→↪* t₂↪ₚ*t'
