module Kitty.Examples.LambdaPiSigma-Derive-Sem.Confluence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPiSigma-Derive-Sem.Definitions
open import Kitty.Util.Closures

open import Kitty.Typing.ITerms compose-traversal kit-type ctx-repr

≡ᶜ-cong-⊢ : ∀ {µ M} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} → 
  Γ₁ ≡ᶜ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ e ∶ t
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢` {x = x} ∋x) = ⊢` (≡ᶜ-cong-∋ x Γ₁≡Γ₂ ∋x)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢λ ⊢e₁ ⊢e₂)    = ⊢λ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶ Γ₁≡Γ₂ refl) ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢∀ ⊢e₁ ⊢e₂)    = ⊢∀ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶ Γ₁≡Γ₂ refl) ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢Σ ⊢e₁ ⊢e₂)    = ⊢Σ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶ Γ₁≡Γ₂ refl) ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢, ⊢e₁ ⊢e₂)    = ⊢, (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢proj₁ ⊢e)     = ⊢proj₁ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢proj₂ ⊢e)     = ⊢proj₂ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢tt             = ⊢tt
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢⊤              = ⊢⊤
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢· ⊢e₁ ⊢e₂)    = ⊢· (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢★              = ⊢★
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢≣ eq ⊢e)      = ⊢≣ eq (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` ; ≡ᶜ-cong-⊢ = ≡ᶜ-cong-⊢ }

open import Kitty.Typing.IKit compose-traversal kit-type ctx-repr iterms
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

ξ-Σ₁* :
  t₁ ↪* t₁' →
  Σ[x∶ t₁ ] t₂ ↪* Σ[x∶ t₁' ] t₂
ξ-Σ₁* = map-↪* ξ-Σ₁

ξ-Σ₂* :
  t₂ ↪* t₂' →
  Σ[x∶ t₁ ] t₂ ↪* Σ[x∶ t₁ ] t₂'
ξ-Σ₂* = map-↪* ξ-Σ₂

ξ-,₁* :
  t₁ ↪* t₁' →
  t₁ , t₂ ↪* t₁' , t₂
ξ-,₁* = map-↪* ξ-,₁

ξ-,₂* :
  t₂ ↪* t₂' →
  t₁ , t₂ ↪* t₁ , t₂'
ξ-,₂* = map-↪* ξ-,₂

ξ-proj₁* :
  e ↪* e' →
  `proj₁ e ↪* `proj₁ e'
ξ-proj₁* = map-↪* ξ-proj₁

ξ-proj₂* :
  e ↪* e' →
  `proj₂ e ↪* `proj₂ e'
ξ-proj₂* = map-↪* ξ-proj₂

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
  β-proj₁ :
    t₁ ↪ₚ t₁' →
    `proj₁ (t₁ , t₂) ↪ₚ t₁'
  β-proj₂ : ∀ {t₂ : µ ⊢ 𝕖} →
    t₂ ↪ₚ t₂' →
    `proj₂ (t₁ , t₂) ↪ₚ t₂'
  ξ-λ :
    t ↪ₚ t' →
    λx t ↪ₚ λx t'
  ξ-∀ :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    ∀[x∶ t₁ ] t₂ ↪ₚ ∀[x∶ t₁' ] t₂'
  ξ-Σ :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    Σ[x∶ t₁ ] t₂ ↪ₚ Σ[x∶ t₁' ] t₂'
  ξ-, :
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    t₁ , t₂ ↪ₚ t₁' , t₂'
  ξ-⊤ :
    `⊤ ↪ₚ `⊤ {µ}
  ξ-tt :
    `tt ↪ₚ `tt {µ}
  ξ-proj₁ :
    t ↪ₚ t' →
    `proj₁ t ↪ₚ `proj₁ t'
  ξ-proj₂ :
    t ↪ₚ t' →
    `proj₂ t ↪ₚ `proj₂ t'
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
↪ₚ-refl {t = Σ[x∶ t₁ ] t₂} = ξ-Σ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = t₁ , t₂}      = ξ-, ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = `proj₁ t}     = ξ-proj₁ ↪ₚ-refl
↪ₚ-refl {t = `proj₂ t}     = ξ-proj₂ ↪ₚ-refl
↪ₚ-refl {t = `⊤}           = ξ-⊤
↪ₚ-refl {t = `tt}          = ξ-tt

open import Kitty.Semantics.ISemantics compose-traversal kit-type ctx-repr

semanticsₚ : Semantics
semanticsₚ = record { _↪_ = _↪ₚ_ }

open Semantics semanticsₚ public using () renaming
  ( _↪*_ to _↪ₚ*_
  ; ↪*-trans to ↪ₚ*-trans
  ; _↪σ_ to _↪ₚσ_
  ; _↪σ*_ to _↪ₚσ*_
  ; _↪*σ_ to _↪ₚ*σ_
  )

rsemanticsₚ : ReflexiveSemantics semanticsₚ
rsemanticsₚ = record { ↪-refl = ↪ₚ-refl }

open ReflexiveTransitiveClosure using (refl; step)

open SemKit ⦃ … ⦄

↪-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄
    ⦃ K : KitT 𝕂 ⦄
    ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄
    ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    ⦃ SK : SemKit semanticsₚ 𝕂 K C₁ C₂ ⦄
    {µ₁ µ₂ M} {t t' : µ₁ ⊢ M} {ϕ ϕ' : µ₁ –[ 𝕂 ]→ µ₂}
  → t ↪ₚ t'
  → ϕ ≡ϕ/↪ϕ ϕ'
  → t ⋯ ϕ ↪ₚ t' ⋯ ϕ'
↪-⋯ {ϕ = ϕ} {ϕ'} (ξ-` {x = x}) ϕ↪ϕ' = ↪/id' {ϕ₁ = ϕ} {ϕ₂ = ϕ'} (ϕ↪ϕ' x)
↪-⋯ {ϕ = ϕ} {ϕ'} (β-λ {t₁' = t₁'} {t₂' = t₂'} t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ t₁' t₂' ϕ'))
                                                                              (β-λ (↪-⋯ t₁↪ₚt₁' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
                                                                                   (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ'))
↪-⋯ (ξ-λ t↪t')                ϕ↪ϕ' = ξ-λ (↪-⋯ t↪t' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂')     ϕ↪ϕ' = ξ-∀ (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-· t₁↪ₚt₁' t₂↪ₚt₂')     ϕ↪ϕ' = ξ-· (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ')
↪-⋯ ξ-★                       ϕ↪ϕ' = ξ-★
↪-⋯ (β-proj₁ t↪ₚt')           ϕ↪ϕ' = β-proj₁ (↪-⋯ t↪ₚt' ϕ↪ϕ')
↪-⋯ (β-proj₂ t₂↪ₚt₂')         ϕ↪ϕ' = β-proj₂ (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ')
↪-⋯ (ξ-Σ t₁↪ₚt₁' t₂↪ₚt₂')     ϕ↪ϕ' = ξ-Σ (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-, t₁↪ₚt₁' t₂↪ₚt₂')     ϕ↪ϕ' = ξ-, (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ')
↪-⋯ ξ-⊤                       ϕ↪ϕ' = ξ-⊤
↪-⋯ ξ-tt                      ϕ↪ϕ' = ξ-tt
↪-⋯ (ξ-proj₁ t↪ₚt')           ϕ↪ϕ' = ξ-proj₁ (↪-⋯ t↪ₚt' ϕ↪ϕ')
↪-⋯ (ξ-proj₂ t↪ₚt')           ϕ↪ϕ' = ξ-proj₂ (↪-⋯ t↪ₚt' ϕ↪ϕ')

sem-traversal : SemTraversal rsemanticsₚ
sem-traversal = record { ↪-⋯ = ↪-⋯ }

open SemTraversal sem-traversal renaming (↪-⋯ₛ to ↪ₚσ-⋯) hiding (↪-⋯)

module Semₚ where
  open Semantics semanticsₚ public
  open ReflexiveSemantics rsemanticsₚ public
  open SemTraversal sem-traversal public

-- Conversions between ↪ and ↪ₚ ------------------------------------------------

↪→↪ₚ : t ↪ t' → t ↪ₚ t'
↪→↪ₚ β-λ            = β-λ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ β-proj₁        = β-proj₁ ↪ₚ-refl
↪→↪ₚ β-proj₂        = β-proj₂ ↪ₚ-refl
↪→↪ₚ (ξ-λ t↪t')     = ξ-λ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-∀₁ t₁↪t₁')  = ξ-∀ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ t₂↪t₂')  = ξ-∀ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-Σ₁ t₁↪t₁')  = ξ-Σ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-Σ₂ t₂↪t₂')  = ξ-Σ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-·₁ t₁↪t₁')  = ξ-· (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ t₂↪t₂')  = ξ-· ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-,₁ t₁↪t₁')  = ξ-, (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-,₂ t₂↪t₂')  = ξ-, ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-proj₁ t↪t') = ξ-proj₁ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-proj₂ t↪t') = ξ-proj₂ (↪→↪ₚ t↪t')

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
↪ₚ→↪* (ξ-Σ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  Σ[x∶ t₁  ] t₂  ↪*⟨ ξ-Σ₁* (↪ₚ→↪* t₁↪ₚt₁') ⟩
  Σ[x∶ t₁' ] t₂  ↪*⟨ ξ-Σ₂* (↪ₚ→↪* t₂↪ₚt₂') ⟩
  Σ[x∶ t₁' ] t₂' ↪∎
↪ₚ→↪* (ξ-· {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  t₁  · t₂  ↪*⟨ ξ-·₁* (↪ₚ→↪* t₁↪ₚt₁') ⟩
  t₁' · t₂  ↪*⟨ ξ-·₂* (↪ₚ→↪* t₂↪ₚt₂') ⟩
  t₁' · t₂' ↪∎
↪ₚ→↪* (ξ-, {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂') =
  t₁  , t₂  ↪*⟨ ξ-,₁* (↪ₚ→↪* t₁↪ₚt₁') ⟩
  t₁' , t₂  ↪*⟨ ξ-,₂* (↪ₚ→↪* t₂↪ₚt₂') ⟩
  t₁' , t₂' ↪∎
↪ₚ→↪* (ξ-proj₁ t↪ₚt') = ξ-proj₁* (↪ₚ→↪* t↪ₚt')
↪ₚ→↪* (ξ-proj₂ t↪ₚt') = ξ-proj₂* (↪ₚ→↪* t↪ₚt')
↪ₚ→↪* (β-proj₁ {t₁ = t₁} {t₁'} {t₂} t₁↪ₚt₁') =
  `proj₁ (t₁ , t₂)  ↪*⟨ ξ-proj₁* (ξ-,₁* (↪ₚ→↪* t₁↪ₚt₁')) ⟩
  `proj₁ (t₁' , t₂) ↪⟨ β-proj₁ ⟩
  t₁' ↪∎
↪ₚ→↪* (β-proj₂ {t₂' = t₂'} {t₁} {t₂} t₂↪ₚt₂') = 
  `proj₂ (t₁ , t₂)  ↪*⟨ ξ-proj₂* (ξ-,₂* (↪ₚ→↪* t₂↪ₚt₂')) ⟩
  `proj₂ (t₁ , t₂') ↪⟨ β-proj₂ ⟩
  t₂'  ↪∎
↪ₚ→↪* ξ-★                    = refl
↪ₚ→↪* ξ-⊤                 = refl
↪ₚ→↪* ξ-tt                = refl

sem-trans : SemTrans semantics semanticsₚ
sem-trans = record { toₚ = ↪→↪ₚ ; fromₚ = ↪ₚ→↪* }

open SemTrans sem-trans public renaming (toₚ* to ↪*→↪ₚ*; fromₚ* to ↪ₚ*→↪*)
open SemTrans-↪-⋯ sem-traversal public

--------------------------------------------------------------------------------

diamondₚ :
  t ↪ₚ t₁ →
  t ↪ₚ t₂ →
  ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
diamondₚ ξ-`             ξ-`               = _ , ξ-` , ξ-`
diamondₚ (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
diamondₚ (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (ξ-· (ξ-λ t₁↪t₁'') t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , (β-λ t₁''↪T₁ t₂''↪T₂)
diamondₚ (ξ-λ t↪t') (ξ-λ t↪t'')
  with diamondₚ t↪t' t↪t''
...  | T , t'↪T , t''↪T
  = λx T , ξ-λ t'↪T , ξ-λ t''↪T
diamondₚ (ξ-∀ t₁↪t₁' t₂↪t₂') (ξ-∀ t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = ∀[x∶ T₁ ] T₂ , ξ-∀ t₁'↪T₁ t₂'↪T₂ , ξ-∀ t₁''↪T₁ t₂''↪T₂
diamondₚ (ξ-· (ξ-λ t₁↪t₁') t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , β-λ t₁'↪T₁ t₂'↪T₂ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
diamondₚ (ξ-· t₁↪t₁' t₂↪t₂') (ξ-· t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ · T₂ , ξ-· t₁'↪T₁ t₂'↪T₂ , ξ-· t₁''↪T₁ t₂''↪T₂
diamondₚ ξ-★ ξ-★ = ★ , ξ-★ , ξ-★
diamondₚ (β-proj₁ t₁↪t₁') (β-proj₁ t₁↪t₁'') = diamondₚ t₁↪t₁' t₁↪t₁''
diamondₚ (β-proj₂ t₂↪t₂') (β-proj₂ t₂↪t₂'') = diamondₚ t₂↪t₂' t₂↪t₂''
diamondₚ (β-proj₁ t₁↪t₁') (ξ-proj₁ (ξ-, t₁↪t₁'' t₂↪t₂''))
  with diamondₚ t₁↪t₁' t₁↪t₁''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁
  = T₁ , t₁'↪T₁ , β-proj₁ t₁''↪T₁
diamondₚ (β-proj₂ t₂↪t₂') (ξ-proj₂ (ξ-, t₁↪t₁'' t₂↪t₂''))
  with diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₂ , t₂'↪T₂ , β-proj₂ t₂''↪T₂
diamondₚ (ξ-Σ t₁↪t₁' t₂↪t₂') (ξ-Σ t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁   | T₂ , t₂'↪T₂ , t₂''↪T₂
 = Σ[x∶ T₁ ] T₂ , ξ-Σ t₁'↪T₁ t₂'↪T₂ , ξ-Σ t₁''↪T₁ t₂''↪T₂
diamondₚ (ξ-, t₁↪t₁' t₂↪t₂') (ξ-, t₁↪t₁'' t₂↪t₂'')
  with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁   | T₂ , t₂'↪T₂ , t₂''↪T₂
 = (T₁ , T₂) , ξ-, t₁'↪T₁ t₂'↪T₂ , ξ-, t₁''↪T₁ t₂''↪T₂
diamondₚ (ξ-proj₁ (ξ-, t₁↪t₁' t₂↪t₂')) (β-proj₁ t₁↪t₁'') 
  with diamondₚ t₁↪t₁' t₁↪t₁''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁
  = T₁ , β-proj₁ t₁'↪T₁ , t₁''↪T₁
diamondₚ (ξ-proj₁ t↪t') (ξ-proj₁ t↪t'')
  with diamondₚ t↪t' t↪t''
...  | T , t'↪T , t''↪T  
 = `proj₁ T , ξ-proj₁ t'↪T , ξ-proj₁ t''↪T
diamondₚ (ξ-proj₂ (ξ-, t₁↪t₁' t₂↪t₂')) (β-proj₂ t₂↪t₂'') 
  with diamondₚ t₂↪t₂' t₂↪t₂''
...  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₂ , β-proj₂ t₂'↪T₂ , t₂''↪T₂
diamondₚ (ξ-proj₂ t↪t') (ξ-proj₂ t↪t'')
  with diamondₚ t↪t' t↪t''
...  | T , t'↪T , t''↪T  
 = `proj₂ T , ξ-proj₂ t'↪T , ξ-proj₂ t''↪T
diamondₚ ξ-⊤ ξ-⊤ = `⊤ , ξ-⊤ , ξ-⊤
diamondₚ ξ-tt ξ-tt = `tt , ξ-tt , ξ-tt

open SemTrans-confluence diamondₚ public
  using (stripₚ; confluenceₚ; confluence)
