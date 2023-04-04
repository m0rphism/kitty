module Kitty.Examples.LambdaPi-Derive-Sem.Confluence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive-Sem.Definitions
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
  β-λ : ∀ {t₁ t₁' : (µ ▷ 𝕖) ⊢ 𝕖} {t₂ t₂' : µ ⊢ 𝕖} →
    t₁ ↪ₚ t₁' →
    t₂ ↪ₚ t₂' →
    (λx t₁) · t₂ ↪ₚ t₁' ⋯ ⦅ t₂' ⦆ₛ
  η-λ : ∀ {t : µ ⊢ 𝕖} →
    t ↪ₚ t' →
    λx (wk _ t · ` here refl) ↪ₚ t'
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
  ξ-` : ∀ {x : µ ∋ m} →
    ` x ↪ₚ ` x
  ξ-★ :
    ★ ↪ₚ (★ {µ = µ})

↪ₚ-refl : t ↪ₚ t
↪ₚ-refl {t = ` x}          = ξ-`
↪ₚ-refl {t = λx t}         = ξ-λ ↪ₚ-refl
↪ₚ-refl {t = ∀[x∶ t₁ ] t₂} = ξ-∀ ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = t₁ · t₂}      = ξ-· ↪ₚ-refl ↪ₚ-refl
↪ₚ-refl {t = ★}            = ξ-★

open import Kitty.Semantics.ISemantics compose-traversal kit-type

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
↪-⋯ (ξ-λ t↪t')       ϕ↪ϕ' = ξ-λ (↪-⋯ t↪t' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = ξ-∀ (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-· t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = ξ-· (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ')
↪-⋯ {ϕ = ϕ} {ϕ'} (ξ-` {x = x}) ϕ↪ϕ' = ↪/id' {ϕ₁ = ϕ} {ϕ₂ = ϕ'} (ϕ↪ϕ' x)
↪-⋯ ξ-★                   ϕ↪ϕ' = ξ-★
↪-⋯ {ϕ = ϕ} {ϕ'} (β-λ {t₁' = t₁'} {t₂' = t₂'} t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' =
  subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ t₁' t₂' ϕ'))
                (β-λ (↪-⋯ t₁↪ₚt₁' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
                     (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ'))
↪-⋯ {ϕ = ϕ} {ϕ'} (η-λ {t' = t'} {t = t} t↪ₚt') ϕ↪ϕ' =
  subst₂ (_↪ₚ_) (λx ((t ⋯ ϕ ⋯ wkₖ _ id) · ` here refl)
                   ≡⟨ cong₂ (λ ■₁ ■₂ → λx (■₁ · ■₂))
                            (sym (dist-↑-f t ϕ))
                            (sym (id/`/id (here refl)))⟩
                 λx ((t ⋯ᵣ wknᵣ ⋯ (ϕ ↑ _)) · (` here refl ⋯ (ϕ ↑ _))) ∎)
                 refl (η-λ (↪-⋯ t↪ₚt' ϕ↪ϕ'))

sem-traversal : SemTraversal rsemanticsₚ
sem-traversal = record { ↪-⋯ = ↪-⋯ }

open SemTraversal sem-traversal renaming (↪-⋯ₛ to ↪ₚσ-⋯) hiding (↪-⋯)

module Semₚ where
  open Semantics semanticsₚ public
  open ReflexiveSemantics rsemanticsₚ public
  open SemTraversal sem-traversal public

-- Conversions between ↪ and ↪ₚ ------------------------------------------------

↪→↪ₚ : t ↪ t' → t ↪ₚ t'
↪→↪ₚ β-λ           = β-λ ↪ₚ-refl ↪ₚ-refl
↪→↪ₚ η-λ           = η-λ ↪ₚ-refl
↪→↪ₚ (ξ-λ t↪t')    = ξ-λ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-∀₁ t₁↪t₁') = ξ-∀ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ t₂↪t₂') = ξ-∀ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-·₁ t₁↪t₁') = ξ-· (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ t₂↪t₂') = ξ-· ↪ₚ-refl (↪→↪ₚ t₂↪t₂')

↪-⋯ᵣ' : ∀ {µ₁ µ₂ M} {ϕ : µ₁ →ᵣ µ₂} {t t' : µ₁ ⊢ M} →
  t ↪ t' →
  t ⋯ᵣ ϕ ↪ t' ⋯ᵣ ϕ
↪-⋯ᵣ' {ϕ = ϕ} (β-λ {e₁ = e₁} {e₂ = e₂}) =
  subst (((λx e₁) · e₂) ⋯ᵣ ϕ ↪_) (sym (dist-⦅⦆ₛ-⋯ e₁ e₂ ϕ)) β-λ
↪-⋯ᵣ' {ϕ = ϕ} (η-λ {e = e}) =
  subst₂ (_↪_) (λx ((e ⋯ ϕ ⋯ wkₖ _ id) · ` here refl)
                  ≡⟨ cong₂ (λ ■₁ ■₂ → λx (■₁ · ■₂))
                           (sym (dist-↑-f e ϕ))
                           (sym (id/`/id ⦃ kitᵣ ⦄ (here refl)))⟩
                λx ((e ⋯ᵣ wknᵣ ⋯ (ϕ ↑ _)) · (` here refl ⋯ (ϕ ↑ _))) ∎)
                refl
                η-λ
↪-⋯ᵣ' (ξ-λ t↪*t') = ξ-λ (↪-⋯ᵣ' t↪*t')
↪-⋯ᵣ' (ξ-∀₁ t↪*t') = ξ-∀₁ (↪-⋯ᵣ' t↪*t')
↪-⋯ᵣ' (ξ-∀₂ t↪*t') = ξ-∀₂ (↪-⋯ᵣ' t↪*t')
↪-⋯ᵣ' (ξ-·₁ t↪*t') = ξ-·₁ (↪-⋯ᵣ' t↪*t')
↪-⋯ᵣ' (ξ-·₂ t↪*t') = ξ-·₂ (↪-⋯ᵣ' t↪*t')

↪*-⋯ᵣ' : ∀ {µ₁ µ₂ M} {ϕ : µ₁ →ᵣ µ₂} {t t' : µ₁ ⊢ M} →
  t ↪* t' →
  t ⋯ᵣ ϕ ↪* t' ⋯ᵣ ϕ
↪*-⋯ᵣ' refl = refl
↪*-⋯ᵣ' (step t↪t' t'↪*t'') = step (↪-⋯ᵣ' t↪t') (↪*-⋯ᵣ' t'↪*t'')

↪ₚ→↪* : t ↪ₚ t' → t ↪* t'
↪ₚ→↪* ξ-`                    = refl
↪ₚ→↪* (β-λ {t₁ = t₁} {t₁'} {t₂} {t₂'} t₁↪ₚt₁' t₂↪ₚt₂'') =
  ((λx t₁) · t₂)   ↪*⟨ ξ-·₁* (ξ-λ* (↪ₚ→↪* t₁↪ₚt₁')) ⟩
  ((λx t₁') · t₂)  ↪*⟨ ξ-·₂* (↪ₚ→↪* t₂↪ₚt₂'') ⟩
  ((λx t₁') · t₂') ↪⟨ β-λ ⟩
  (t₁' ⋯ ⦅ t₂' ⦆ₛ) ↪∎
↪ₚ→↪* (η-λ {t' = t'} {t = t} t↪ₚt') =
  λx (wkₛ _ t  · ` here refl) ↪*⟨ ξ-λ* (ξ-·₁* (↪*-⋯ᵣ' (↪ₚ→↪* t↪ₚt'))) ⟩
                           -- Required becaues {!↪ₚ→↪* (↪-⋯ᵣ t↪ₚt')!} is bad for termination checker...
  λx (wkₛ _ t' · ` here refl) ↪⟨ η-λ ⟩
  t'                          ↪∎
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

sem-trans : SemTrans semantics semanticsₚ
sem-trans = record { toₚ = ↪→↪ₚ ; fromₚ = ↪ₚ→↪* }

open SemTrans sem-trans public renaming (toₚ* to ↪*→↪ₚ*; fromₚ* to ↪ₚ*→↪*)
open SemTrans-↪-⋯ sem-traversal public

--------------------------------------------------------------------------------

diamondₚ :
  t ↪ₚ t₁ →
  t ↪ₚ t₂ →
  ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
diamondₚ (β-λ xx xx₁) (β-λ yy yy₁) = {!!}
diamondₚ (β-λ xx xx₁) (ξ-· yy yy₁) = {!!}
diamondₚ (η-λ xx) yy = {!yy!}
diamondₚ (ξ-λ xx) yy = {!!}
diamondₚ (ξ-∀ xx xx₁) yy = {!!}
diamondₚ (ξ-· xx xx₁) yy = {!!}
diamondₚ ξ-` yy = {!!}
diamondₚ ξ-★ yy = {!!}

-- diamondₚ :
--   t ↪ₚ t₁ →
--   t ↪ₚ t₂ →
--   ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
-- diamondₚ ξ-`             ξ-`               = _ , ξ-` , ξ-`
-- diamondₚ (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
--   with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
-- diamondₚ (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (ξ-· (ξ-λ t₁↪t₁'') t₂↪t₂'')
--   with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , (β-λ t₁''↪T₁ t₂''↪T₂)
-- diamondₚ (ξ-λ t↪t') (ξ-λ t↪t'')
--   with diamondₚ t↪t' t↪t''
-- ...  | T , t'↪T , t''↪T
--   = λx T , ξ-λ t'↪T , ξ-λ t''↪T
-- diamondₚ (ξ-∀ t₁↪t₁' t₂↪t₂') (ξ-∀ t₁↪t₁'' t₂↪t₂'')
--   with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = ∀[x∶ T₁ ] T₂ , ξ-∀ t₁'↪T₁ t₂'↪T₂ , ξ-∀ t₁''↪T₁ t₂''↪T₂
-- diamondₚ (ξ-· (ξ-λ t₁↪t₁') t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
--   with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , β-λ t₁'↪T₁ t₂'↪T₂ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
-- diamondₚ (ξ-· t₁↪t₁' t₂↪t₂') (ξ-· t₁↪t₁'' t₂↪t₂'')
--   with diamondₚ t₁↪t₁' t₁↪t₁'' | diamondₚ t₂↪t₂' t₂↪t₂''
-- ...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
--   = T₁ · T₂ , ξ-· t₁'↪T₁ t₂'↪T₂ , ξ-· t₁''↪T₁ t₂''↪T₂
-- diamondₚ ξ-★ ξ-★ = ★ , ξ-★ , ξ-★

open SemTrans-confluence diamondₚ public
  using (stripₚ; confluenceₚ; confluence)
