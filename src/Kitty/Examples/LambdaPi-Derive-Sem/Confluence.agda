module Kitty.Examples.LambdaPi-Derive-Sem.Confluence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
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
↪-⋯ {ϕ = ϕ} {ϕ'} (ξ-` {x = x}) ϕ↪ϕ' = ↪/id' {ϕ₁ = ϕ} {ϕ₂ = ϕ'} (ϕ↪ϕ' x)
↪-⋯ {ϕ = ϕ} {ϕ'} (β-λ {t₁' = t₁'} {t₂' = t₂'} t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = subst (_ ↪ₚ_) (sym (dist-⦅⦆ₛ-⋯ t₁' t₂' ϕ'))
                                                                              (β-λ (↪-⋯ t₁↪ₚt₁' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
                                                                                   (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ'))
↪-⋯ (ξ-λ t↪t')       ϕ↪ϕ' = ξ-λ (↪-⋯ t↪t' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = ξ-∀ (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' (≡ϕ/↪ϕ-↑ ϕ↪ϕ'))
↪-⋯ (ξ-· t₁↪ₚt₁' t₂↪ₚt₂') ϕ↪ϕ' = ξ-· (↪-⋯ t₁↪ₚt₁' ϕ↪ϕ') (↪-⋯ t₂↪ₚt₂' ϕ↪ϕ')
↪-⋯ ξ-★                   ϕ↪ϕ' = ξ-★

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
↪→↪ₚ (ξ-λ t↪t')    = ξ-λ (↪→↪ₚ t↪t')
↪→↪ₚ (ξ-∀₁ t₁↪t₁') = ξ-∀ (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-∀₂ t₂↪t₂') = ξ-∀ ↪ₚ-refl (↪→↪ₚ t₂↪t₂')
↪→↪ₚ (ξ-·₁ t₁↪t₁') = ξ-· (↪→↪ₚ t₁↪t₁') ↪ₚ-refl
↪→↪ₚ (ξ-·₂ t₂↪t₂') = ξ-· ↪ₚ-refl (↪→↪ₚ t₂↪t₂')

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

sem-trans : SemTrans semantics semanticsₚ
sem-trans = record { toₚ = ↪→↪ₚ ; fromₚ = ↪ₚ→↪* }

open SemTrans sem-trans public renaming (toₚ* to ↪*→↪ₚ*; fromₚ* to ↪ₚ*→↪*)
open SemTrans-↪-⋯ sem-traversal public

--------------------------------------------------------------------------------

↪ₚσ-⋯-⦅⦆ : ∀ {µ M} {t₁ t₁' : (µ ▷ 𝕖) ⊢ M}  {t₂ t₂' : µ ⊢ 𝕖} →
  t₁ ↪ₚ t₁' →
  t₂ ↪ₚ t₂' →
  t₁ ⋯ ⦅ t₂ ⦆ₛ ↪ₚ t₁' ⋯ ⦅ t₂' ⦆ₛ
↪ₚσ-⋯-⦅⦆ t₁↪ₚt₁' t₂↪ₚt₂' = ↪ₚσ-⋯ t₁↪ₚt₁' Semₚ.↪σ-⦅ t₂↪ₚt₂' ⦆

diamond :
  t ↪ₚ t₁ →
  t ↪ₚ t₂ →
  ∃[ t' ] t₁ ↪ₚ t' × t₂ ↪ₚ t'
diamond ξ-`             ξ-`               = _ , ξ-` , ξ-`
diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (β-λ t₁↪t₁'' t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
diamond (β-λ {t₁' = t₁'} t₁↪t₁' t₂↪t₂') (ξ-· (ξ-λ t₁↪t₁'') t₂↪t₂'')
  with diamond t₁↪t₁' t₁↪t₁'' | diamond t₂↪t₂' t₂↪t₂''
...  | T₁ , t₁'↪T₁ , t₁''↪T₁  | T₂ , t₂'↪T₂ , t₂''↪T₂
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , ↪ₚσ-⋯ t₁'↪T₁ Semₚ.↪σ-⦅ t₂'↪T₂ ⦆ , (β-λ t₁''↪T₁ t₂''↪T₂)
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
  = T₁ ⋯ₛ ⦅ T₂ ⦆ₛ , β-λ t₁'↪T₁ t₂'↪T₂ , ↪ₚσ-⋯ t₁''↪T₁ Semₚ.↪σ-⦅ t₂''↪T₂ ⦆
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
