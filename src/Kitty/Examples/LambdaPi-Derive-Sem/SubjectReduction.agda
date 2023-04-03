module Kitty.Examples.LambdaPi-Derive-Sem.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive-Sem.Definitions
open import Kitty.Examples.LambdaPi-Derive-Sem.Confluence
open import Kitty.Util.Closures
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_; proj₁; proj₂)

open ReflexiveTransitiveClosure using (refl; step)

↪ₚ*σ-⋯' : ∀ {µ₁ µ₂ m} {t t' : µ₁ ⊢ m} {σ σ' : µ₁ →ₛ µ₂} →
  t ↪ₚ* t' →
  σ ↪ₚσ σ' →
  t ⋯ σ ↪ₚ* t' ⋯ σ'
↪ₚ*σ-⋯' {t = t} refl          σ↪ₚσ' = step (↪ₚσ-⋯ {t = t} ↪ₚ-refl σ↪ₚσ') refl
↪ₚ*σ-⋯' (step t↪ₚt' t'↪ₚ*t'') σ↪ₚσ' = step (↪ₚσ-⋯ t↪ₚt' λ x → ↪ₚ-refl) (↪ₚ*σ-⋯' t'↪ₚ*t'' σ↪ₚσ')

↪ₚ*σ-⋯ : ∀ {µ₁ µ₂ m} {t t' : µ₁ ⊢ m} {σ σ' : µ₁ →ₛ µ₂} →
  t ↪ₚ* t' →
  σ ↪ₚσ* σ' →
  t ⋯ σ ↪ₚ* t' ⋯ σ'
↪ₚ*σ-⋯ t↪ₚ*t' refl = ↪ₚ*σ-⋯' t↪ₚ*t' (λ x → ↪ₚ-refl)
↪ₚ*σ-⋯ {t = t} t↪ₚ*t' (step {a₂ = σ'} σ↪ₚσ' σ'↪ₚ*σ'') = step {a₂ = t ⋯ σ'} (↪ₚσ-⋯ {t = t} ↪ₚ-refl σ↪ₚσ') (↪ₚ*σ-⋯ t↪ₚ*t' σ'↪ₚ*σ'')

-- ↪σ-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
--   t ↪ t' →
--   σ ↪σ σ' →
--   t ⋯ₛ σ ↪* t' ⋯ₛ σ'
-- ↪σ-⋯ₛ t↪t' σ↪σ' = ↪ₚ→↪* (↪ₚσ-⋯ (↪→↪ₚ t↪t') (λ x → ↪→↪ₚ (σ↪σ' x)))

↪*-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪* t' →
  σ ↪*σ σ' →
  t ⋯ₛ σ ↪* t' ⋯ₛ σ'
↪*-⋯ₛ t↪*t' σ↪*σ' = ↪ₚ*→↪* (↪ₚ*σ-⋯ (↪*→↪ₚ* t↪*t') (Semₚ.[↪*σ]→[↪σ*] (λ x → ↪*→↪ₚ* (σ↪*σ' x)))) 

≣-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ≣ t' →
  σ ≣σ σ' →
  t ⋯ₛ σ ≣ t' ⋯ₛ σ'
≣-⋯ₛ (mk-≣ T t↪*T t'↪*T) σ≣σ'
 with ≣σ→↪*σ σ≣σ'
... | σ'' , σ↪*σ'' , σ'↪*σ''
 = mk-≣ _ (↪*-⋯ₛ t↪*T σ↪*σ'') (↪*-⋯ₛ t'↪*T σ'↪*σ'')

--------------------------------------------------------------------------------

↪-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ ϕ ↪ t' ⋯ ϕ
↪-⋯ (ξ-λ t↪t')  = ξ-λ (↪-⋯ t↪t')
↪-⋯ (ξ-∀₁ t↪t') = ξ-∀₁ (↪-⋯ t↪t')
↪-⋯ (ξ-∀₂ t↪t') = ξ-∀₂ (↪-⋯ t↪t')
↪-⋯ (ξ-·₁ t↪t') = ξ-·₁ (↪-⋯ t↪t')
↪-⋯ (ξ-·₂ t↪t') = ξ-·₂ (↪-⋯ t↪t')
↪-⋯ {ϕ = ϕ} (β-λ {e₁ = e₁} {e₂ = e₂}) =
  subst (((λx e₁) · e₂) ⋯ ϕ ↪_)
        (sym (dist-⦅⦆ₛ-⋯ e₁ e₂ ϕ))
        (β-λ {e₁ = e₁ ⋯ (ϕ ↑ 𝕖)} {e₂ = e₂ ⋯ ϕ})

-- ↪-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
--   t ↪ t' →
--   t ⋯ₛ ϕ ↪ t' ⋯ₛ ϕ
-- ↪-⋯ₛ = ↪-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

↪-⋯ᵣ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ᵣ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ᵣ ϕ ↪ t' ⋯ᵣ ϕ
↪-⋯ᵣ = ↪-⋯ where instance _ = kitᵣ; _ = kittᵣ; _ = ckitₛᵣ; _ = ckitᵣ

≣-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ≣ t' →
  t ⋯ ϕ ≣ t' ⋯ ϕ
≣-⋯ = map-≣ ↪-⋯

--------------------------------------------------------------------------------

_⊢⋯_ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x      ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢λ ⊢t₁ ⊢e  ⊢⋯ ⊢ϕ = ⊢λ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢∀ ⊢t₁ ⊢t₂ ⊢⋯ ⊢ϕ = ⊢∀ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢t₂ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
_⊢⋯_ {Γ₂ = Γ₂} {e = e₁ · e₂} {ϕ = ϕ} (⊢· {t₁ = t₁} {t₂ = t₂} ⊢e₁ ⊢e₂) ⊢ϕ =
  Γ₂ ⊢ e₁ · e₂ ⋯ ϕ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ ⋯ ϕ
    by subst (Γ₂ ⊢ (e₁ · e₂) ⋯ ϕ ∶_)
             ((t₂ ⋯ (ϕ ↑ 𝕖)) ⋯ₛ ⦅ e₂ ⋯ ϕ ⦆ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ t₂ e₂ ϕ) ⟩
              t₂ ⋯ₛ ⦅ e₂ ⦆ₛ ⋯ ϕ             ∎)
             (⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ))
⊢★         ⊢⋯ ⊢ϕ = ⊢★
⊢≣ t≣t' ⊢e ⊢⋯ ⊢ϕ = ⊢≣ (≣-⋯ t≣t') (⊢e ⊢⋯ ⊢ϕ)

open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

--------------------------------------------------------------------------------

↪-wk : {t₁ t₂ : µ ⊢ M} →
  t₁ ↪ t₂ →
  wk m t₁ ↪ wk m t₂
↪-wk t₁↪t₂ = ↪-⋯ᵣ t₁↪t₂

≣-wk : {t₁ t₂ : µ ⊢ M} →
  t₁ ≣ t₂ →
  wk m t₁ ≣ wk m t₂
≣-wk = map-≣ ↪-wk

≣*-wk-telescope :
  Γ₁ x ≣ Γ₂ x →
  wk-telescope Γ₁ x ≣ wk-telescope Γ₂ x
≣*-wk-telescope {x = here refl} eq = ≣-wk eq
≣*-wk-telescope {Γ₁ = Γ₁} {x = there x} {Γ₂ = Γ₂}  eq = ≣-wk (≣*-wk-telescope {Γ₁ = λ x → Γ₁ (there x)}
                                                                              {Γ₂ = λ x → Γ₂ (there x)}
                                                                              eq)

≣*-pres : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
  Γ₁ ≣* Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ e ∶ t
≣*-pres {Γ₁ = Γ₁} {Γ₂ = Γ₂} {M = 𝕖} Γ≣ (⊢` {x = x} refl) = ⊢≣ (≣-sym (≣*-wk-telescope {Γ₁ = Γ₁} {Γ₂ = Γ₂} (Γ≣ x))) (⊢` refl)
≣*-pres Γ≣ (⊢λ ⊢t₁ ⊢e)  = ⊢λ (≣*-pres Γ≣ ⊢t₁) (≣*-pres (≣*-↑ Γ≣) ⊢e)
≣*-pres Γ≣ (⊢∀ ⊢t₁ ⊢t₂) = ⊢∀ (≣*-pres Γ≣ ⊢t₁) (≣*-pres (≣*-↑ Γ≣) ⊢t₂)
≣*-pres Γ≣ (⊢· ⊢e₁ ⊢e₂) = ⊢· (≣*-pres Γ≣ ⊢e₁) (≣*-pres Γ≣ ⊢e₂)
≣*-pres Γ≣ ⊢★           = ⊢★
≣*-pres Γ≣ (⊢≣ t≣t' ⊢e) = ⊢≣ t≣t' (≣*-pres Γ≣ ⊢e)

--------------------------------------------------------------------------------

open ↪-WithConfluence confluence public

invert-⊢λ : ∀ {µ} {Γ : Ctx µ} {e : (µ ▷ 𝕖) ⊢ 𝕖} {t : µ ⊢ 𝕖} →
    Γ ⊢ λx e ∶ t →
    ∃[ t₁ ] ∃[ t₂ ]
      t ≣ ∀[x∶ t₁ ] t₂ ×
      Γ ⊢ t₁ ∶ ★ ×
      Γ ▶ t₁ ⊢ e ∶ t₂
invert-⊢λ (⊢λ ⊢t₁ ⊢e) = _ , _ , ≣-refl , ⊢t₁ , ⊢e
invert-⊢λ (⊢≣ t≣t' ⊢e) with invert-⊢λ ⊢e
... | t₁ , t₂ , t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e = t₁ , t₂ , ≣-trans (≣-sym t≣t') t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e

↪-∀-shape :
  ∀[x∶ t₁ ] t₂ ↪ t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪-∀-shape (ξ-∀₁ t₁↪t₁') = _ , _ , refl , ↪*-embed t₁↪t₁' , refl
↪-∀-shape (ξ-∀₂ t₂↪t₂') = _ , _ , refl , refl , ↪*-embed t₂↪t₂'

↪*-∀-shape :
  ∀[x∶ t₁ ] t₂ ↪* t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪*-∀-shape refl = _ , _ , refl , refl , refl
↪*-∀-shape (step ∀↪t t↪*t')
  with ↪-∀-shape ∀↪t
...  | t₁' , t₂' , refl , t₁↪*t₁' , t₂↪*t₂'
  with ↪*-∀-shape t↪*t'
...  | t₁'' , t₂'' , refl , t₁'↪*t₁'' , t₂'↪*t₂''
  = t₁'' , t₂'' , refl , ↪*-trans t₁↪*t₁' t₁'↪*t₁'' , ↪*-trans t₂↪*t₂' t₂'↪*t₂''

invert-≣-λ :
  ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
  t₁ ≣ t₁' × t₂ ≣ t₂'
invert-≣-λ (mk-≣ t ∀₁↪*t ∀₂↪*t)
  with ↪*-∀-shape ∀₁↪*t                | ↪*-∀-shape ∀₂↪*t
... | T₁ , T₂ , refl , t₁↪*T₁ , t₂↪*T₂ | .T₁ , .T₂ , refl , t₁'↪*T₁ , t₂'↪*T₂
  = mk-≣ T₁ t₁↪*T₁ t₁'↪*T₁ , mk-≣ T₂ t₂↪*T₂ t₂'↪*T₂

--------------------------------------------------------------------------------

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢t ⊢e)             (ξ-λ e↪e')    = ⊢λ ⊢t (subject-reduction ⊢e e↪e')
subject-reduction {Γ = Γ} (⊢∀ ⊢t₁ ⊢t₂)   (ξ-∀₁ t₁↪t₁') = ⊢∀ (subject-reduction ⊢t₁ t₁↪t₁')
                                                            (≣*-pres (≣*-ext (≣*-refl {Γ = Γ}) (≣-↪ t₁↪t₁')) ⊢t₂)
subject-reduction (⊢∀ ⊢t₁ ⊢t₂)           (ξ-∀₂ t₂↪t₂') = ⊢∀ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
subject-reduction (⊢· {e₂ = e₂} ⊢e₁ ⊢e₂) β-λ           with invert-⊢λ ⊢e₁
...                                                       | t₁ , t₂ , ∀≣∀ , ⊢t₁ , ⊢e₁
                                                       with invert-≣-λ ∀≣∀
...                                                       | t₁≣t₁' , t₂≣t₂'
                                                       =  ⊢≣ (≣-sym (≣-⋯ₛ t₂≣t₂' (≣σ-refl {σ = ⦅ e₂ ⦆ₛ})))
                                                             (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢≣ t₁≣t₁' ⊢e₂ ⦆ₛ)
subject-reduction (⊢· ⊢e₁ ⊢e₂)           (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· {t₂ = t₂} ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = ⊢≣ (≣-⋯ₛ (≣-refl {t = t₂}) ≣σ-⦅ ≣-↩ e₂↪e₂' ⦆)
                                                            (⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂'))
subject-reduction (⊢≣ t≣t' ⊢e)           e↪e'          = ⊢≣ t≣t' (subject-reduction ⊢e e↪e')
