module Kitty.Examples.LambdaPi-Derive-Sem.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive-Sem.Definitions
open import Kitty.Examples.LambdaPi-Derive-Sem.Confluence
open import Kitty.Util.Closures
open import Kitty.Semantics.ISemantics compose-traversal ctx-repr
open import Kitty.Typing.IKit compose-traversal ctx-repr iterms
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_; proj₁; proj₂)

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
⊢≣ t≣t' ⊢e ⊢⋯ ⊢ϕ = ⊢≣ (≣-⋯₁ t≣t') (⊢e ⊢⋯ ⊢ϕ)

open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

--------------------------------------------------------------------------------

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
