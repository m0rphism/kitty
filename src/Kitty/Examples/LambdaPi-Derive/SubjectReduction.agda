module Kitty.Examples.LambdaPi-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)

↪-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ ϕ ↪ t' ⋯ ϕ
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(λx _)}       {.(λx _)}       (ξ-λ t↪t')  = ξ-λ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(∀[x∶ _ ] _)} {.(∀[x∶ _ ] _)} (ξ-∀₁ t↪t') = ξ-∀₁ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(∀[x∶ _ ] _)} {.(∀[x∶ _ ] _)} (ξ-∀₂ t↪t') = ξ-∀₂ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(_ · _)}      {.(_ · _)}      (ξ-·₁ t↪t') = ξ-·₁ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ} {.(_ · _)}      {.(_ · _)}      (ξ-·₂ t↪t') = ξ-·₂ (↪-⋯ t↪t')
↪-⋯ {µ₁} {µ₂} {.𝕖} {ϕ}
    {.((λx e₁) · e₂)}
    {.(e₁ ⋯ ⦅ e₂ ⦆ₛ)}
    (β-λ {e₁ = e₁} {e₂ = e₂}) =
  subst (((λx e₁) · e₂) ⋯ ϕ ↪_)
        (sym (dist-⦅⦆ₛ-⋯ e₁ e₂ ϕ))
        (β-λ {e₁ = e₁ ⋯ (ϕ ↑ 𝕖)} {e₂ = e₂ ⋯ ϕ})

≣-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ≣ t' →
  t ⋯ ϕ ≣ t' ⋯ ϕ
≣-⋯ = ≣-f ↪-⋯

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

-- _↪**_ : ∀ {µ} (Γ₁ Γ₂ : Ctx µ) → Set
-- Γ₁ ↪** Γ₂ = ∀ {m} (x : _ ∋ m) → Γ₁ x ↪* Γ₂ x

-- ↪**-ext : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
--   Γ₁ ↪** Γ₂ →
--   (Γ₁ ▶ t) ↪** (Γ₂ ▶ t)
-- ↪**-ext {M = 𝕖} ↪Γ (here refl) = refl
-- ↪**-ext {M = M} ↪Γ (there x) = ↪Γ x

-- ↪**-pres : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
--   Γ₁ ↪** Γ₂ →
--   Γ₁ ⊢ e ∶ t →
--   Γ₂ ⊢ e ∶ t
-- ↪**-pres {M = 𝕖} Γ↪ (⊢` {x = x} refl)       = {!⊢↪* {!Γ↪ x!} (⊢` refl)!}
-- ↪**-pres Γ↪ (⊢λ ⊢t₁ ⊢e)  = {!!}
-- ↪**-pres Γ↪ (⊢∀ ⊢t₁ ⊢t₂) = {!!}
-- ↪**-pres Γ↪ (⊢· ⊢e₁ ⊢e₂) = {!!}
-- ↪**-pres Γ↪ ⊢★           = ⊢★
-- ↪**-pres Γ↪ (⊢≣ t≣t' ⊢e) = {!!}

_≣σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ≣σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ≣ σ₂ _ x

-- Are Ctx's basically Substitutions which don't weaken automatically?
-- Can be represent them as such or even generalize our substitutions?
≣σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
  σ ≣σ σ
≣σ-refl {m = 𝕖} x = ≣-refl

_≣*_ : ∀ {µ} (Γ₁ Γ₂ : Ctx µ) → Set
Γ₁ ≣* Γ₂ = ∀ {m} (x : _ ∋ m) → Γ₁ x ≣ Γ₂ x

≣*-refl : ∀ {µ} {Γ : Ctx µ} →
  Γ ≣* Γ
≣*-refl {m = 𝕖} x = ≣-refl

≣*-ext : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {t₁ t₂ : µ ⊢ M} →
  Γ₁ ≣* Γ₂ →
  t₁ ≣ t₂ →
  (Γ₁ ▶ t₁) ≣* (Γ₂ ▶ t₂)
≣*-ext {M = 𝕖} Γ₁≣Γ₂ t₁≣t₂ (here refl) = t₁≣t₂
≣*-ext {M = M} Γ₁≣Γ₂ t₁≣t₂ (there x)   = Γ₁≣Γ₂ x

≣*-↑ : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {t : µ ⊢ M} →
  Γ₁ ≣* Γ₂ →
  (Γ₁ ▶ t) ≣* (Γ₂ ▶ t)
≣*-↑ {M = 𝕖} ≣Γ = ≣*-ext ≣Γ ≣-refl

≣*-pres : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
  Γ₁ ≣* Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ e ∶ t
≣*-pres {M = 𝕖} Γ≣ (⊢` {x = x} refl) = ⊢≣ {!Γ≣ x!} (⊢` refl)
≣*-pres Γ≣ (⊢λ ⊢t₁ ⊢e)  = {!!}
≣*-pres Γ≣ (⊢∀ ⊢t₁ ⊢t₂) = {!!}
≣*-pres Γ≣ (⊢· ⊢e₁ ⊢e₂) = {!!}
≣*-pres Γ≣ ⊢★           = ⊢★
≣*-pres Γ≣ (⊢≣ t≣t' ⊢e) = {!!}

open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)

invert-⊢λ : ∀ {µ} {Γ : Ctx µ} {e : (µ ▷ 𝕖) ⊢ 𝕖} {t : µ ⊢ 𝕖} →
    Γ ⊢ λx e ∶ t →
    ∃[ t₁ ] ∃[ t₂ ]
      t ≣ ∀[x∶ t₁ ] t₂ ×
      Γ ⊢ t₁ ∶ ★ ×
      Γ ▶ t₁ ⊢ e ∶ t₂
invert-⊢λ (⊢λ ⊢t₁ ⊢e) = _ , _ , ≣-refl , ⊢t₁ , ⊢e
invert-⊢λ (⊢≣ t≣t' ⊢e) with invert-⊢λ ⊢e
... | t₁ , t₂ , t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e = t₁ , t₂ , ≣-trans (≣-sym t≣t') t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e

-- invert-↪-λ :
--   ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁' ] t₂' →
--   t₁ ↪* t₁' × t₂ ↪* t₂'
-- invert-↪-λ refl = refl , refl
-- invert-↪-λ (step (ξ-∀₁ x) st) = {!!}
-- invert-↪-λ (step (ξ-∀₂ x) st) = {!!}

open import Data.Sum using (_⊎_; inj₁; inj₂)

invert-↪-λ :
  ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂' →
  t₁ ↪ t₁' ⊎ t₂ ↪ t₂'
invert-↪-λ (ξ-∀₁ t₁↪t₁') = inj₁ t₁↪t₁'
invert-↪-λ (ξ-∀₂ t₂↪t₂') = inj₂ t₂↪t₂'

-- invert-≣-λ'' :
--   ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
--   (λx e₁) · e₂ ↪ ∀[x∶ t₁' ] t₂' →

invert-≣-λ' :
  t ≣ t' →
  t ≡ ∀[x∶ t₁ ] t₂ →
  t' ≡ ∀[x∶ t₁' ] t₂' →
  t₁ ≣ t₁' × t₂ ≣ t₂'
invert-≣-λ' ≣-refl refl refl         = ≣-refl , ≣-refl
invert-≣-λ' (≣-step-↪ (ξ-∀₁ t₁↪t₁'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↪ t₁↪t₁'') t₁''≣t₁' , t₂≣t₂'
invert-≣-λ' (≣-step-↪ (ξ-∀₂ t₂↪t₂'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↪ t₂↪t₂'') t₂''≣t₂'
invert-≣-λ' (≣-step-↩ (ξ-∀₁ t₁↩t₁'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↩ t₁↩t₁'') t₁''≣t₁' , t₂≣t₂'
invert-≣-λ' (≣-step-↩ (ξ-∀₂ t₂↩t₂'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↩ t₂↩t₂'') t₂''≣t₂'
invert-≣-λ' (≣-step-↩ β-λ e₂≣∀) eq refl = {!!}
-- ∀[x∶ t₁ ] t₂  ↩  (λx e₁) · e₂  ≣  ∀[x∶ t₁' ] t₂'

-- invert-≣-λ' (≣-step-↩ (β-λ {e₁ = ` x}) e₂≣∀) eq refl = {!!}
-- invert-≣-λ' (≣-step-↩ (β-λ {e₁ = ∀[x∶ e₁ ] e₂}) e₂≣∀) refl refl = {!!}

invert-≣-λ :
  ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
  t₁ ≣ t₁' × t₂ ≣ t₂'
invert-≣-λ ≣-refl          = ≣-refl , ≣-refl
invert-≣-λ (≣-step-↪ (ξ-∀₁ t₁↪t₁'') ∀≣∀) with invert-≣-λ ∀≣∀
... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↪ t₁↪t₁'') t₁''≣t₁' , t₂≣t₂'
invert-≣-λ (≣-step-↪ (ξ-∀₂ t₂↪t₂'') ∀≣∀) with invert-≣-λ ∀≣∀
... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↪ t₂↪t₂'') t₂''≣t₂'
invert-≣-λ (≣-step-↩ ∀↩e₂ e₂≣∀) = {!eq!}
-- invert-≣-λ (≣-step-↩ (ξ-∀₁ t₁↩t₁'') ∀≣∀) with invert-≣-λ ∀≣∀
-- ... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↩ t₁↩t₁'') t₁''≣t₁' , t₂≣t₂'
-- invert-≣-λ (≣-step-↩ (ξ-∀₂ t₂↩t₂'') ∀≣∀) with invert-≣-λ ∀≣∀
-- ... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↩ t₂↩t₂'') t₂''≣t₂'

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢t ⊢e)   (ξ-λ e↪e')    = ⊢λ ⊢t (subject-reduction ⊢e e↪e')
subject-reduction {Γ = Γ} (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₁ t₁↪t₁') = ⊢∀ (subject-reduction ⊢t₁ t₁↪t₁')
                                                          (≣*-pres (≣*-ext (≣*-refl {Γ = Γ}) (≣-↪ t₁↪t₁')) ⊢t₂)
subject-reduction (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₂ t₂↪t₂') = ⊢∀ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
-- subject-reduction (⊢· (⊢λ ⊢t ⊢e₁) ⊢e₂) β-λ = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆
-- subject-reduction (⊢· (⊢≣ x ⊢e₁) ⊢e₂) β-λ = {!!}
subject-reduction (⊢· ⊢e₁ ⊢e₂) β-λ with invert-⊢λ ⊢e₁
... | t₁ , t₂ , ∀≣∀ , ⊢t₁ , ⊢e₁ = {!⊢≣ (≣-sym ∀≣∀) (⊢λ ⊢t₁ ⊢e₁) !} -- ⊢≣ {!≣-sym eq!} {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ!}
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = {!⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')!}
subject-reduction (⊢≣ t≣t' ⊢e) e↪e'          = ⊢≣ t≣t' (subject-reduction ⊢e e↪e')
