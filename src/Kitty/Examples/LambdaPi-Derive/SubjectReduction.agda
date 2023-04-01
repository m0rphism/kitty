module Kitty.Examples.LambdaPi-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Examples.LambdaPi-Derive.Confluence
open import Kitty.Examples.LambdaPi-Derive.Closures
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_)

≣-refl : e ≣ e
≣-refl = mk-≣ _ refl refl

≣-sym : e₁ ≣ e₂ → e₂ ≣ e₁
≣-sym (mk-≣ e e₁↪*e e₂↪*e) = mk-≣ e e₂↪*e e₁↪*e

≣-trans : e₁ ≣ e₂ → e₂ ≣ e₃ → e₁ ≣ e₃
≣-trans (mk-≣ e e₁↪*e e₂↪*e) (mk-≣ e' e₂↪*e' e₃↪*e') with confluence e₂↪*e e₂↪*e'
... | e'' , e↪*e'' , e'↪*e'' = mk-≣ e'' (↪*-trans e₁↪*e e↪*e'') (↪*-trans e₃↪*e' e'↪*e'')

_≣σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ≣σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ≣ σ₂ _ x

≣σ-ext : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
  σ₁ ≣σ σ₂ →
  t₁ ≣ t₂ →
  (σ₁ ,ₛ t₁) ≣σ (σ₂ ,ₛ t₂)
≣σ-ext = {!!}

≣σ-⦅_⦆ : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
  t₁ ≣ t₂ →
  ⦅ t₁ ⦆ₛ ≣σ ⦅ t₂ ⦆ₛ
≣σ-⦅ t₁≣t₂ ⦆ = ?

-- Are Ctx's basically Substitutions which don't weaken automatically?
-- Can be represent them as such or even generalize our substitutions?
≣σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
  σ ≣σ σ
≣σ-refl {m = 𝕖} x = ≣-refl

map-≣ :
  ∀ {µ} {µ'} {M}
    {f : µ ⊢ M → µ' ⊢ M}
    (F : ∀ {e e' : µ ⊢ M} → e ↪ e' → f e ↪ f e')
    {e e' : µ ⊢ M}
  → e ≣ e'
  → f e ≣ f e'
map-≣ {f = f} F (mk-≣ e e₁↪*e e₂↪*e) = mk-≣ (f e) (map-↪* F e₁↪*e) (map-↪* F e₂↪*e)

≣-↪ : e ↪ e' → e ≣ e'
≣-↪ e↪e' = mk-≣ _ (embed e↪e') refl

≣-↩ : e' ↪ e → e ≣ e'
≣-↩ e'↪e = mk-≣ _ refl (embed e'↪e)

≣-λ : e ≣ e' → λx e ≣ λx e'
≣-λ = map-≣ ξ-λ

≣-·₁ : e₁ ≣ e₁' → e₁ · e₂ ≣ e₁' · e₂
≣-·₁ = map-≣ ξ-·₁

≣-·₂ : e₂ ≣ e₂' → e₁ · e₂ ≣ e₁ · e₂'
≣-·₂ = map-≣ ξ-·₂

≣-∀₁ : e₁ ≣ e₁' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁' ] e₂
≣-∀₁ = map-≣ ξ-∀₁

≣-∀₂ : e₂ ≣ e₂' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁ ] e₂'
≣-∀₂ = map-≣ ξ-∀₂

≣-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ≣ t' →
  σ ≣σ σ' →
  t ⋯ₛ σ ≣ t' ⋯ₛ σ'
≣-⋯ₛ = {!!}

↪-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
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

↪-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ₛ ϕ ↪ t' ⋯ₛ ϕ
↪-⋯ₛ = ↪-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

≣-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ≣ t' →
  t ⋯ ϕ ≣ t' ⋯ ϕ
≣-⋯ = map-≣ ↪-⋯

-- ≣-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
--   t ≣ t' →
--   t ⋯ₛ ϕ ≣ t' ⋯ₛ ϕ
-- ≣-⋯ₛ = ≣-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

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
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂'
↪-∀-shape (ξ-∀₁ t₁↪t₁') = _ , _ , refl
↪-∀-shape (ξ-∀₂ t₂↪t₂') = _ , _ , refl

↪*-∀-shape :
  ∀[x∶ t₁ ] t₂ ↪* t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂'
↪*-∀-shape refl = _ , _ , refl
↪*-∀-shape (step ∀↪t t↪*t')
  with ↪-∀-shape ∀↪t
... | t₁' , t₂' , refl
  with ↪*-∀-shape t↪*t'
... | t₁'' , t₂'' , refl
  = t₁'' , t₂'' , refl

↪-∀-shape' :
  ∀[x∶ t₁ ] t₂ ↪ t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪-∀-shape' (ξ-∀₁ t₁↪t₁') = _ , _ , refl , embed t₁↪t₁' , refl
↪-∀-shape' (ξ-∀₂ t₂↪t₂') = _ , _ , refl , refl , embed t₂↪t₂'

↪*-∀-shape' :
  ∀[x∶ t₁ ] t₂ ↪* t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪*-∀-shape' refl = _ , _ , refl , refl , refl
↪*-∀-shape' (step ∀↪t t↪*t')
  with ↪-∀-shape' ∀↪t
... | t₁' , t₂' , refl , t₁↪*t₁' , t₂↪*t₂'
  with ↪*-∀-shape' t↪*t'
... | t₁'' , t₂'' , refl , t₁'↪*t₁'' , t₂'↪*t₂''
  = t₁'' , t₂'' , refl , ↪*-trans t₁↪*t₁' t₁'↪*t₁'' , ↪*-trans t₂↪*t₂' t₂'↪*t₂''

invert-≣-λ :
  ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
  t₁ ≣ t₁' × t₂ ≣ t₂'
invert-≣-λ (mk-≣ t ∀₁↪*t ∀₂↪*t)
  with ↪*-∀-shape' ∀₁↪*t | ↪*-∀-shape' ∀₂↪*t
... | T₁ , T₂ , refl , t₁↪*T₁ , t₂↪*T₂ | .T₁ , .T₂ , refl , t₁'↪*T₁ , t₂'↪*T₂
  = mk-≣ T₁ t₁↪*T₁ t₁'↪*T₁ , mk-≣ T₂ t₂↪*T₂ t₂'↪*T₂

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢t ⊢e)   (ξ-λ e↪e')    = ⊢λ ⊢t (subject-reduction ⊢e e↪e')
subject-reduction {Γ = Γ} (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₁ t₁↪t₁') = ⊢∀ (subject-reduction ⊢t₁ t₁↪t₁')
                                                          (≣*-pres (≣*-ext (≣*-refl {Γ = Γ}) (≣-↪ t₁↪t₁')) ⊢t₂)
subject-reduction (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₂ t₂↪t₂') = ⊢∀ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
subject-reduction (⊢· {e₂ = e₂} ⊢e₁ ⊢e₂) β-λ
 with invert-⊢λ ⊢e₁
... | t₁ , t₂ , ∀≣∀ , ⊢t₁ , ⊢e₁
 with invert-≣-λ ∀≣∀
... | t₁≣t₁' , t₂≣t₂'
 =  ⊢≣ (≣-sym (≣-⋯ₛ t₂≣t₂' (≣σ-refl {σ = ⦅ e₂ ⦆ₛ}))) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢≣ t₁≣t₁' ⊢e₂ ⦆ₛ) -- ⊢≣ {!≣-sym eq!} {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ!}
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = ⊢≣ (≣-⋯ₛ ≣-refl (≣σ-ext (≣σ-refl {σ = idₛ}) (≣-↪ e₂↪e₂'))) (⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂'))
subject-reduction (⊢≣ t≣t' ⊢e) e↪e'          = ⊢≣ t≣t' (subject-reduction ⊢e e↪e')
