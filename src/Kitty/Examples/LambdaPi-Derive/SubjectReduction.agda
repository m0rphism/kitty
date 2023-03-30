module Kitty.Examples.LambdaPi-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_ ; _,_)

↪*-trans : t₁ ↪* t₂ → t₂ ↪* t₃ → t₁ ↪* t₃
↪*-trans refl b = b
↪*-trans (step x a) b = step x (↪*-trans a b)

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

↪*-⋯ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
    ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
    ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪* t' →
  t ⋯ ϕ ↪* t' ⋯ ϕ
↪*-⋯ refl = refl
↪*-⋯ (step t↪t' t'↪*t'') = step (↪-⋯ t↪t') (↪*-⋯ t'↪*t'')

↪-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ₛ ϕ ↪ t' ⋯ₛ ϕ
↪-⋯ₛ = ↪-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

↪*-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪* t' →
  t ⋯ₛ ϕ ↪* t' ⋯ₛ ϕ
↪*-⋯ₛ = ↪*-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

≣-sym : e₁ ≣ e₂ → e₂ ≣ e₁
≣-sym (mk-≣ e e₁↪*e e₂↪*e) = mk-≣ e e₂↪*e e₁↪*e

ξ-λ* :
  e ↪* e' →
  λx e ↪* λx e'
ξ-λ* = {!!}

ξ-∀₁* :
  t₁ ↪* t₁' →
  ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁' ] t₂
ξ-∀₁* = {!!}

ξ-∀₂* :
  t₂ ↪* t₂' →
  ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁ ] t₂'
ξ-∀₂* = {!!}

ξ-·₁* :
  e₁ ↪* e₁' →
  e₁ · e₂ ↪* e₁' · e₂
ξ-·₁* = {!!}

ξ-·₂* :
  e₂ ↪* e₂' →
  e₁ · e₂ ↪* e₁ · e₂'
ξ-·₂* = {!!}

↪-det : e ↪ e₁ → e ↪ e₂ → ∃[ e' ] (e₁ ↪* e' × e₂ ↪* e')
↪-det β-λ β-λ = _ , refl , refl
↪-det (β-λ {e₁ = e₁} {e₂ = e₂}) (ξ-·₁ {e₁' = λx e₁'} (ξ-λ e₁↪e₁')) = e₁' ⋯ₛ ⦅ e₂ ⦆ₛ , step (↪-⋯ₛ e₁↪e₁') refl  , step β-λ refl
↪-det (β-λ {e₁ = e₁} {e₂ = e₂}) (ξ-·₂ {e₂' = e₂'} e₂↪e₂')          = e₁ ⋯ₛ ⦅ e₂' ⦆ₛ , {!!} , step β-λ refl
↪-det (ξ-λ x) (ξ-λ y) with ↪-det x y
... | e' , x' , y' = _ , ξ-λ* x' , ξ-λ* y'
↪-det (ξ-∀₁ {t₁ = t₁} {t₁' = t₁'} {t₂ = t₂} t₁↪t₁') (ξ-∀₁ {t₁' = t₁''} t₁↪t₁'') with ↪-det t₁↪t₁' t₁↪t₁''
... | e' , x' , y' = _ , ξ-∀₁* x' , ξ-∀₁* y'
↪-det (ξ-∀₁ {t₁ = t₁} {t₁' = t₁'} {t₂ = t₂} t₁↪t₁') (ξ-∀₂ {t₂' = t₂'} t₂↪t₂') = ∀[x∶ t₁' ] t₂' , step (ξ-∀₂ t₂↪t₂') refl
                                                                                               , step (ξ-∀₁ t₁↪t₁') refl
↪-det (ξ-∀₂ {t₂ = t₂} {t₂' = t₂'} {t₁ = t₁} t₂↪t₂') (ξ-∀₁ {t₁' = t₁'} t₁↪t₁') = ∀[x∶ t₁' ] t₂' , step (ξ-∀₁ t₁↪t₁') refl
                                                                                               , step (ξ-∀₂ t₂↪t₂') refl
↪-det (ξ-∀₂ {t₂ = t₂} {t₂' = t₂'} {t₁ = t₁} t₂↪t₂') (ξ-∀₂ {t₂' = t₂''} t₂↪t₂'') with ↪-det t₂↪t₂' t₂↪t₂''
... | e' , x' , y' = _ , ξ-∀₂* x' , ξ-∀₂* y'
↪-det (ξ-·₁ (ξ-λ x)) β-λ = _ , step β-λ refl , step (↪-⋯ₛ x) refl
↪-det (ξ-·₁ x) (ξ-·₁ y) with ↪-det x y
... | e' , x' , y' = _ , ξ-·₁* x' , ξ-·₁* y'
↪-det (ξ-·₁ x) (ξ-·₂ y) = _ , step (ξ-·₂ y) refl , step (ξ-·₁ x) refl
↪-det (ξ-·₂ x) β-λ = _ , step β-λ refl , {!!}
↪-det (ξ-·₂ x) (ξ-·₁ y) = _ , step (ξ-·₁ y) refl , step (ξ-·₂ x) refl
↪-det (ξ-·₂ x) (ξ-·₂ y) with ↪-det x y
... | e' , x' , y' = _ , ξ-·₂* x' , ξ-·₂* y'

-- data _↪*'_ : µ ⊢ M → µ ⊢ M → Set where
--   refl :
--     t ↪*' t
--   step :
--     t₁ ↪*'  t₂ →
--     t₂ ↪ t₃ →
--     t₁ ↪*' t₃

-- ↪*'-trans :
--     t₁ ↪*' t₂ →
--     t₂ ↪*' t₃ →
--     t₁ ↪*' t₃
-- ↪*'-trans = {!!}

-- ↪*-to-↪*' :
--     t₁ ↪* t₂ →
--     t₁ ↪*' t₂
-- ↪*-to-↪*' refl = refl
-- ↪*-to-↪*' (step x y) = ↪*'-trans (step refl x) (↪*-to-↪*' y)

-- ↪*'-to-↪* :
--     t₁ ↪*' t₂ →
--     t₁ ↪* t₂
-- ↪*'-to-↪* refl = refl
-- ↪*'-to-↪* (step y x) = ↪*-trans (↪*'-to-↪* y) (step x refl)

-- ↪*-det' : e ↪*' e₁ → e ↪*' e₂ → ∃[ e' ] (e₁ ↪*' e' × e₂ ↪*' e')
-- ↪*-det' refl                       e↪*e₂ = _ , e↪*e₂ , refl
-- ↪*-det' e↪*e₁@(step e↪*e₁' e₁'↪e₁) refl = _ , refl , e↪*e₁
-- ↪*-det' xe↪*e₁@(step e↪*e₁' e₁'↪e₁)       (step e↪*e₂' e₂'↪e₂)
-- --   with ↪*-det' e↪*e₁' e↪*e₂'
-- -- ... | e' , e₁'↪*e' , e₂'↪*e'
--   with ↪*-det' e↪*e₁' (step e↪*e₂' e₂'↪e₂)
-- ... | E' , e₁'↪*E' , e₂↪*E'
--   with ↪*-det' xe↪*e₁ e↪*e₂'
-- ... | F' , e₁↪*F' , e₂'↪*F'
--   -- = {!!} , e₁↪*F' , ↪*'-trans e₂↪*E' {!!}
--   = {!!} , e₁↪*F' , ↪*'-trans {!!} e₂'↪*F'

↪*-det : e ↪* e₁ → e ↪* e₂ → ∃[ e' ] (e₁ ↪* e' × e₂ ↪* e')
↪*-det refl  e↪*e₂ = _ , e↪*e₂ , refl
↪*-det e↪*e₁ refl  = _ , refl , e↪*e₁
↪*-det (step e↪e₁' e₁'↪*e₁) (step e↪e₂' e₂'↪*e₂)
  with ↪-det e↪e₁' e↪e₂'
... | e' , e₁'↪*e' , e₂'↪*e'
  with ↪*-det e₁'↪*e₁ e₁'↪*e' -- | ↪*-det e₂'↪*e₂ e₂'↪*e' 
... | E₁' , e₁↪*E₁' , e'↪*E₁' -- | E₂' , e₂↪*E₂' , e₂'↪*E₂' 
  = {!!} , e₁↪*E₁' , ↪*-trans {!!} e'↪*E₁'

lem :
  e₁  ↪  e₂  → e₂  ↪* e₃  →
  e₁  ↪  e₂' → e₂' ↪* e₃' →
  e₂  ↪* e₃' ⊎ e₂' ↪* e₃
-- lem e₁↪e₂ e₂↪*e₃ e₁↪e₂' e₂'↪*e₃' = {!!}
lem e₁↪e₂ e₂↪*e₃ e₁↪e₂' e₂'↪*e₃' = {!!}

≣-trans : e₁ ≣ e₂ → e₂ ≣ e₃ → e₁ ≣ e₃
≣-trans (mk-≣ e e₁↪*e e₂↪*e) (mk-≣ e' e₂↪*e' e₃↪*e') with ↪*-det e₂↪*e e₂↪*e'
... | e'' , e↪*e'' , e'↪*e'' = mk-≣ e'' (↪*-trans e₁↪*e e↪*e'') (↪*-trans e₃↪*e' e'↪*e'')
-- ≣-trans (mk-≣ e e₁↪*e refl)               (mk-≣ e' e↪*e' e₃↪*e')            = mk-≣ e' (↪*-trans e₁↪*e e↪*e') e₃↪*e'
-- ≣-trans (mk-≣ e e₁↪*e e'↪*e)              (mk-≣ e' refl e₃↪*e')             = mk-≣ e e₁↪*e (↪*-trans e₃↪*e' e'↪*e)
-- ≣-trans (mk-≣ e e₁↪*e (step e₂↪t₂ t₂↪*e)) (mk-≣ e' (step e₂↪t₃ t₃↪*e') e₃↪*e')
--   with ↪-det e₂↪t₂ e₂↪t₃
-- ... | e₂' , t₂↪*e₂'' , t₃↪*e₂'' =
--   -- Looking for: t₂↪*e'
--   {!≣-trans (mk-≣ e e₁↪*e t₂↪*e) (mk-≣ e' t₃↪*e' e₃↪*e')!}

-- ≣-f :
--   ∀ {µ} {µ'} {M}
--     {f : µ ⊢ M → µ' ⊢ M}
--     (F : ∀ {e e' : µ ⊢ M} → e ↪ e' → f e ↪ f e')
--     {e e' : µ ⊢ M}
--   → e ≣ e'
--   → f e ≣ f e'
-- ≣-f F ≣-refl = ≣-refl
-- ≣-f F {e' = e''} (≣-step-↪ e↪e' e'≣e'') = ≣-step-↪ (F e↪e') (≣-f F e'≣e'')
-- ≣-f F {e' = e''} (≣-step-↩ e'↪e e'≣e'') = ≣-step-↩ (F e'↪e) (≣-f F e'≣e'')

-- ≣-↪ : e ↪ e' → e ≣ e'
-- ≣-↪ e↪e' = ≣-step-↪ e↪e' ≣-refl

-- ≣-↩ : e' ↪ e → e ≣ e'
-- ≣-↩ e'↪e = ≣-step-↩ e'↪e ≣-refl

-- ≣-λ : e ≣ e' → λx e ≣ λx e'
-- ≣-λ = ≣-f ξ-λ

-- ≣-·₁ : e₁ ≣ e₁' → e₁ · e₂ ≣ e₁' · e₂
-- ≣-·₁ = ≣-f ξ-·₁

-- ≣-·₂ : e₂ ≣ e₂' → e₁ · e₂ ≣ e₁ · e₂'
-- ≣-·₂ = ≣-f ξ-·₂

-- ≣-∀₁ : e₁ ≣ e₁' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁' ] e₂
-- ≣-∀₁ = ≣-f ξ-∀₁

-- ≣-∀₂ : e₂ ≣ e₂' → ∀[x∶ e₁ ] e₂ ≣ ∀[x∶ e₁ ] e₂'
-- ≣-∀₂ = ≣-f ξ-∀₂


-- ≣-⋯ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
--     ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
--     ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
--     ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
--     {µ₁ µ₂ m} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {t t' : µ₁ ⊢ m} →
--   t ≣ t' →
--   t ⋯ ϕ ≣ t' ⋯ ϕ
-- ≣-⋯ = ≣-f ↪-⋯

-- _⊢⋯_ :
--   ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
--     ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
--     ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
--     ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
--     {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
--   Γ₁ ⊢ e ∶ t →
--   Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
--   Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
-- ⊢` ∋x      ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
-- ⊢λ ⊢t₁ ⊢e  ⊢⋯ ⊢ϕ = ⊢λ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
-- ⊢∀ ⊢t₁ ⊢t₂ ⊢⋯ ⊢ϕ = ⊢∀ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢t₂ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
-- _⊢⋯_ {Γ₂ = Γ₂} {e = e₁ · e₂} {ϕ = ϕ} (⊢· {t₁ = t₁} {t₂ = t₂} ⊢e₁ ⊢e₂) ⊢ϕ =
--   Γ₂ ⊢ e₁ · e₂ ⋯ ϕ ∶ t₂ ⋯ₛ ⦅ e₂ ⦆ₛ ⋯ ϕ
--     by subst (Γ₂ ⊢ (e₁ · e₂) ⋯ ϕ ∶_)
--              ((t₂ ⋯ (ϕ ↑ 𝕖)) ⋯ₛ ⦅ e₂ ⋯ ϕ ⦆ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ t₂ e₂ ϕ) ⟩
--               t₂ ⋯ₛ ⦅ e₂ ⦆ₛ ⋯ ϕ             ∎)
--              (⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ))
-- ⊢★         ⊢⋯ ⊢ϕ = ⊢★
-- ⊢≣ t≣t' ⊢e ⊢⋯ ⊢ϕ = ⊢≣ (≣-⋯ t≣t') (⊢e ⊢⋯ ⊢ϕ)

-- open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

-- -- _↪**_ : ∀ {µ} (Γ₁ Γ₂ : Ctx µ) → Set
-- -- Γ₁ ↪** Γ₂ = ∀ {m} (x : _ ∋ m) → Γ₁ x ↪* Γ₂ x

-- -- ↪**-ext : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
-- --   Γ₁ ↪** Γ₂ →
-- --   (Γ₁ ▶ t) ↪** (Γ₂ ▶ t)
-- -- ↪**-ext {M = 𝕖} ↪Γ (here refl) = refl
-- -- ↪**-ext {M = M} ↪Γ (there x) = ↪Γ x

-- -- ↪**-pres : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
-- --   Γ₁ ↪** Γ₂ →
-- --   Γ₁ ⊢ e ∶ t →
-- --   Γ₂ ⊢ e ∶ t
-- -- ↪**-pres {M = 𝕖} Γ↪ (⊢` {x = x} refl)       = {!⊢↪* {!Γ↪ x!} (⊢` refl)!}
-- -- ↪**-pres Γ↪ (⊢λ ⊢t₁ ⊢e)  = {!!}
-- -- ↪**-pres Γ↪ (⊢∀ ⊢t₁ ⊢t₂) = {!!}
-- -- ↪**-pres Γ↪ (⊢· ⊢e₁ ⊢e₂) = {!!}
-- -- ↪**-pres Γ↪ ⊢★           = ⊢★
-- -- ↪**-pres Γ↪ (⊢≣ t≣t' ⊢e) = {!!}

-- _≣σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
-- σ₁ ≣σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ≣ σ₂ _ x

-- -- Are Ctx's basically Substitutions which don't weaken automatically?
-- -- Can be represent them as such or even generalize our substitutions?
-- ≣σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
--   σ ≣σ σ
-- ≣σ-refl {m = 𝕖} x = ≣-refl

-- _≣*_ : ∀ {µ} (Γ₁ Γ₂ : Ctx µ) → Set
-- Γ₁ ≣* Γ₂ = ∀ {m} (x : _ ∋ m) → Γ₁ x ≣ Γ₂ x

-- ≣*-refl : ∀ {µ} {Γ : Ctx µ} →
--   Γ ≣* Γ
-- ≣*-refl {m = 𝕖} x = ≣-refl

-- ≣*-ext : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {t₁ t₂ : µ ⊢ M} →
--   Γ₁ ≣* Γ₂ →
--   t₁ ≣ t₂ →
--   (Γ₁ ▶ t₁) ≣* (Γ₂ ▶ t₂)
-- ≣*-ext {M = 𝕖} Γ₁≣Γ₂ t₁≣t₂ (here refl) = t₁≣t₂
-- ≣*-ext {M = M} Γ₁≣Γ₂ t₁≣t₂ (there x)   = Γ₁≣Γ₂ x

-- ≣*-↑ : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {t : µ ⊢ M} →
--   Γ₁ ≣* Γ₂ →
--   (Γ₁ ▶ t) ≣* (Γ₂ ▶ t)
-- ≣*-↑ {M = 𝕖} ≣Γ = ≣*-ext ≣Γ ≣-refl

-- ≣*-pres : ∀ {µ} {Γ₁ Γ₂ : Ctx µ} {M} {e : µ ⊢ M} {t : µ ⊢ M} →
--   Γ₁ ≣* Γ₂ →
--   Γ₁ ⊢ e ∶ t →
--   Γ₂ ⊢ e ∶ t
-- ≣*-pres {M = 𝕖} Γ≣ (⊢` {x = x} refl) = ⊢≣ {!Γ≣ x!} (⊢` refl)
-- ≣*-pres Γ≣ (⊢λ ⊢t₁ ⊢e)  = {!!}
-- ≣*-pres Γ≣ (⊢∀ ⊢t₁ ⊢t₂) = {!!}
-- ≣*-pres Γ≣ (⊢· ⊢e₁ ⊢e₂) = {!!}
-- ≣*-pres Γ≣ ⊢★           = ⊢★
-- ≣*-pres Γ≣ (⊢≣ t≣t' ⊢e) = {!!}

-- open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)

-- invert-⊢λ : ∀ {µ} {Γ : Ctx µ} {e : (µ ▷ 𝕖) ⊢ 𝕖} {t : µ ⊢ 𝕖} →
--     Γ ⊢ λx e ∶ t →
--     ∃[ t₁ ] ∃[ t₂ ]
--       t ≣ ∀[x∶ t₁ ] t₂ ×
--       Γ ⊢ t₁ ∶ ★ ×
--       Γ ▶ t₁ ⊢ e ∶ t₂
-- invert-⊢λ (⊢λ ⊢t₁ ⊢e) = _ , _ , ≣-refl , ⊢t₁ , ⊢e
-- invert-⊢λ (⊢≣ t≣t' ⊢e) with invert-⊢λ ⊢e
-- ... | t₁ , t₂ , t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e = t₁ , t₂ , ≣-trans (≣-sym t≣t') t'≣∀[t₁]t₂ , ⊢t₁ , ⊢e

-- -- invert-↪-λ :
-- --   ∀[x∶ t₁ ] t₂ ↪* ∀[x∶ t₁' ] t₂' →
-- --   t₁ ↪* t₁' × t₂ ↪* t₂'
-- -- invert-↪-λ refl = refl , refl
-- -- invert-↪-λ (step (ξ-∀₁ x) st) = {!!}
-- -- invert-↪-λ (step (ξ-∀₂ x) st) = {!!}

-- invert-↪-λ :
--   ∀[x∶ t₁ ] t₂ ↪ ∀[x∶ t₁' ] t₂' →
--   t₁ ↪ t₁' ⊎ t₂ ↪ t₂'
-- invert-↪-λ (ξ-∀₁ t₁↪t₁') = inj₁ t₁↪t₁'
-- invert-↪-λ (ξ-∀₂ t₂↪t₂') = inj₂ t₂↪t₂'

-- -- invert-≣-λ'' :
-- --   ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
-- --   (λx e₁) · e₂ ↪ ∀[x∶ t₁' ] t₂' →

-- invert-≣-λ' :
--   t ≣ t' →
--   t ≡ ∀[x∶ t₁ ] t₂ →
--   t' ≡ ∀[x∶ t₁' ] t₂' →
--   t₁ ≣ t₁' × t₂ ≣ t₂'
-- invert-≣-λ' ≣-refl refl refl         = ≣-refl , ≣-refl
-- invert-≣-λ' (≣-step-↪ (ξ-∀₁ t₁↪t₁'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
-- ... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↪ t₁↪t₁'') t₁''≣t₁' , t₂≣t₂'
-- invert-≣-λ' (≣-step-↪ (ξ-∀₂ t₂↪t₂'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
-- ... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↪ t₂↪t₂'') t₂''≣t₂'
-- invert-≣-λ' (≣-step-↩ (ξ-∀₁ t₁↩t₁'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
-- ... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↩ t₁↩t₁'') t₁''≣t₁' , t₂≣t₂'
-- invert-≣-λ' (≣-step-↩ (ξ-∀₂ t₂↩t₂'') ∀≣∀) refl refl with invert-≣-λ' ∀≣∀ refl refl
-- ... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↩ t₂↩t₂'') t₂''≣t₂'
-- invert-≣-λ' (≣-step-↩ β-λ e₂≣∀) eq refl = {!!}
-- -- ∀[x∶ t₁ ] t₂  ↩  (λx e₁) · e₂  ≣  ∀[x∶ t₁' ] t₂'

-- -- invert-≣-λ' (≣-step-↩ (β-λ {e₁ = ` x}) e₂≣∀) eq refl = {!!}
-- -- invert-≣-λ' (≣-step-↩ (β-λ {e₁ = ∀[x∶ e₁ ] e₂}) e₂≣∀) refl refl = {!!}

-- invert-≣-λ :
--   ∀[x∶ t₁ ] t₂ ≣ ∀[x∶ t₁' ] t₂' →
--   t₁ ≣ t₁' × t₂ ≣ t₂'
-- invert-≣-λ ≣-refl          = ≣-refl , ≣-refl
-- invert-≣-λ (≣-step-↪ (ξ-∀₁ t₁↪t₁'') ∀≣∀) with invert-≣-λ ∀≣∀
-- ... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↪ t₁↪t₁'') t₁''≣t₁' , t₂≣t₂'
-- invert-≣-λ (≣-step-↪ (ξ-∀₂ t₂↪t₂'') ∀≣∀) with invert-≣-λ ∀≣∀
-- ... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↪ t₂↪t₂'') t₂''≣t₂'
-- invert-≣-λ (≣-step-↩ ∀↩e₂ e₂≣∀) = {!eq!}
-- -- invert-≣-λ (≣-step-↩ (ξ-∀₁ t₁↩t₁'') ∀≣∀) with invert-≣-λ ∀≣∀
-- -- ... | t₁''≣t₁' , t₂≣t₂' = ≣-trans (≣-↩ t₁↩t₁'') t₁''≣t₁' , t₂≣t₂'
-- -- invert-≣-λ (≣-step-↩ (ξ-∀₂ t₂↩t₂'') ∀≣∀) with invert-≣-λ ∀≣∀
-- -- ... | t₁≣t₁' , t₂''≣t₂' = t₁≣t₁' , ≣-trans (≣-↩ t₂↩t₂'') t₂''≣t₂'

-- subject-reduction :
--   Γ ⊢ e ∶ t →
--   e ↪ e' →
--   Γ ⊢ e' ∶ t
-- subject-reduction (⊢λ ⊢t ⊢e)   (ξ-λ e↪e')    = ⊢λ ⊢t (subject-reduction ⊢e e↪e')
-- subject-reduction {Γ = Γ} (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₁ t₁↪t₁') = ⊢∀ (subject-reduction ⊢t₁ t₁↪t₁')
--                                                           (≣*-pres (≣*-ext (≣*-refl {Γ = Γ}) (≣-↪ t₁↪t₁')) ⊢t₂)
-- subject-reduction (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₂ t₂↪t₂') = ⊢∀ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
-- -- subject-reduction (⊢· (⊢λ ⊢t ⊢e₁) ⊢e₂) β-λ = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆
-- -- subject-reduction (⊢· (⊢≣ x ⊢e₁) ⊢e₂) β-λ = {!!}
-- subject-reduction (⊢· ⊢e₁ ⊢e₂) β-λ with invert-⊢λ ⊢e₁
-- ... | t₁ , t₂ , ∀≣∀ , ⊢t₁ , ⊢e₁ = {!⊢≣ (≣-sym ∀≣∀) (⊢λ ⊢t₁ ⊢e₁) !} -- ⊢≣ {!≣-sym eq!} {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ!}
-- subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
-- subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = {!⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')!}
-- subject-reduction (⊢≣ t≣t' ⊢e) e↪e'          = ⊢≣ t≣t' (subject-reduction ⊢e e↪e')
