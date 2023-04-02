module Kitty.Examples.LambdaPi-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.LambdaPi-Derive.Definitions
open import Kitty.Examples.LambdaPi-Derive.Confluence
open import Kitty.Examples.LambdaPi-Derive.Closures
open import Kitty.Typing.IKit compose-traversal kit-type record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }
open IKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_; proj₁; proj₂)

_↪σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ↪σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ↪ σ₂ _ x

_↪*σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ↪*σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ↪* σ₂ _ x

_↪ₚ*σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ↪ₚ*σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ↪ₚ* σ₂ _ x

open ReflexiveTransitiveClosure₂ (_→ₛ_) _↪ₚσ_ renaming
  ( ReflTrans to _↪ₚσ*_
  ; map-ReflTrans to map-↪ₚσ*
  ; _⟨_⟩_ to _↪ₚσ⟨_⟩_
  ; _*⟨_⟩_ to _↪ₚσ*⟨_⟩_
  ; _∎ to _↪ₚσ∎
  ; trans to ↪ₚσ*-trans
  ; embed to ↪ₚσ*-embed
  ) hiding (refl; step) public

to''' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} {t₂'} →
  σ₁ ↓ₛ ≡ σ₂ ↓ₛ →
  t₂' ≡ σ₂ _ (here refl) →
  σ₁ _ (here refl) ↪ₚ* t₂' →
  σ₁ ↪ₚσ* σ₂
to''' {σ₁ = σ₁} {σ₂ = σ₂} p q refl =
  step (λ { (here refl) → subst (_ ↪ₚ_) q ↪ₚ-refl
          ; (there x)   → subst (_ ↪ₚ_) (cong-app (cong-app p _) x ) ↪ₚ-refl})
        refl
to''' {σ₁ = σ₁} xx refl (step {a₂ = t'} t₁↪t' t'↪*t₂) =
  step {a₂ = (σ₁ ↓ₛ) ,ₛ t'}
       (λ { (here refl) → t₁↪t'
          ; (there x) → ↪ₚ-refl})
       (to''' xx refl t'↪*t₂)

to'' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} {t₂'} {σ₂'} →
  σ₂' ≡ σ₂ ↓ₛ →
  t₂' ≡ σ₂ _ (here refl) →
  σ₁ ↓ₛ ↪ₚσ* σ₂' →
  σ₁ _ (here refl) ↪ₚ* t₂' →
  σ₁ ↪ₚσ* σ₂
to'' p q refl t₁↪*t₂ = to''' p q t₁↪*t₂
to'' {σ₁ = σ₁} refl q (step {a₂ = σ'} σ₁↪*σ' σ'↪*σ₂) t₁↪*t₂ =
  step {a₂ = σ' ,ₛ σ₁ _ (here refl)}
       (λ { (here refl) → ↪ₚ-refl
          ; (there x)   → σ₁↪*σ' x})
       (to'' refl q σ'↪*σ₂ t₁↪*t₂)

to' : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : (µ₁ ▷ m) →ₛ µ₂} →
  σ₁ ↓ₛ ↪ₚσ* σ₂ ↓ₛ →
  σ₁ _ (here refl) ↪ₚ* σ₂ _ (here refl) →
  σ₁ ↪ₚσ* σ₂
to' = to'' refl refl

to : ∀ {µ₁ µ₂} {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  σ₁ ↪ₚ*σ σ₂ →
  σ₁ ↪ₚσ* σ₂
to {[]}     σ₁↪*σ₂ = step (λ ()) refl
to {µ₁ ▷ m} σ₁↪*σ₂ with to (λ x → σ₁↪*σ₂ (there x))
... | σ₁↪*σ₂' = to' σ₁↪*σ₂' (σ₁↪*σ₂ (here refl))

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

↪σ-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  σ ↪σ σ' →
  t ⋯ₛ σ ↪* t' ⋯ₛ σ'
↪σ-⋯ₛ t↪t' σ↪σ' = ↪ₚ→↪* (↪ₚσ-⋯ (↪→↪ₚ t↪t') (λ x → ↪→↪ₚ (σ↪σ' x)))

↪*-⋯ₛ : ∀ {µ₁ µ₂ m} {σ σ' : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪* t' →
  σ ↪*σ σ' →
  t ⋯ₛ σ ↪* t' ⋯ₛ σ'
↪*-⋯ₛ t↪*t' σ↪*σ' = ↪ₚ*→↪* (↪ₚ*σ-⋯ (↪*→↪ₚ* t↪*t') (to (λ x → ↪*→↪ₚ* (σ↪*σ' x)))) 

--------------------------------------------------------------------------------

≣-refl : e ≣ e
≣-refl = mk-≣ _ refl refl

≣-sym : e₁ ≣ e₂ → e₂ ≣ e₁
≣-sym (mk-≣ e e₁↪*e e₂↪*e) = mk-≣ e e₂↪*e e₁↪*e

≣-trans : e₁ ≣ e₂ → e₂ ≣ e₃ → e₁ ≣ e₃
≣-trans (mk-≣ e e₁↪*e e₂↪*e) (mk-≣ e' e₂↪*e' e₃↪*e') with confluence e₂↪*e e₂↪*e'
... | e'' , e↪*e'' , e'↪*e'' = mk-≣ e'' (↪*-trans e₁↪*e e↪*e'') (↪*-trans e₃↪*e' e'↪*e'')

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

--------------------------------------------------------------------------------

_≣σ_ : ∀ {µ₁ µ₂} (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ≣σ σ₂ = ∀ {m} (x : _ ∋ m) → σ₁ _ x ≣ σ₂ _ x

-- Are Ctx's basically Substitutions which don't weaken automatically?
-- Can we represent them as such or even generalize our substitutions?
≣σ-refl : ∀ {µ₁ µ₂} {σ : µ₁ →ₛ µ₂} →
  σ ≣σ σ
≣σ-refl {m = 𝕖} x = ≣-refl

≣σ-ext : ∀ {µ₁ µ₂ m} {σ₁ σ₂ : µ₁ →ₛ µ₂} {t₁ t₂ : µ₂ ⊢ m→M m} →
  σ₁ ≣σ σ₂ →
  t₁ ≣ t₂ →
  (σ₁ ,ₛ t₁) ≣σ (σ₂ ,ₛ t₂)
≣σ-ext σ₁≣σ₂ t₁≣t₂ (here refl) = t₁≣t₂
≣σ-ext σ₁≣σ₂ t₁≣t₂ (there x)   = σ₁≣σ₂ x

≣σ-⦅_⦆ : ∀ {µ m} {t₁ t₂ : µ ⊢ m→M m} →
  t₁ ≣ t₂ →
  ⦅ t₁ ⦆ₛ ≣σ ⦅ t₂ ⦆ₛ
≣σ-⦅ t₁≣t₂ ⦆ = ≣σ-ext (≣σ-refl {σ = idₛ}) t₁≣t₂

≣→Σ : t₁ ≣ t₂ → ∃[ t ] t₁ ↪* t × t₂ ↪* t 
≣→Σ (mk-≣ t t₁↪*t t₂↪*t) = t , t₁↪*t , t₂↪*t

≣σ→↪*σ : ∀ {µ₁ µ₂} {σ σ' : µ₁ →ₛ µ₂} →
  σ ≣σ σ' →
  ∃[ σ'' ] σ ↪*σ σ'' × σ' ↪*σ σ''
≣σ→↪*σ σ≣σ' = (λ m x → proj₁ (≣→Σ (σ≣σ' x)))
          , (λ x → proj₁ (proj₂ (≣→Σ (σ≣σ' x))))
          , (λ x → proj₂ (proj₂ (≣→Σ (σ≣σ' x))))

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

↪-⋯ₛ : ∀ {µ₁ µ₂ m} {ϕ : µ₁ →ₛ µ₂} {t t' : µ₁ ⊢ m} →
  t ↪ t' →
  t ⋯ₛ ϕ ↪ t' ⋯ₛ ϕ
↪-⋯ₛ = ↪-⋯ where instance _ = kitₛ; _ = kittₛ; _ = ckitₛₛ; _ = ckitᵣ

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
↪-∀-shape (ξ-∀₁ t₁↪t₁') = _ , _ , refl , embed t₁↪t₁' , refl
↪-∀-shape (ξ-∀₂ t₂↪t₂') = _ , _ , refl , refl , embed t₂↪t₂'

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
subject-reduction (⊢· {t₂ = t₂} ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = ⊢≣ (≣-⋯ₛ (≣-refl {e = t₂}) ≣σ-⦅ ≣-↩ e₂↪e₂' ⦆)
                                                            (⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂'))
subject-reduction (⊢≣ t≣t' ⊢e)           e↪e'          = ⊢≣ t≣t' (subject-reduction ⊢e e↪e')
