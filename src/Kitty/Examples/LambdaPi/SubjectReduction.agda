module Kitty.Examples.LambdaPi.SubjectReduction where

open import Data.Product using (∃-syntax; Σ-syntax; _×_ ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using () renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong-app; subst; module ≡-Reasoning)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (List; []; _∷_; drop)
open ≡-Reasoning

open import Kitty.Examples.LambdaPi.Definitions
open import Kitty.Examples.LambdaPi.Confluence
open import Kitty.Typing.TypingKit compose-traversal ctx-repr typing
open import Kitty.Util.List using (depth)
open TypingKit ⦃ … ⦄

-- Conversion is an equivalence relation

≈-refl :
  e ≈ e
≈-refl {e = e} = mk-≈ e ↪*-refl ↪*-refl

≈-sym :
  e₁ ≈ e₂ →
  e₂ ≈ e₁
≈-sym (mk-≈ e e₁↪*e e₂↪*e) = mk-≈ e e₂↪*e e₁↪*e

≈-trans :
  e₁ ≈ e₂ →
  e₂ ≈ e₃ →
  e₁ ≈ e₃
≈-trans (mk-≈ e e₁↪*e e₂↪*e) (mk-≈ e' e₂↪*e' e₃↪*e')
 with confluence e₂↪*e e₂↪*e'
... | e'' , e↪*e'' , e'↪*e''
 = mk-≈ e'' (↪*-trans e₁↪*e e↪*e'') (↪*-trans e₃↪*e' e'↪*e'')

-- Reduction implies conversion

↪→≈ :
  e₁ ↪ e₂ →
  e₁ ≈ e₂
↪→≈ e₁↪e₂ = mk-≈ _ (↪*-step e₁↪e₂ ↪*-refl) ↪*-refl

-- Lifting reduction and conversion pointwise to substitutions

_↪ₚ*σ_ : ∀ (σ₁ σ₂ : S₁ →ₛ S₂) → Set
σ₁ ↪ₚ*σ σ₂ = ∀ s (x : _ ∋ s) → σ₁ _ x ↪ₚ* σ₂ _ x

_↪*σ_ : ∀ (σ₁ σ₂ : S₁ →ₛ S₂) → Set
σ₁ ↪*σ σ₂ = ∀ s (x : _ ∋ s) → σ₁ _ x ↪* σ₂ _ x

_≈σ_ : ∀ (σ₁ σ₂ : S₁ →ₛ S₂) → Set
σ₁ ≈σ σ₂ = ∀ s (x : _ ∋ s) → σ₁ _ x ≈ σ₂ _ x

↪ₚ*-⋯ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ s} →
  e ↪ₚ* e' →
  (e ⋯ ϕ) ↪ₚ* (e' ⋯ ϕ)
↪ₚ*-⋯ ⦃ C₂ = C₂ ⦄ ↪ₚ*-refl       = ↪ₚ*-refl
↪ₚ*-⋯ ⦃ C₂ = C₂ ⦄ (↪ₚ*-step p q) = ↪ₚ*-step (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ p) (↪ₚ*-⋯ ⦃ C₂ = C₂ ⦄ q)

↪-⋯ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ s} →
  e ↪ e' →
  e ⋯ ϕ ↪* e' ⋯ ϕ
↪-⋯ ⦃ C₂ = C₂ ⦄ e↪e' = ↪ₚ→↪* (↪ₚ-⋯ ⦃ C₂ = C₂ ⦄ (↪→↪ₚ e↪e'))

↪*-⋯ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ s} →
  e ↪* e' →
  e ⋯ ϕ ↪* e' ⋯ ϕ
↪*-⋯ ⦃ C₂ = C₂ ⦄ ↪*-refl = ↪*-refl
↪*-⋯ ⦃ C₂ = C₂ ⦄ (↪*-step p q) = ↪*-trans (↪-⋯ ⦃ C₂ = C₂ ⦄ p) (↪*-⋯ ⦃ C₂ = C₂ ⦄ q)

≈-⋯ₖ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄
    ⦃ C₁ : ComposeKit K K K ⦄ ⦃ C₂ : ComposeKit Kₛ K Kₛ ⦄ ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {ϕ : S₁ –[ K ]→ S₂} {e e' : S₁ ⊢ s} →
  e ≈ e' →
  (e ⋯ ϕ) ≈ (e' ⋯ ϕ)
≈-⋯ₖ ⦃ C₂ = C₂ ⦄ {ϕ = ϕ} (mk-≈ E e₁↪*E e₂↪*E) = mk-≈ (E ⋯ ϕ) (↪*-⋯ ⦃ C₂ = C₂ ⦄ e₁↪*E) (↪*-⋯ ⦃ C₂ = C₂ ⦄ e₂↪*E)

↪ₚ*σ-↑ : ∀ {σ σ' : S₁ →ₛ S₂}
  → σ ↪ₚ*σ σ'
  → (σ ↑ₛ s) ↪ₚ*σ (σ' ↑ₛ s)
↪ₚ*σ-↑ σ↪ₚσ' _ (here refl) = ↪ₚ*-refl
↪ₚ*σ-↑ σ↪ₚσ' _ (there x) = ↪ₚ*-⋯ (σ↪ₚσ' _ x)

↪ₚ*σ-⋯ : ∀ {σ σ' : S₁ →ₛ S₂} →
  e ↪ₚ e' →
  σ ↪ₚ*σ σ' →
  (e ⋯ σ) ↪ₚ* (e' ⋯ σ')
↪ₚ*σ-⋯ ξ-`                         σ↪σ' = σ↪σ' _ _
↪ₚ*σ-⋯ {σ' = σ'} (β-λ {e₁' = e₁'} {e₂' = e₂'} e₁↪ₚe₁' e₂↪ₚe₂')
                                   σ↪σ' = subst (_ ↪ₚ*_) (sym (dist-⦅⦆ₛ-⋯ₛ e₁' e₂' σ'))
                                                (β*-λ (↪ₚ*σ-⋯ e₁↪ₚe₁' (↪ₚ*σ-↑ σ↪σ')) (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ'))
↪ₚ*σ-⋯ (ξ-λ e↪ₚe')                 σ↪σ' = ↪ₚ*-map ξ-λ (↪ₚ*σ-⋯ e↪ₚe' (↪ₚ*σ-↑ σ↪σ'))
↪ₚ*σ-⋯ (ξ-∀ t₁↪ₚt₁' t₂↪ₚt₂')       σ↪σ' = ↪ₚ*-map₂ ξ-∀ (↪ₚ*σ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚ*σ-⋯ t₂↪ₚt₂' (↪ₚ*σ-↑ σ↪σ'))
↪ₚ*σ-⋯ (ξ-· e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ↪ₚ*-map₂ ξ-· (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚ*σ-⋯ ξ-Set                       σ↪σ' = ↪ₚ*-refl
↪ₚ*σ-⋯ (β-proj₁ e₁↪ₚe₁' e₂↪ₚe₂')   σ↪σ' = β*-proj₁ (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚ*σ-⋯ (β-proj₂ e₁↪ₚe₁' e₂↪ₚe₂')   σ↪σ' = β*-proj₂ (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚ*σ-⋯ (ξ-∃ t₁↪ₚt₁' t₂↪ₚt₂')       σ↪σ' = ↪ₚ*-map₂ ξ-∃ (↪ₚ*σ-⋯ t₁↪ₚt₁' σ↪σ') (↪ₚ*σ-⋯ t₂↪ₚt₂' (↪ₚ*σ-↑ σ↪σ'))
↪ₚ*σ-⋯ (ξ-, e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ↪ₚ*-map₂ ξ-, (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚ*σ-⋯ (ξ-proj₁ e↪ₚe')             σ↪σ' = ↪ₚ*-map ξ-proj₁ (↪ₚ*σ-⋯ e↪ₚe' σ↪σ')
↪ₚ*σ-⋯ (ξ-proj₂ e↪ₚe')             σ↪σ' = ↪ₚ*-map ξ-proj₂ (↪ₚ*σ-⋯ e↪ₚe' σ↪σ')
↪ₚ*σ-⋯ (β-J e↪ₚe')                 σ↪σ' = β*-J (↪ₚ*σ-⋯ e↪ₚe' σ↪σ')
↪ₚ*σ-⋯ (ξ-≡ e₁↪ₚe₁' e₂↪ₚe₂')       σ↪σ' = ↪ₚ*-map₂ ξ-≡ (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ') (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')
↪ₚ*σ-⋯ ξ-refl                      σ↪σ' = ↪ₚ*-refl
↪ₚ*σ-⋯ (ξ-J t↪ₚt' e₁↪ₚe₁' e₂↪ₚe₂') σ↪σ' = ↪ₚ*-map₃ ξ-J (↪ₚ*σ-⋯ t↪ₚt' (↪ₚ*σ-↑ σ↪σ'))
                                                       (↪ₚ*σ-⋯ e₁↪ₚe₁' σ↪σ')
                                                       (↪ₚ*σ-⋯ e₂↪ₚe₂' σ↪σ')

↪ₚ*σ-⋯' : ∀ {σ σ' : S₁ →ₛ S₂} →
  e ↪ₚ* e' →
  σ ↪ₚ*σ σ' →
  (e ⋯ σ) ↪ₚ* (e' ⋯ σ')
↪ₚ*σ-⋯' {e = e} ↪ₚ*-refl σ↪ₚ*σ' = ↪ₚ*σ-⋯ {e = e} ↪ₚ-refl σ↪ₚ*σ'
↪ₚ*σ-⋯' (↪ₚ*-step p q) σ↪ₚ*σ' = ↪ₚ*-trans (↪ₚ*σ-⋯ p λ s x → ↪ₚ*-refl) (↪ₚ*σ-⋯' q σ↪ₚ*σ' )

↪*σ-⋯ : ∀ {σ σ' : S₁ →ₛ S₂} →
  e ↪* e' →
  σ ↪*σ σ' →
  (e ⋯ σ) ↪* (e' ⋯ σ')
↪*σ-⋯ {e = e} e↪*e' σ↪*σ' = ↪ₚ*→↪* (↪ₚ*σ-⋯' (↪*→↪ₚ* e↪*e') λ s x → ↪*→↪ₚ* (σ↪*σ' s x))

≈-⋯ : ∀ {σ σ' : S₁ →ₛ S₂} →
  e ≈ e' →
  σ ≈σ σ' →
  (e ⋯ σ) ≈ (e' ⋯ σ')
≈-⋯ (mk-≈ E e₁↪*E e₂↪*E) σ≈σ' =
  mk-≈ _ (↪*σ-⋯ e₁↪*E λ s x → ≈-e₁↪*e (σ≈σ' s x)) (↪*σ-⋯ e₂↪*E (λ s x → ≈-e₂↪*e (σ≈σ' s x)))

≈→≈σ : ∀ {e e' : S ⊢ s} →
  e ≈ e' →
  ⦅ e ⦆' ≈σ ⦅ e' ⦆'
≈→≈σ e≈e' _ (here refl) = e≈e'
≈→≈σ e≈e' _ (there x) = mk-≈ (` x) ↪*-refl ↪*-refl

≈σ-refl : ∀ {σ : S₁ →ₛ S₂} →
  σ ≈σ σ
≈σ-refl _ x = ≈-refl

-- Context Conversion

_≈ᶜ_ : Ctx S → Ctx S → Set
Γ₁ ≈ᶜ Γ₂ = ∀ s (x : _ ∋ s) → wk-telescope Γ₁ x ≈ wk-telescope Γ₂ x

≈ᶜ-refl : ∀ {Γ : Ctx S}
  → Γ ≈ᶜ Γ
≈ᶜ-refl _ x = ≈-refl


≈-subst : ∀ (eq₁ eq₂ : S ≡ S') →
  e₁ ≈ e₂ →
  subst (_⊢ s) eq₁ e₁ ≈ subst (_⊢ s) eq₂ e₂ 
≈-subst refl refl p = p

≈-subst⁻ : ∀ (eq₁ eq₂ : S ≡ S') →
  subst (_⊢ s) eq₁ e₁ ≈ subst (_⊢ s) eq₂ e₂ →
  e₁ ≈ e₂
≈-subst⁻ refl refl p = p

≈ᶜ-ext : ∀ {Γ₁ Γ₂ : Ctx S}
  → Γ₁ ≈ᶜ Γ₂
  → t₁ ≈ t₂
  → (Γ₁ ▶ t₁) ≈ᶜ (Γ₂ ▶ t₂)
≈ᶜ-ext {S = S} Γ₁≈Γ₂ t₁≈t₂ _ (here refl) = ≈-⋯ₖ (≈-subst p p (≈-subst (sym p) (sym p) t₁≈t₂))
                                           where p = ++-identityʳ S
≈ᶜ-ext {S = S} Γ₁≈Γ₂ t₁≈t₂ _ (there x)   = ≈-⋯ₖ (Γ₁≈Γ₂ _ x) 

≈-Γ-⊢ : ∀ {Γ₁ Γ₂ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s}
  → Γ₁ ≈ᶜ Γ₂
  → Γ₁ ⊢ e ∶ t
  → Γ₂ ⊢ e ∶ t
≈-Γ-⊢ Γ₁≈Γ₂ (⊢` {s = 𝕖} {x = x} refl) =  ⊢≈ (≈-sym (Γ₁≈Γ₂ _ x)) (⊢` {x = x} refl)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢λ ⊢t₁ ⊢e)             = ⊢λ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢t₁) (≈-Γ-⊢ (≈ᶜ-ext Γ₁≈Γ₂ ≈-refl) ⊢e)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢· ⊢e₁ ⊢e₂)            = ⊢· (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₁) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₂)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢∀ ⊢t₁ ⊢t₂)            = ⊢∀ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢t₁) (≈-Γ-⊢ (≈ᶜ-ext Γ₁≈Γ₂ ≈-refl) ⊢t₂)
≈-Γ-⊢ Γ₁≈Γ₂ ⊢Set                    = ⊢Set
≈-Γ-⊢ Γ₁≈Γ₂ (⊢≈ t≈t' ⊢e)            = ⊢≈ t≈t' (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢∃ ⊢t₁ ⊢t₂)            = ⊢∃ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢t₁) (≈-Γ-⊢ (≈ᶜ-ext Γ₁≈Γ₂ ≈-refl) ⊢t₂)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢, ⊢e₁ ⊢e₂)            = ⊢, (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₁) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₂)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢proj₁ ⊢e)             = ⊢proj₁ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢proj₂ ⊢e)             = ⊢proj₂ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢≡ ⊢e₁ ⊢e₂)            = ⊢≡ (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₁) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₂)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢refl ⊢e)              = ⊢refl (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e)
≈-Γ-⊢ Γ₁≈Γ₂ (⊢J ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) = ⊢J (≈-Γ-⊢ (≈ᶜ-ext Γ₁≈Γ₂ ≈-refl) ⊢t) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢u₁) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢u₂) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₁) (≈-Γ-⊢ Γ₁≈Γ₂ ⊢e₂)

≈-Γ-⊢₁ : ∀ {Γ : Ctx S} {t₁ t₂ : S ∶⊢ 𝕖} {e : (𝕖 ∷ S) ⊢ 𝕖} {t : (𝕖 ∷ S) ∶⊢ 𝕖}
  → t₁ ≈ t₂
  → Γ ▶ t₁ ⊢ e ∶ t
  → Γ ▶ t₂ ⊢ e ∶ t
≈-Γ-⊢₁ {Γ = Γ} t₁≈t₂ ⊢e = ≈-Γ-⊢ (≈ᶜ-ext (≈ᶜ-refl {Γ = Γ}) t₁≈t₂) ⊢e

--------------------------------------------------------------------------------
-- Inversion for lambda terms

↪-∀-shape :
  ∀[x∶ t₁ ] t₂ ↪ t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪-∀-shape (ξ-∀₁ t₁↪t₁') = _ ,  _ ,  refl ,  ↪*-step t₁↪t₁' ↪*-refl , ↪*-refl    
↪-∀-shape (ξ-∀₂ t₂↪t₂') = _ ,  _ ,  refl ,  ↪*-refl , ↪*-step t₂↪t₂' ↪*-refl    

↪*-∀-shape :
  (∀[x∶ t₁ ] t₂) ↪* t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∀[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪*-∀-shape ↪*-refl =  _ ,  _ ,  refl ,  ↪*-refl , ↪*-refl    
↪*-∀-shape (↪*-step ∀↪t t↪*t')
  with ↪-∀-shape ∀↪t
...  |  t₁' ,  t₂' ,  refl ,  t₁↪*t₁' , t₂↪*t₂'    
  with ↪*-∀-shape t↪*t'
...  |  t₁'' ,  t₂'' ,  refl ,  t₁'↪*t₁'' , t₂'↪*t₂''    
  =  t₁'' ,  t₂'' ,  refl ,  ↪*-trans t₁↪*t₁' t₁'↪*t₁'' , ↪*-trans t₂↪*t₂' t₂'↪*t₂''    

invert-≈-∀ :
  (∀[x∶ t₁ ] t₂) ≈ (∀[x∶ t₁' ] t₂') →
  t₁ ≈ t₁' × t₂ ≈ t₂'
invert-≈-∀ (mk-≈ t ∀₁↪*t ∀₂↪*t)
  with ↪*-∀-shape ∀₁↪*t                | ↪*-∀-shape ∀₂↪*t
... |  T₁ ,  T₂ ,  refl ,  t₁↪*T₁ , t₂↪*T₂     |  .T₁ ,  .T₂ ,  refl ,  t₁'↪*T₁ , t₂'↪*T₂    
  =  (mk-≈ T₁ t₁↪*T₁ t₁'↪*T₁) , (mk-≈ T₂ t₂↪*T₂ t₂'↪*T₂) 

invert-⊢λ' :
  Γ ⊢ λx e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    t ≈ (∀[x∶ t₁ ] t₂) ×
    Γ ⊢ t₁ ∶ `Set ×
    Γ ▶ t₁ ⊢ e ∶ t₂
invert-⊢λ' (⊢λ ⊢t₁ ⊢e) =  _ ,  _ ,  ≈-refl ,  ⊢t₁ , ⊢e    
invert-⊢λ' (⊢≈ t≈t' ⊢e) with invert-⊢λ' ⊢e
... |  t₁ ,  t₂ ,  t'≈∀[t₁]t₂ ,  ⊢t₁ , ⊢e     =  t₁ ,  t₂ ,  ≈-trans (≈-sym t≈t') t'≈∀[t₁]t₂ ,  ⊢t₁ , ⊢e    

invert-⊢λ :
  Γ ⊢ λx e ∶ ∀[x∶ t₁ ] t₂ →
  ∃[ t₁' ] ∃[ t₂' ]
      t₁ ≈ t₁' ×
      t₂ ≈ t₂' ×
      Γ ⊢ t₁' ∶ `Set ×
      Γ ▶ t₁' ⊢ e ∶ t₂'
invert-⊢λ ⊢e
 with invert-⊢λ' ⊢e
... |  t₁' ,  t₂' ,  ∀≈∀' ,  ⊢t₁' , ⊢e    
 with invert-≈-∀ ∀≈∀'
... |  t₁≈t₁' , t₂≈t₂' 
 =  t₁' ,  t₂' ,  t₁≈t₁' ,  t₂≈t₂' ,  ⊢t₁' , ⊢e     

-- Inversion for product terms

↪-∃-shape :
  ∃[x∶ t₁ ] t₂ ↪ t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∃[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪-∃-shape (ξ-∃₁ t₁↪t₁') =  _ ,  _ ,  refl ,  ↪*-step t₁↪t₁' ↪*-refl , ↪*-refl    
↪-∃-shape (ξ-∃₂ t₂↪t₂') =  _ ,  _ ,  refl ,  ↪*-refl , ↪*-step t₂↪t₂' ↪*-refl    

↪*-∃-shape :
  (∃[x∶ t₁ ] t₂) ↪* t → 
  ∃[ t₁' ] ∃[ t₂' ] t ≡ ∃[x∶ t₁' ] t₂' × (t₁ ↪* t₁') × (t₂ ↪* t₂')
↪*-∃-shape ↪*-refl =  _ ,  _ ,  refl ,  ↪*-refl , ↪*-refl    
↪*-∃-shape (↪*-step ∃↪t t↪*t')
  with ↪-∃-shape ∃↪t
...  |  t₁' ,  t₂' ,  refl ,  t₁↪*t₁' , t₂↪*t₂'    
  with ↪*-∃-shape t↪*t'
...  |  t₁'' ,  t₂'' ,  refl ,  t₁'↪*t₁'' , t₂'↪*t₂''    
  =  t₁'' ,  t₂'' ,  refl ,  ↪*-trans t₁↪*t₁' t₁'↪*t₁'' , ↪*-trans t₂↪*t₂' t₂'↪*t₂''    

invert-≈-∃ :
  (∃[x∶ t₁ ] t₂) ≈ (∃[x∶ t₁' ] t₂') →
  t₁ ≈ t₁' × t₂ ≈ t₂'
invert-≈-∃ (mk-≈ t ∃₁↪*t ∃₂↪*t)
  with ↪*-∃-shape ∃₁↪*t                                | ↪*-∃-shape ∃₂↪*t
... |  T₁ ,  T₂ ,  refl ,  t₁↪*T₁ , t₂↪*T₂     |  .T₁ ,  .T₂ ,  refl ,  t₁'↪*T₁ , t₂'↪*T₂    
  =  (mk-≈ T₁ t₁↪*T₁ t₁'↪*T₁) , (mk-≈ T₂ t₂↪*T₂ t₂'↪*T₂) 

invert-⊢,' : ∀ {e₁ : S ⊢ 𝕖} {t₂ : (𝕖 ∷ S) ⊢ 𝕖} →
  Γ ⊢ (e₁ `, e₂) ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    t ≈ (∃[x∶ t₁ ] t₂) ×
    Γ ⊢ e₁ ∶ t₁ ×
    Γ ⊢ e₂ ∶ t₂ ⋯ₛ ⦅ e₁ ⦆ₛ
invert-⊢,' (⊢, ⊢e₁ ⊢e₂) =  _ ,  _ ,  ≈-refl ,  ⊢e₁ , ⊢e₂    
invert-⊢,' {t₂ = t₂} (⊢≈ t≈t' ⊢e) with invert-⊢,' {t₂ = t₂} ⊢e
... |  t₁ ,  t₂ ,  t'≈∀[t₁]t₂ ,  ⊢t₁ , ⊢e     =  t₁ ,  t₂ ,  ≈-trans (≈-sym t≈t') t'≈∀[t₁]t₂ ,  ⊢t₁ , ⊢e    

invert-⊢, : ∀ {e₁ : S ⊢ 𝕖} {t₂ : (𝕖 ∷ S) ⊢ 𝕖} →
  Γ ⊢ (e₁ `, e₂) ∶ ∃[x∶ t₁ ] t₂ →
  ∃[ t₁' ] ∃[ t₂' ]
      t₁ ≈ t₁' ×
      t₂ ≈ t₂' ×
      Γ ⊢ e₁ ∶ t₁' ×
      Γ ⊢ e₂ ∶ t₂' ⋯ₛ ⦅ e₁ ⦆ₛ
invert-⊢, {t₂ = t₂} ⊢e
 with invert-⊢,' {t₂ = t₂} ⊢e
... |  t₁' ,  t₂' ,  eq ,  ⊢e₁ , ⊢e₂    
 with invert-≈-∃ eq
... |  t₁≈t₁' , t₂≈t₂' 
 =  t₁' ,  t₂' ,  t₁≈t₁' ,  t₂≈t₂' ,  ⊢e₁ , ⊢e₂     

--------------------------------------------------------------------------------

-- Inversion for equality terms

↪-≡-shape :
  (e₁ `≡ e₂) ↪ t → 
  ∃[ e₁' ] ∃[ e₂' ] t ≡ (e₁' `≡ e₂') × (e₁ ↪* e₁') × (e₂ ↪* e₂')
↪-≡-shape (ξ-≡₁ p) =  _ ,  _ ,  refl ,  ↪*-step p ↪*-refl , ↪*-refl    
↪-≡-shape (ξ-≡₂ p) =  _ ,  _ ,  refl ,  ↪*-refl , ↪*-step p ↪*-refl    

↪*-≡-shape :
  (e₁ `≡ e₂) ↪* t → 
  ∃[ e₁' ] ∃[ e₂' ] t ≡ (e₁' `≡ e₂') × (e₁ ↪* e₁') × (e₂ ↪* e₂')
↪*-≡-shape ↪*-refl =  _ ,  _ ,  refl ,  ↪*-refl , ↪*-refl    
↪*-≡-shape (↪*-step x p)
 with ↪-≡-shape x
... |  e₁ ,  e₂ ,  refl ,  p' , q'    
 with ↪*-≡-shape p
... |  e₁' ,  e₂' ,  eq' ,  p'' , q''    
 =  _ ,  _ ,  eq' ,  ↪*-trans p' p'' , ↪*-trans q' q''    

invert-≈-≡ :
  (e₁ `≡ e₂) ≈ (e₁' `≡ e₂') →
  (e₁ ≈ e₁') × (e₂ ≈ e₂')
invert-≈-≡ (mk-≈ t t₁↪*t t₂↪*t)
 with ↪*-≡-shape t₁↪*t                           | ↪*-≡-shape t₂↪*t
... |  e₁' ,  e₂' ,  refl ,  p' , q'     |  e₁'' ,  e₂'' ,  refl ,  p'' , q''    
 =  mk-≈ e₁' p' p'' , mk-≈ e₂' q' q'' 

invert-⊢refl' :
  Γ ⊢ `refl ∶ t →
  ∃[ e₁ ] ∃[ e₂ ] t ≈ (e₁ `≡ e₂) × e₁ ≈ e₂
invert-⊢refl' (⊢≈ t'≈t ⊢e) with invert-⊢refl' ⊢e
... |  e₁ ,  e₂ ,  t'≈[e₁≡e₂] , p    =  e₁ ,  e₂ ,  ≈-trans (≈-sym t'≈t) t'≈[e₁≡e₂] , p   
invert-⊢refl' (⊢refl ⊢e) =  _ ,  _ ,  ≈-refl , ≈-refl   

invert-⊢refl :
  Γ ⊢ `refl ∶ (e₁ `≡ e₂) →
  e₁ ≈ e₂
invert-⊢refl ⊢e
 with invert-⊢refl' ⊢e
... |  e₁' ,  e₂' ,  eq , e₁'≈e₂'   
 with invert-≈-≡ eq
... |  e₁≈e₁' , e₂≈e₂'  = ≈-trans e₁≈e₁' (≈-trans e₁'≈e₂' (≈-sym e₂≈e₂'))

--------------------------------------------------------------------------------

_⊢⋯_ :
  ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ TK : TypingKit K W C₁ C₂ ⦄
    ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ∋x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
⊢∀ ⊢t₁ ⊢t₂ ⊢⋯ ⊢ϕ = ⊢∀ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢t₂ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢λ ⊢t₁ ⊢e ⊢⋯ ⊢ϕ = ⊢λ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
_⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢· {e₁ = e₁} {t₂ = t₂} {e₂ = e₂} ⊢e₁ ⊢e₂) ⊢ϕ =
  subst (Γ₂ ⊢ (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ) ∶_)
        (sym (dist-⦅⦆-⋯ t₂ e₂ ϕ))
        (⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ))
⊢∃ ⊢t₁ ⊢t₂ ⊢⋯ ⊢ϕ = ⊢∃ (⊢t₁ ⊢⋯ ⊢ϕ) (⊢t₂ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
_⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢, {e₁ = e₁} {e₂ = e₂} {t₂ = t₂} ⊢e₁ ⊢e₂) ⊢ϕ =
  ⊢, (⊢e₁ ⊢⋯ ⊢ϕ)
     (subst (Γ₂ ⊢ (e₂ ⋯ ϕ) ∶_)
            (dist-⦅⦆-⋯ t₂ e₁ ϕ)
            (⊢e₂ ⊢⋯ ⊢ϕ))
⊢proj₁ ⊢e ⊢⋯ ⊢ϕ = ⊢proj₁ (⊢e ⊢⋯ ⊢ϕ)
_⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢proj₂ {e = e} {t₂ = t₂} ⊢e) ⊢ϕ =
  subst (Γ₂ ⊢ `proj₂ (e ⋯ ϕ) ∶_)
        (sym (dist-⦅⦆-⋯ t₂ (`proj₁ e) ϕ))
        (⊢proj₂ (⊢e ⊢⋯ ⊢ϕ))
⊢≡ ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢≡ (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢refl ⊢e ⊢⋯ ⊢ϕ = ⊢refl (⊢e ⊢⋯ ⊢ϕ)
_⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢J {t' = t'} {u₁ = u₁} {u₂ = u₂} {e₁ = e₁} {e₂ = e₂} {t = t} ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) ⊢ϕ =
  subst (Γ₂ ⊢ `J (t ⋯ (ϕ ↑ _)) (e₁ ⋯ ϕ) (e₂ ⋯ ϕ) ∶_)
        (sym (dist-⦅⦆-⋯ t u₂ ϕ))
        (⊢J (⊢t ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
            (⊢u₁ ⊢⋯ ⊢ϕ)
            (⊢u₂ ⊢⋯ ⊢ϕ)
            (⊢e₁ ⊢⋯ ⊢ϕ)
            (subst (Γ₂ ⊢ (e₂ ⋯ ϕ) ∶_)
                   (dist-⦅⦆-⋯ t u₁ ϕ)
                   (⊢e₂ ⊢⋯ ⊢ϕ) ))

⊢Set ⊢⋯ ⊢ϕ = ⊢Set
⊢≈ t≈t' ⊢e ⊢⋯ ⊢ϕ = ⊢≈ (≈-⋯ₖ t≈t') (⊢e ⊢⋯ ⊢ϕ)

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

--------------------------------------------------------------------------------

subject-reduction : ∀ {Γ : Ctx S} →
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢t ⊢e)   (ξ-λ e↪e')    = ⊢λ ⊢t (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂) β-λ           with invert-⊢λ ⊢e₁
...                                          |  t₁' ,  t₂' ,  t₁≈t₁' ,  t₂≈t₂' ,  ⊢t₁' , ⊢e₁'     
                                             = ⊢≈ (≈-sym t₂≈t₂') ⊢e₁' ⊢⋯ₛ ⊢⦅ ⊢≈ t₁≈t₁' ⊢e₂ ⦆ₛ
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· {t₂ = t₂} ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') = ⊢≈ (≈-⋯ {e = t₂} ≈-refl (≈→≈σ (≈-sym (↪→≈ e₂↪e₂'))))
                                                            (⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂'))
subject-reduction (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₁ t₁↪t₁') = ⊢∀ (subject-reduction ⊢t₁ t₁↪t₁') (≈-Γ-⊢₁ (↪→≈ t₁↪t₁') ⊢t₂)
subject-reduction (⊢∀ ⊢t₁ ⊢t₂) (ξ-∀₂ t₂↪t₂') = ⊢∀ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
subject-reduction (⊢≈ t≈t' ⊢e) e↪e'          = ⊢≈ t≈t' (subject-reduction ⊢e e↪e')
subject-reduction (⊢∃ ⊢t₁ ⊢t₂) (ξ-∃₁ t₁↪t₁') = ⊢∃ (subject-reduction ⊢t₁ t₁↪t₁') (≈-Γ-⊢₁ (↪→≈ t₁↪t₁') ⊢t₂)
subject-reduction (⊢∃ ⊢t₁ ⊢t₂) (ξ-∃₂ t₂↪t₂') = ⊢∃ ⊢t₁ (subject-reduction ⊢t₂ t₂↪t₂')
subject-reduction (⊢, {t₂ = t₂} ⊢e₁ ⊢e₂) (ξ-,₁ e₁↪e₁') = ⊢, (subject-reduction ⊢e₁ e₁↪e₁')
                                                            (⊢≈ (≈-⋯ {e = t₂} ≈-refl (≈→≈σ (↪→≈ e₁↪e₁'))) ⊢e₂)
subject-reduction (⊢, ⊢e₁ ⊢e₂) (ξ-,₂ e₂↪e₂') = ⊢, ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢proj₁ ⊢e) β-proj₁ with invert-⊢, ⊢e
... |  t₁' ,  t₂' ,  t₁≈t₁' ,  t₂≈t₂' ,  ⊢e₁ , ⊢e₂      = ⊢≈ (≈-sym t₁≈t₁') ⊢e₁
subject-reduction (⊢proj₁ ⊢e) (ξ-proj₁ e↪e') = ⊢proj₁ (subject-reduction ⊢e e↪e')
subject-reduction (⊢proj₂ ⊢e) β-proj₂ with invert-⊢, ⊢e
... |  t₁' ,  t₂' ,  t₁≈t₁' ,  t₂≈t₂' ,  ⊢e₁ , ⊢e₂      = ⊢≈ (≈-⋯ (≈-sym t₂≈t₂') (≈→≈σ (≈-sym (↪→≈ β-proj₁))))
                                                             ⊢e₂
subject-reduction (⊢proj₂ {t₂ = t₂} ⊢e) (ξ-proj₂ e↪e') = ⊢≈ (≈-⋯ {e = t₂} ≈-refl (≈→≈σ (≈-sym (↪→≈ (ξ-proj₁ e↪e')))))
                                                            (⊢proj₂ (subject-reduction ⊢e e↪e'))
subject-reduction (⊢≡ ⊢e₁ ⊢e₂) (ξ-≡₁ e₁↪e₁') = ⊢≡ (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢≡ ⊢e₁ ⊢e₂) (ξ-≡₂ e₂↪e₂') = ⊢≡ ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢J {t = t} ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) β-J with invert-⊢refl ⊢e₁
... | e₁'≈e₂' =
  ⊢≈ (≈-⋯ {e = t} ≈-refl (≈→≈σ e₁'≈e₂')) ⊢e₂
subject-reduction (⊢J ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) (ξ-J₁ t↪t') =
  ⊢≈ (≈-⋯ (≈-sym (↪→≈ t↪t')) ≈σ-refl) (⊢J (subject-reduction ⊢t t↪t') ⊢u₁ ⊢u₂ ⊢e₁ (⊢≈ (≈-⋯ (↪→≈ t↪t') ≈σ-refl) ⊢e₂))
subject-reduction (⊢J ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) (ξ-J₂ e₁↪e₁') = ⊢J ⊢t ⊢u₁ ⊢u₂ (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢J ⊢t ⊢u₁ ⊢u₂ ⊢e₁ ⊢e₂) (ξ-J₃ e₂↪e₂') = ⊢J ⊢t ⊢u₁ ⊢u₂ ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
