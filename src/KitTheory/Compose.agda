open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Compose
    (VarKind  : Set)
    (TermKind : Set)
    (k→K      : VarKind → TermKind)
    (_⊢_      : List VarKind → TermKind → Set)
    (`_       : ∀ {κ k} → k ∈ κ → κ ⊢ k→K k)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id)

open import KitTheory.Kit VarKind TermKind k→K _⊢_ `_

open Kit {{...}}
open KitTraversal {{...}}

private
  variable
    k k' k₁ k₂    : VarKind
    κ κ' κ₁ κ₂ κ₃ : List VarKind
    K K' K₁ K₂    : TermKind
    x y z         : k ∈ κ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

-- If the client provides a `KitAssoc` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeKit {{Trav : KitTraversal}} {{𝕂₁ : Kit}} {{𝕂₂ : Kit}} {{𝕂 : Kit}} : Set₁ where
  field
    _∘ₖ_ : κ₂ –[ 𝕂₁ ]→ κ₃ → κ₁ –[ 𝕂₂ ]→ κ₂ → κ₁ –[ 𝕂 ]→ κ₃

    tm'-⋯-∘ : ∀ {k} (ρ₁ : κ₁ –[ 𝕂₂ ]→ κ₂) (ρ₂ : κ₂ –[ 𝕂₁ ]→ κ₃) (x : κ₁ ∋ k) →
      tm' (ρ₁ _ x) ⋯ ρ₂ ≡ tm' ((ρ₂ ∘ₖ ρ₁) _ x)

    dist-↑-∘ : ∀ k (f : κ₂ –[ 𝕂₁ ]→ κ₃) (g : κ₁ –[ 𝕂₂ ]→ κ₂) →
      (f ∘ₖ g) ↑ k ≡ (f ↑ k) ∘ₖ (g ↑ k)

record KitAssoc {{T : KitTraversal}} : Set₁ where
  open ComposeKit {{...}}
  field
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{T}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : κ₁ ⊢ K) (ρ₁ : κ₁ –[ 𝕂₂ ]→ κ₂) (ρ₂ : κ₂ –[ 𝕂₁ ]→ κ₃) →
      v ⋯ ρ₁ ⋯ ρ₂ ≡ v ⋯ (ρ₂ ∘ₖ ρ₁)

  ∘≡∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit {{_}} {{𝕂₂ }} {{𝕂₁ }} {{𝕂}} }}
              {{𝔸' : ComposeKit {{_}} {{𝕂₂'}} {{𝕂₁'}} {{𝕂}} }}
              {κ₂'}
              {f  : κ₁ –[ 𝕂₁  ]→ κ₂ } {g  : κ₂  –[ 𝕂₂  ]→ κ₃}
              {f' : κ₁ –[ 𝕂₁' ]→ κ₂'} {g' : κ₂' –[ 𝕂₂' ]→ κ₃} →
    g ∘ₖ f ≡ g' ∘ₖ f' →
    ∀ {K} (t : κ₁ ⊢ K) →
    t ⋯ f ⋯ g ≡ t ⋯ f' ⋯ g'
  ∘≡∘→⋯≡⋯ {f = f} {g = g} {f' = f'} {g' = g'} eq t =
    t ⋯ f ⋯ g    ≡⟨ ⋯-assoc t f g ⟩
    t ⋯ g ∘ₖ f   ≡⟨ cong (t ⋯_) eq ⟩
    t ⋯ g' ∘ₖ f' ≡⟨ sym (⋯-assoc t f' g') ⟩
    t ⋯ f' ⋯ g'  ∎

  -- Example:
  --
  --   instance ckit : KitAssoc {{traversal}}
  --   KitAssoc.⋯-assoc ckit (` x) f g =
  --     tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  --     tm' ((g ∘ₖ f) _ x) ∎
  --   KitAssoc.⋯-assoc ckit (λ→ e) f g = cong λ→_
  --     (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  --      e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  --      e ⋯ (g ∘ₖ f) ↑ _         ∎)
  --   KitAssoc.⋯-assoc ckit (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

open KitAssoc {{...}}

kitᵣᵣ : {{T : KitTraversal}} →
                     ComposeKit {{T}} {{kitᵣ}} {{kitᵣ}} {{kitᵣ}}
ComposeKit._∘ₖ_     kitᵣᵣ = _ᵣ∘ᵣ_
ComposeKit.tm'-⋯-∘  kitᵣᵣ = λ ρ₁ ρ₂ x → ⋯-var (ρ₁ _ x) ρ₂ where instance _ = kitᵣ
ComposeKit.dist-↑-∘ kitᵣᵣ = λ _ f g → fun-ext₂ λ where
                                                 _ (here px) → refl
                                                 _ (there x) → refl

kitₛᵣ : {{T : KitTraversal}} →
                     ComposeKit {{T}} {{kitₛ}} {{kitᵣ}} {{kitₛ}}
ComposeKit._∘ₖ_     kitₛᵣ = _ₛ∘ᵣ_
ComposeKit.tm'-⋯-∘  kitₛᵣ = λ σ₁ ρ₂ x → ⋯-var (σ₁ _ x) ρ₂ where instance _ = kitₛ
ComposeKit.dist-↑-∘ kitₛᵣ = λ _ f g → fun-ext₂ λ where
                                                 _ (here px) → refl
                                                 _ (there x) → refl

kitᵣₛ : {{T : KitTraversal}} {{_ : KitAssoc {{T}} }} →
                     ComposeKit {{T}} {{kitᵣ}} {{kitₛ}} {{kitₛ}}
ComposeKit._∘ₖ_     kitᵣₛ = _ᵣ∘ₛ_
ComposeKit.tm'-⋯-∘  kitᵣₛ = λ ρ₁ σ₂ x → refl
ComposeKit.dist-↑-∘ kitᵣₛ =
  λ k₁ ρ σ → fun-ext₂ λ where
      k (here refl) →
        ((ρ ᵣ∘ₛ σ) ↑ k) k (here refl)       ≡⟨⟩
        (` here refl)                       ≡⟨⟩
        (` ((ρ ↑ k₁) _ (here refl)))        ≡⟨ sym (⋯-var (here refl) (ρ ↑ k₁)) ⟩
        ((` here refl) ⋯ (ρ ↑ k₁))          ≡⟨⟩
        ((ρ ↑ k) ᵣ∘ₛ (σ ↑ k)) k (here refl) ∎
      k (there x)   →
        (σ k x ⋯ ρ) ⋯ wk          ≡⟨ ⋯-assoc (σ k x) ρ wk ⟩
        σ k x ⋯ (wk ᵣ∘ᵣ ρ)        ≡⟨⟩
        σ k x ⋯ ((ρ ↑ k₁) ᵣ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ k x) wk (ρ ↑ k₁)) ⟩
        (σ k x ⋯ wk) ⋯ (ρ ↑ k₁)   ∎
    where instance _ = kitₛ
                   _ = kitᵣ
                   _ = kitᵣᵣ

kitₛₛ : {{T : KitTraversal}} {{_ : KitAssoc {{T}} }} →
                     ComposeKit {{T}} {{kitₛ}} {{kitₛ}} {{kitₛ}}
ComposeKit._∘ₖ_     kitₛₛ = _ₛ∘ₛ_
ComposeKit.tm'-⋯-∘  kitₛₛ = λ σ₁ σ₂ x → refl
ComposeKit.dist-↑-∘ kitₛₛ =
  λ k₁ σ₁ σ₂ → fun-ext₂ λ where
      k (here refl) →
        (` here refl)             ≡⟨ sym (⋯-var (here refl) (σ₁ ↑ k₁)) ⟩
        (` here refl) ⋯ (σ₁ ↑ k₁) ∎
      k (there x)   →
        (σ₂ k x ⋯ σ₁) ⋯ wk          ≡⟨ ⋯-assoc (σ₂ k x) σ₁ wk ⟩
        σ₂ k x ⋯ (wk ᵣ∘ₛ σ₁)        ≡⟨⟩
        σ₂ k x ⋯ ((σ₁ ↑ k₁) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ₂ k x) wk (σ₁ ↑ k₁)) ⟩
        (σ₂ k x ⋯ wk) ⋯ (σ₁ ↑ k₁)   ∎
    where instance _ = kitₛ
                   _ = kitᵣ
                   _ = kitᵣₛ
                   _ = kitₛᵣ
