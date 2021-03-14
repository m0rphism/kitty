open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Compose
    (VarMode  : Set)
    (TermMode : Set)
    (m→M      : VarMode → TermMode)
    (_⊢_      : List VarMode → TermMode → Set)
    (`_       : ∀ {µ m} → m ∈ µ → µ ⊢ m→M m)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id)

open import KitTheory.Kit VarMode TermMode m→M _⊢_ `_

open Kit {{...}}
open KitTraversal {{...}}

private
  variable
    m m' m₁ m₂    : VarMode
    µ µ' µ₁ µ₂ µ₃ : List VarMode
    M M' M₁ M₂    : TermMode
    x y z         : m ∈ µ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

-- If the client provides a `KitAssoc` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeKit {{Trav : KitTraversal}} {{𝕂₁ : Kit}} {{𝕂₂ : Kit}} {{𝕂 : Kit}} : Set₁ where
  field
    _∘ₖ_ : µ₂ –[ 𝕂₁ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₃

    tm'-⋯-∘ : ∀ {m} (ρ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ρ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
      tm' (ρ₁ _ x) ⋯ ρ₂ ≡ tm' ((ρ₂ ∘ₖ ρ₁) _ x)

    dist-↑-∘ : ∀ m (f : µ₂ –[ 𝕂₁ ]→ µ₃) (g : µ₁ –[ 𝕂₂ ]→ µ₂) →
      (f ∘ₖ g) ↑ m ≡ (f ↑ m) ∘ₖ (g ↑ m)

record KitAssoc {{T : KitTraversal}} : Set₁ where
  open ComposeKit {{...}}
  field
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{T}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)

  ∘≡∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit {{_}} {{𝕂₂ }} {{𝕂₁ }} {{𝕂}} }}
              {{𝔸' : ComposeKit {{_}} {{𝕂₂'}} {{𝕂₁'}} {{𝕂}} }}
              {µ₂'}
              {f  : µ₁ –[ 𝕂₁  ]→ µ₂ } {g  : µ₂  –[ 𝕂₂  ]→ µ₃}
              {f' : µ₁ –[ 𝕂₁' ]→ µ₂'} {g' : µ₂' –[ 𝕂₂' ]→ µ₃} →
    g ∘ₖ f ≡ g' ∘ₖ f' →
    ∀ {M} (t : µ₁ ⊢ M) →
    t ⋯ f ⋯ g ≡ t ⋯ f' ⋯ g'
  ∘≡∘→⋯≡⋯ {f = f} {g = g} {f' = f'} {g' = g'} eq t =
    t ⋯ f ⋯ g    ≡⟨ ⋯-assoc t f g ⟩
    t ⋯ g ∘ₖ f   ≡⟨ cong (t ⋯_) eq ⟩
    t ⋯ g' ∘ₖ f' ≡⟨ sym (⋯-assoc t f' g') ⟩
    t ⋯ f' ⋯ g'  ∎

  -- Example:
  --
  --   instance kit-assoc : KitAssoc {{traversal}}
  --   KitAssoc.⋯-assoc kit-assoc (` x) f g =
  --     tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  --     tm' ((g ∘ₖ f) _ x) ∎
  --   KitAssoc.⋯-assoc kit-assoc (λ→ e) f g = cong λ→_
  --     (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  --      e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  --      e ⋯ (g ∘ₖ f) ↑ _         ∎)
  --   KitAssoc.⋯-assoc kit-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

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
  λ m₁ ρ σ → fun-ext₂ λ where
      m (here refl) →
        ((ρ ᵣ∘ₛ σ) ↑ m) m (here refl)       ≡⟨⟩
        (` here refl)                       ≡⟨⟩
        (` ((ρ ↑ m₁) _ (here refl)))        ≡⟨ sym (⋯-var (here refl) (ρ ↑ m₁)) ⟩
        ((` here refl) ⋯ (ρ ↑ m₁))          ≡⟨⟩
        ((ρ ↑ m) ᵣ∘ₛ (σ ↑ m)) m (here refl) ∎
      m (there x)   →
        (σ m x ⋯ ρ) ⋯ wk          ≡⟨ ⋯-assoc (σ m x) ρ wk ⟩
        σ m x ⋯ (wk ᵣ∘ᵣ ρ)        ≡⟨⟩
        σ m x ⋯ ((ρ ↑ m₁) ᵣ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ m x) wk (ρ ↑ m₁)) ⟩
        (σ m x ⋯ wk) ⋯ (ρ ↑ m₁)   ∎
    where instance _ = kitₛ
                   _ = kitᵣ
                   _ = kitᵣᵣ

kitₛₛ : {{T : KitTraversal}} {{_ : KitAssoc {{T}} }} →
        ComposeKit {{T}} {{kitₛ}} {{kitₛ}} {{kitₛ}}
ComposeKit._∘ₖ_     kitₛₛ = _ₛ∘ₛ_
ComposeKit.tm'-⋯-∘  kitₛₛ = λ σ₁ σ₂ x → refl
ComposeKit.dist-↑-∘ kitₛₛ =
  λ m₁ σ₁ σ₂ → fun-ext₂ λ where
      m (here refl) →
        (` here refl)             ≡⟨ sym (⋯-var (here refl) (σ₁ ↑ m₁)) ⟩
        (` here refl) ⋯ (σ₁ ↑ m₁) ∎
      m (there x)   →
        (σ₂ m x ⋯ σ₁) ⋯ wk          ≡⟨ ⋯-assoc (σ₂ m x) σ₁ wk ⟩
        σ₂ m x ⋯ (wk ᵣ∘ₛ σ₁)        ≡⟨⟩
        σ₂ m x ⋯ ((σ₁ ↑ m₁) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ₂ m x) wk (σ₁ ↑ m₁)) ⟩
        (σ₂ m x ⋯ wk) ⋯ (σ₁ ↑ m₁)   ∎
    where instance _ = kitₛ
                   _ = kitᵣ
                   _ = kitᵣₛ
                   _ = kitₛᵣ
