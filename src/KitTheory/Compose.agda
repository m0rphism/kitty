open import KitTheory.Modes
open import KitTheory.Kit using (KitTraversal)

module KitTheory.Compose {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id)
open import KitTheory.Prelude

open Modes 𝕄
open Terms 𝕋
open KitTheory.Kit 𝕋
open KitTheory.Kit.KitTraversal T

open Kit {{...}}

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- If the client provides a `KitAssoc` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeKit {{𝕂₁ : Kit}} {{𝕂₂ : Kit}} {{𝕂 : Kit}} : Set₁ where
  field
    _∘ₖ_ : µ₂ –[ 𝕂₁ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₃

    tm-⋯-∘ : (ρ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ρ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
      tm _ (ρ₁ _ x) ⋯ ρ₂ ≡ tm _ ((ρ₂ ∘ₖ ρ₁) _ x)

    dist-↑-∘ : ∀ m (f : µ₂ –[ 𝕂₁ ]→ µ₃) (g : µ₁ –[ 𝕂₂ ]→ µ₂) →
      (f ∘ₖ g) ↑ m ≡ (f ↑ m) ∘ₖ (g ↑ m)

record KitAssoc : Set₁ where
  open ComposeKit {{...}}

  field
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)

  ∘≡∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit {{𝕂₂ }} {{𝕂₁ }} {{𝕂}} }}
              {{𝔸' : ComposeKit {{𝕂₂'}} {{𝕂₁'}} {{𝕂}} }}
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

  private instance _ = kitᵣ
  private instance _ = kitₛ

  kitᵣᵣ : ComposeKit {{kitᵣ}} {{kitᵣ}} {{kitᵣ}}
  ComposeKit._∘ₖ_     kitᵣᵣ = _ᵣ∘ᵣ_
  ComposeKit.tm-⋯-∘   kitᵣᵣ = λ ρ₁ ρ₂ x → ⋯-var (ρ₁ _ x) ρ₂ where instance _ = kitᵣ
  ComposeKit.dist-↑-∘ kitᵣᵣ = λ _ f g → fun-ext₂ λ where
                                                  _ (here px) → refl
                                                  _ (there x) → refl

  kitₛᵣ : ComposeKit {{kitₛ}} {{kitᵣ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitₛᵣ = _ₛ∘ᵣ_
  ComposeKit.tm-⋯-∘   kitₛᵣ = λ σ₁ ρ₂ x → ⋯-var (σ₁ _ x) ρ₂ where instance _ = kitₛ
  ComposeKit.dist-↑-∘ kitₛᵣ = λ _ f g → fun-ext₂ λ where
                                                  _ (here px) → refl
                                                  _ (there x) → refl

  private instance _ = kitᵣᵣ
  private instance _ = kitₛᵣ

  kitᵣₛ : ComposeKit {{kitᵣ}} {{kitₛ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitᵣₛ = _ᵣ∘ₛ_
  ComposeKit.tm-⋯-∘   kitᵣₛ = λ ρ₁ σ₂ x → refl
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

  private instance _ = kitᵣₛ

  kitₛₛ : ComposeKit {{kitₛ}} {{kitₛ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitₛₛ = _ₛ∘ₛ_
  ComposeKit.tm-⋯-∘   kitₛₛ = λ σ₁ σ₂ x → refl
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

  private instance _ = kitₛₛ

  dist-↑-sub : ∀ (v : µ₁ ⊢ M) (σ : µ₁ →ₛ µ₂) →
    v ⋯ wk ⋯ (σ ↑ m) ≡ v ⋯ σ ⋯ wk
  dist-↑-sub {m = m} v σ =
    (v ⋯ wk) ⋯ (σ ↑ₛ m)   ≡⟨ ⋯-assoc v wk (σ ↑ m) ⟩
    v ⋯ ((σ ↑ₛ m) ₛ∘ᵣ wk) ≡⟨ refl ⟩
    v ⋯ (wk ᵣ∘ₛ σ)        ≡⟨ sym (⋯-assoc v σ wk) ⟩
    (v ⋯ σ) ⋯ wk          ∎

  dist-↑-ren : ∀ {µ₁ µ₂ M m} (v : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
    v ⋯ wk ⋯ (ρ ↑ m) ≡ v ⋯ ρ ⋯ wk
  dist-↑-ren {m = m} v ρ =
    v ⋯ wk ⋯ (ρ ↑ m)  ≡⟨ ⋯-assoc v wk (ρ ↑ m)  ⟩
    v ⋯ (ρ ↑ m) ∘ᵣ wk ≡⟨ refl ⟩
    v ⋯ wk ∘ᵣ ρ       ≡⟨ sym (⋯-assoc v ρ wk) ⟩
    v ⋯ ρ ⋯ wk        ∎

  wk-cancels-,ₛ : ∀ {µ₁ µ₂ M m} (v : µ₁ ⊢ M) (v' : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
    wk _ v ⋯ (σ ,ₛ v') ≡ v ⋯ σ
  wk-cancels-,ₛ v v' σ = ⋯-assoc v wk (σ ,ₛ v')

  wk-cancels-,ᵣ : ∀ {µ₁ µ₂ M m} (v : µ₁ ⊢ M) (v' : µ₂ ∋ m) (σ : µ₁ →ᵣ µ₂) →
    wk _ v ⋯ (σ ,ᵣ v') ≡ v ⋯ σ
  wk-cancels-,ᵣ v v' ρ = ⋯-assoc v wk (ρ ,ᵣ v')

  record KitAssocLemmas : Set₁ where
    open ComposeKit {{...}}

    field
      ⋯-id : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

    ⋯-idₛ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitₛ}} ≡ v
    ⋯-idₛ = ⋯-id

    ⋯-idᵣ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitᵣ}} ≡ v
    ⋯-idᵣ = ⋯-id

    wk-cancels-⦅⦆ₛ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ⊢ m→M m) →
      wk _ v ⋯ ⦅ v' ⦆ₛ ≡ v
    wk-cancels-⦅⦆ₛ v v' =
      wk _ v ⋯ ⦅ v' ⦆ₛ ≡⟨ wk-cancels-,ₛ v v' idₛ ⟩
      v ⋯ idₛ          ≡⟨ ⋯-id v ⟩
      v                ∎

    wk-cancels-⦅⦆ᵣ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ∋ m) →
      wk _ v ⋯ ⦅ v' ⦆ᵣ ≡ v
    wk-cancels-⦅⦆ᵣ v v' =
      wk _ v ⋯ ⦅ v' ⦆ᵣ ≡⟨ wk-cancels-,ᵣ v v' idᵣ ⟩
      v ⋯ idᵣ          ≡⟨ ⋯-id v ⟩
      v                ∎

    dist-ᵣ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ∋ m) (σ : µ₁ →ᵣ µ₂) →
      σ ᵣ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ᵣ∘ᵣ (σ ↑ m)
    dist-ᵣ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
      _ (here refl) → refl
      _ (there x) → refl

    dist-ᵣ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (σ : µ₁ →ᵣ µ₂) →
      σ ᵣ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ₛ∘ᵣ (σ ↑ m)
    dist-ᵣ∘ₛ-⦅⦆ t σ = fun-ext₂ λ where
      _ (here refl) → refl
      _ (there x) → ⋯-var x σ

    dist-ₛ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      σ ₛ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ₛ∘ₛ (σ ↑ m)
    dist-ₛ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
      _ (here refl) → sym (⋯-var (here refl) ⦅ σ _ t ⦆)
      _ (there x) →
        σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
        σ _ x ⋯ ((idₖ ,ₖ (σ _ t)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ σ _ t ⦆) ⟩
        (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (σ _ t))   ∎

    dist-ₛ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      σ ₛ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ₛ∘ₛ (σ ↑ m)
    dist-ₛ∘ₛ-⦅⦆ t σ = fun-ext₂ λ where
      _ (here refl) →
        t ⋯ σ                     ≡⟨⟩
        ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
        (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
      _ (there x) →
        (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
        σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
        σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
        (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎

    dist-⦅⦆ᵣ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ∋ m) (σ : µ₁ →ᵣ µ₂) →
      t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ σ _ t ⦆
    dist-⦅⦆ᵣ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ t σ) t₂

    dist-⦅⦆ₛ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ⊢ m→M m) (σ : µ₁ →ᵣ µ₂) →
      t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ t ⋯ σ ⦆
    dist-⦅⦆ₛ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t σ) t₂

    dist-⦅⦆ᵣ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ σ _ t ⦆
    dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

    dist-⦅⦆ₛ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ t ⋯ σ ⦆
    dist-⦅⦆ₛ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ₛ-⦅⦆ t σ) t₂

  -- record KitTraversalLemmas : Set₁ where
  --   open AssocAssumptions {{...}}
  --   field
  --     {{kit-traversal}} : KitTraversal
  --     ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ K) → v ⋯ idₖ {{𝕂}} ≡ v

  --   dist-∘-⦅⦆ :
  --     ∀ {{𝕂₁ : Kit }}
  --       {{𝕂₂ : Kit }}
  --       {{𝕂  : Kit }}
  --       {{𝔸₁ : AssocAssumptions {{kit-traversal}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
  --       {{𝔸₂ : AssocAssumptions {{kit-traversal}} {{𝕂₂}} {{𝕂₁}} {{𝕂}} }}
  --       {{_ : KitCompose {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{kit-traversal}} {{𝔸₁}} }}
  --       {{_ : KitCompose {{𝕂₂}} {{𝕂₁}} {{𝕂}} {{kit-traversal}} {{𝔸₂}} }}
  --       (t : µ ◆ k→SK k) (σ : µ₁ –[ 𝕂₁ ]→ µ₂) →
  --     σ ∘ₖ ⦅ t ⦆ ≡ ⦅ tm _ t ⋯ σ ⦆ ∘ₖ (σ ↑ k)
  --   -- ⦅_⦆ : µ ◆ k→SK k → (k ∷ µ) –→ µ
  --   dist-∘-⦅⦆ t σ = {!!}
  --   -- dist-∘-⦅⦆ t σ = fun-ext₂ λ where
  --   --   _ (here refl) →
  --   --     t ⋯ σ                     ≡⟨⟩
  --   --     ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
  --   --     (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
  --   --   _ (there x) →
  --   --     (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
  --   --     σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
  --   --     σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
  --   --     (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎
