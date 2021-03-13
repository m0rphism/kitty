open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.ComposeLemmas
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

open import KitTheory.Kit     VarMode TermMode m→M _⊢_ `_
open import KitTheory.Compose VarMode TermMode m→M _⊢_ `_

open Kit {{...}}
open KitTraversal {{...}}
open ComposeKit {{...}}
open KitAssoc {{...}}

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kitᵣᵣ
private instance _ = kitᵣₛ
private instance _ = kitₛᵣ
private instance _ = kitₛₛ

private
  variable
    m m' m₁ m₂    : VarMode
    µ µ' µ₁ µ₂ µ₃ : List VarMode
    M M' M₁ M₂    : TermMode
    x y z         : m ∈ µ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

dist-↑-sub : ∀ {{T : KitTraversal}}
               {{_ : KitAssoc {{T}} }}
               (v : µ₁ ⊢ M) (σ : µ₁ →ₛ µ₂) →
  v ⋯ wk ⋯ (σ ↑ m) ≡ v ⋯ σ ⋯ wk
dist-↑-sub {m = m} v σ =
  (v ⋯ wk) ⋯ (σ ↑ₛ m)   ≡⟨ ⋯-assoc v wk (σ ↑ m) ⟩
  v ⋯ ((σ ↑ₛ m) ₛ∘ᵣ wk) ≡⟨ refl ⟩
  v ⋯ (wk ᵣ∘ₛ σ)        ≡⟨ sym (⋯-assoc v σ wk) ⟩
  (v ⋯ σ) ⋯ wk          ∎

dist-↑-ren : ∀ {{T : KitTraversal}} {{_ : KitAssoc {{T}} }}
               (v : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
  v ⋯ wk ⋯ (ρ ↑ m) ≡ v ⋯ ρ ⋯ wk
dist-↑-ren {m = m} v ρ =
  v ⋯ wk ⋯ (ρ ↑ m)  ≡⟨ ⋯-assoc v wk (ρ ↑ m)  ⟩
  v ⋯ (ρ ↑ m) ∘ᵣ wk ≡⟨ refl ⟩
  v ⋯ wk ∘ᵣ ρ       ≡⟨ sym (⋯-assoc v ρ wk) ⟩
  v ⋯ ρ ⋯ wk        ∎

wk-cancels-,ₛ : ∀ {{T : KitTraversal}} {{_ : KitAssoc {{T}} }}
                  (v : µ₁ ⊢ M) (v' : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
  wk _ v ⋯ (σ ,ₛ v') ≡ v ⋯ σ
wk-cancels-,ₛ v v' σ = ⋯-assoc v wk (σ ,ₛ v')

wk-cancels-,ᵣ : ∀ {{T : KitTraversal}} {{_ : KitAssoc {{T}} }}
                  (v : µ₁ ⊢ M) (v' : µ₂ ∋ m) (σ : µ₁ →ᵣ µ₂) →
  wk _ v ⋯ (σ ,ᵣ v') ≡ v ⋯ σ
wk-cancels-,ᵣ v v' ρ = ⋯-assoc v wk (ρ ,ᵣ v')

record KitAssocLemmas : Set₁ where
  open ComposeKit {{...}}
  field
    {{kit-traversal}} : KitTraversal
    {{kit-assoc}} : KitAssoc {{kit-traversal}}
    ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

  dist-ᵣ∘ᵣ-⦅⦆ : ∀ (t : µ₁ ∋ m) (σ : µ₁ →ᵣ µ₂) →
    σ ᵣ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ᵣ∘ᵣ (σ ↑ m)
  dist-ᵣ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → refl
    _ (there x) → refl

  dist-ᵣ∘ₛ-⦅⦆ : ∀ (t : µ₁ ⊢ m→M m) (σ : µ₁ →ᵣ µ₂) →
    σ ᵣ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ₛ∘ᵣ (σ ↑ m)
  dist-ᵣ∘ₛ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → refl
    _ (there x) → ⋯-var x σ

  dist-ₛ∘ᵣ-⦅⦆ : ∀ (t : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
    σ ₛ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ₛ∘ₛ (σ ↑ m)
  dist-ₛ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → sym (⋯-var (here refl) ⦅ σ _ t ⦆)
    _ (there x) →
      σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
      σ _ x ⋯ ((idₖ ,ₖ (σ _ t)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ σ _ t ⦆) ⟩
      (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (σ _ t))   ∎

  dist-ₛ∘ₛ-⦅⦆ : ∀ (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
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

  dist-⦅⦆ᵣ-⋯ᵣ : ∀ (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ∋ m) (σ : µ₁ →ᵣ µ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ σ _ t ⦆
  dist-⦅⦆ᵣ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ t σ) t₂

  dist-⦅⦆ₛ-⋯ᵣ : ∀ (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ⊢ m→M m) (σ : µ₁ →ᵣ µ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ t ⋯ σ ⦆
  dist-⦅⦆ₛ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t σ) t₂

  dist-⦅⦆ᵣ-⋯ₛ : ∀ (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ m) ⋯ ⦅ σ _ t ⦆
  dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

  dist-⦅⦆ₛ-⋯ₛ : ∀ (t₂ : (m ∷ µ₁) ⊢ M) (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
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
