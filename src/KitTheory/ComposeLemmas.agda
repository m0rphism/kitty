open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.ComposeLemmas
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

open import KitTheory.Kit     VarKind TermKind k→K _⊢_ `_
open import KitTheory.Compose VarKind TermKind k→K _⊢_ `_

open Kit {{...}}
open KitTraversal {{...}}
open AssocAssumptions {{...}}
open KitCompose {{...}}

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = AssocAssumptionsᵣᵣ
private instance _ = AssocAssumptionsᵣₛ
private instance _ = AssocAssumptionsₛᵣ
private instance _ = AssocAssumptionsₛₛ

private
  variable
    k k' k₁ k₂    : VarKind
    κ κ' κ₁ κ₂ κ₃ : List VarKind
    K K' K₁ K₂    : TermKind
    x y z         : k ∈ κ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

dist-↑-sub : ∀ {{T : KitTraversal}}
               {{_ : KitCompose {{T}} }}
               (v : κ₁ ⊢ K) (σ : κ₁ →ₛ κ₂) →
  v ⋯ wk ⋯ (σ ↑ k) ≡ v ⋯ σ ⋯ wk
dist-↑-sub {k = k} v σ =
  (v ⋯ wk) ⋯ (σ ↑ₛ k)   ≡⟨ ⋯-assoc v wk (σ ↑ k) ⟩
  v ⋯ ((σ ↑ₛ k) ₛ∘ᵣ wk) ≡⟨ refl ⟩
  v ⋯ (wk ᵣ∘ₛ σ)        ≡⟨ sym (⋯-assoc v σ wk) ⟩
  (v ⋯ σ) ⋯ wk          ∎

dist-↑-ren : ∀ {{T : KitTraversal}} {{_ : KitCompose {{T}} }}
               (v : κ₁ ⊢ K) (ρ : κ₁ →ᵣ κ₂) →
  v ⋯ wk ⋯ (ρ ↑ k) ≡ v ⋯ ρ ⋯ wk
dist-↑-ren {k = k} v ρ =
  v ⋯ wk ⋯ (ρ ↑ k)  ≡⟨ ⋯-assoc v wk (ρ ↑ k)  ⟩
  v ⋯ (ρ ↑ k) ∘ᵣ wk ≡⟨ refl ⟩
  v ⋯ wk ∘ᵣ ρ       ≡⟨ sym (⋯-assoc v ρ wk) ⟩
  v ⋯ ρ ⋯ wk        ∎

wk-cancels-,ₛ : ∀ {{T : KitTraversal}} {{_ : KitCompose {{T}} }}
                  (v : κ₁ ⊢ K) (v' : κ₂ ⊢ k→K k) (σ : κ₁ →ₛ κ₂) →
  wk _ v ⋯ (σ ,ₛ v') ≡ v ⋯ σ
wk-cancels-,ₛ v v' σ = ⋯-assoc v wk (σ ,ₛ v')

wk-cancels-,ᵣ : ∀ {{T : KitTraversal}} {{_ : KitCompose {{T}} }}
                  (v : κ₁ ⊢ K) (v' : κ₂ ∋ k) (σ : κ₁ →ᵣ κ₂) →
  wk _ v ⋯ (σ ,ᵣ v') ≡ v ⋯ σ
wk-cancels-,ᵣ v v' ρ = ⋯-assoc v wk (ρ ,ᵣ v')

record KitComposeLemmas : Set₁ where
  open AssocAssumptions {{...}}
  field
    {{kit-traversal}} : KitTraversal
    {{ckit}} : KitCompose {{kit-traversal}}
    ⋯-id : ∀ {{𝕂 : Kit}} (v : κ ⊢ K) → v ⋯ idₖ {{𝕂}} ≡ v

  dist-ᵣ∘ᵣ-⦅⦆ : ∀ (t : κ₁ ∋ k) (σ : κ₁ →ᵣ κ₂) →
    σ ᵣ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ᵣ∘ᵣ (σ ↑ k)
  dist-ᵣ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → refl
    _ (there x) → refl

  dist-ᵣ∘ₛ-⦅⦆ : ∀ (t : κ₁ ⊢ k→K k) (σ : κ₁ →ᵣ κ₂) →
    σ ᵣ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ₛ∘ᵣ (σ ↑ k)
  dist-ᵣ∘ₛ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → refl
    _ (there x) → ⋯-var x σ

  dist-ₛ∘ᵣ-⦅⦆ : ∀ (t : κ₁ ∋ k) (σ : κ₁ →ₛ κ₂) →
    σ ₛ∘ᵣ ⦅ t ⦆ ≡ ⦅ σ _ t ⦆ ₛ∘ₛ (σ ↑ k)
  dist-ₛ∘ᵣ-⦅⦆ t σ = fun-ext₂ λ where
    _ (here refl) → sym (⋯-var (here refl) ⦅ σ _ t ⦆)
    _ (there x) →
      σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
      σ _ x ⋯ ((idₖ ,ₖ (σ _ t)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ σ _ t ⦆) ⟩
      (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (σ _ t))   ∎

  dist-ₛ∘ₛ-⦅⦆ : ∀ (t : κ₁ ⊢ k→K k) (σ : κ₁ →ₛ κ₂) →
    σ ₛ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ₛ∘ₛ (σ ↑ k)
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

  dist-⦅⦆ᵣ-⋯ᵣ : ∀ (t₂ : (k ∷ κ₁) ⊢ K) (t : κ₁ ∋ k) (σ : κ₁ →ᵣ κ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ k) ⋯ ⦅ σ _ t ⦆
  dist-⦅⦆ᵣ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ t σ) t₂

  dist-⦅⦆ₛ-⋯ᵣ : ∀ (t₂ : (k ∷ κ₁) ⊢ K) (t : κ₁ ⊢ k→K k) (σ : κ₁ →ᵣ κ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ k) ⋯ ⦅ t ⋯ σ ⦆
  dist-⦅⦆ₛ-⋯ᵣ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t σ) t₂

  dist-⦅⦆ᵣ-⋯ₛ : ∀ (t₂ : (k ∷ κ₁) ⊢ K) (t : κ₁ ∋ k) (σ : κ₁ →ₛ κ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ k) ⋯ ⦅ σ _ t ⦆
  dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

  dist-⦅⦆ₛ-⋯ₛ : ∀ (t₂ : (k ∷ κ₁) ⊢ K) (t : κ₁ ⊢ k→K k) (σ : κ₁ →ₛ κ₂) →
    t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ k) ⋯ ⦅ t ⋯ σ ⦆
  dist-⦅⦆ₛ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ₛ-⦅⦆ t σ) t₂

-- record KitTraversalLemmas : Set₁ where
--   open AssocAssumptions {{...}}
--   field
--     {{kit-traversal}} : KitTraversal
--     ⋯-id : ∀ {{𝕂 : Kit}} (v : κ ⊢ K) → v ⋯ idₖ {{𝕂}} ≡ v

--   dist-∘-⦅⦆ :
--     ∀ {{𝕂₁ : Kit }}
--       {{𝕂₂ : Kit }}
--       {{𝕂  : Kit }}
--       {{𝔸₁ : AssocAssumptions {{kit-traversal}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
--       {{𝔸₂ : AssocAssumptions {{kit-traversal}} {{𝕂₂}} {{𝕂₁}} {{𝕂}} }}
--       {{_ : KitCompose {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{kit-traversal}} {{𝔸₁}} }}
--       {{_ : KitCompose {{𝕂₂}} {{𝕂₁}} {{𝕂}} {{kit-traversal}} {{𝔸₂}} }}
--       (t : κ ◆ k→SK k) (σ : κ₁ –[ 𝕂₁ ]→ κ₂) →
--     σ ∘ₖ ⦅ t ⦆ ≡ ⦅ tm _ t ⋯ σ ⦆ ∘ₖ (σ ↑ k)
--   -- ⦅_⦆ : κ ◆ k→SK k → (k ∷ κ) –→ κ
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
