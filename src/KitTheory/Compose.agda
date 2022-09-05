open import KitTheory.Modes
open import KitTheory.Kit using (KitTraversal)

module KitTheory.Compose {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) where

open import Data.List using (List; [])
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

    tm-⋯-∘ : (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
      tm _ (ϕ₁ _ x) ⋯ ϕ₂ ≡ tm _ ((ϕ₂ ∘ₖ ϕ₁) _ x)

    dist-↑-∘ : ∀ m (ϕ₁ : µ₂ –[ 𝕂₁ ]→ µ₃) (ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂) →
      (ϕ₁ ∘ₖ ϕ₂) ↑ m ≡ (ϕ₁ ↑ m) ∘ₖ (ϕ₂ ↑ m)

  dist-↑*-∘ : ∀ µ (ϕ₁ : µ₂ –[ 𝕂₁ ]→ µ₃) (ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    (ϕ₁ ∘ₖ ϕ₂) ↑* µ ≡ (ϕ₁ ↑* µ) ∘ₖ (ϕ₂ ↑* µ)
  dist-↑*-∘ []      ϕ₁ ϕ₂ = refl
  dist-↑*-∘ (µ ▷ m) ϕ₁ ϕ₂ =
    (ϕ₁ ∘ₖ ϕ₂) ↑* (µ ▷ m)                ≡⟨ refl ⟩
    ((ϕ₁ ∘ₖ ϕ₂) ↑* µ) ↑ m                ≡⟨ cong (_↑ m) (dist-↑*-∘ µ ϕ₁ ϕ₂) ⟩
    ((ϕ₁ ↑* µ) ∘ₖ (ϕ₂ ↑* µ)) ↑ m         ≡⟨ dist-↑-∘ m (ϕ₁ ↑* µ) (ϕ₂ ↑* µ) ⟩
    (((ϕ₁ ↑* µ) ↑ m) ∘ₖ ((ϕ₂ ↑* µ) ↑ m)) ≡⟨ refl ⟩
    ((ϕ₁ ↑* (µ ▷ m)) ∘ₖ (ϕ₂ ↑* (µ ▷ m))) ∎

record KitAssoc : Set₁ where
  open ComposeKit {{...}}

  field
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ ϕ₁ ⋯ ϕ₂ ≡ v ⋯ (ϕ₂ ∘ₖ ϕ₁)

  ∘≡∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit {{𝕂₂ }} {{𝕂₁ }} {{𝕂}} }}
              {{𝔸' : ComposeKit {{𝕂₂'}} {{𝕂₁'}} {{𝕂}} }}
              {ϕ₁  : µ₁ –[ 𝕂₁  ]→ µ₂ } {ϕ₂  : µ₂  –[ 𝕂₂  ]→ µ₃}
              {ϕ₁' : µ₁ –[ 𝕂₁' ]→ µ₂'} {ϕ₂' : µ₂' –[ 𝕂₂' ]→ µ₃} →
    ϕ₂ ∘ₖ ϕ₁ ≡ ϕ₂' ∘ₖ ϕ₁' →
    ∀ {M} (t : µ₁ ⊢ M) →
    t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
  ∘≡∘→⋯≡⋯ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
    t ⋯ ϕ₁ ⋯ ϕ₂    ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
    t ⋯ ϕ₂ ∘ₖ ϕ₁   ≡⟨ cong (t ⋯_) eq ⟩
    t ⋯ ϕ₂' ∘ₖ ϕ₁' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
    t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

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
  ComposeKit.dist-↑-∘ kitᵣᵣ = λ _ ρ₁ ρ₂ → fun-ext₂ λ where
                                                  _ (here px) → refl
                                                  _ (there x) → refl

  kitₛᵣ : ComposeKit {{kitₛ}} {{kitᵣ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitₛᵣ = _ₛ∘ᵣ_
  ComposeKit.tm-⋯-∘   kitₛᵣ = λ σ₁ ρ₂ x → ⋯-var (σ₁ _ x) ρ₂ where instance _ = kitₛ
  ComposeKit.dist-↑-∘ kitₛᵣ = λ _ σ₁ ρ₂ → fun-ext₂ λ where
                                                  _ (here px) → refl
                                                  _ (there x) → refl

  private instance _ = kitᵣᵣ
  private instance _ = kitₛᵣ

  kitᵣₛ : ComposeKit {{kitᵣ}} {{kitₛ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitᵣₛ = _ᵣ∘ₛ_
  ComposeKit.tm-⋯-∘   kitᵣₛ = λ ρ₁ σ₂ x → refl
  ComposeKit.dist-↑-∘ kitᵣₛ =
    λ m₁ ρ₁ σ₂ → fun-ext₂ λ where
        m (here refl) →
          ((ρ₁ ᵣ∘ₛ σ₂) ↑ m) m (here refl)       ≡⟨⟩
          (` here refl)                         ≡⟨⟩
          (` ((ρ₁ ↑ m₁) _ (here refl)))         ≡⟨ sym (⋯-var (here refl) (ρ₁ ↑ m₁)) ⟩
          ((` here refl) ⋯ (ρ₁ ↑ m₁))           ≡⟨⟩
          ((ρ₁ ↑ m) ᵣ∘ₛ (σ₂ ↑ m)) m (here refl) ∎
        m (there x)   →
          (σ₂ m x ⋯ ρ₁) ⋯ wk          ≡⟨ ⋯-assoc (σ₂ m x) ρ₁ wk ⟩
          σ₂ m x ⋯ (wk ᵣ∘ᵣ ρ₁)        ≡⟨⟩
          σ₂ m x ⋯ ((ρ₁ ↑ m₁) ᵣ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ₂ m x) wk (ρ₁ ↑ m₁)) ⟩
          (σ₂ m x ⋯ wk) ⋯ (ρ₁ ↑ m₁)   ∎

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

  record WkDistKit
      {{𝕂 : Kit}}
      {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
      {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
      : Set₁ where
    field
      comm-↑-wk : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
        (ϕ ↑ m) ∘ₖ wkᵣ ≡ wkᵣ ∘ₖ ϕ
      wk-cancels-,ₖ-∘ : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v : µ₂ ◆[ 𝕂 ] m→SM m) →
        (ϕ ,ₖ v) ∘ₖ wkᵣ ≡ ϕ

    -- TODO: generalize kitᵣ to arbitrary kits and include ⦅⦆ lemmas.

    -- This isn't limited to renamings i.e. wkᵣ ...
    dist-↑-f : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
      v ⋯ᵣ wkᵣ ⋯ (ϕ ↑ m) ≡ v ⋯ ϕ ⋯ᵣ wkᵣ
    dist-↑-f v ϕ =
      v ⋯ wkᵣ ⋯ (ϕ ↑ _)  ≡⟨ ⋯-assoc v wk (ϕ ↑ _)  ⟩
      v ⋯ (ϕ ↑ _) ∘ₖ wkᵣ ≡⟨ cong (v ⋯_) (comm-↑-wk ϕ) ⟩
      v ⋯ wkᵣ ∘ₖ ϕ       ≡⟨ sym (⋯-assoc v ϕ wk) ⟩
      v ⋯ ϕ ⋯ wkᵣ        ∎

    wk-cancels-,ₖ : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v' : µ₂ ◆[ 𝕂 ] m→SM m) →
      v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v') ≡ v ⋯ ϕ
    wk-cancels-,ₖ v ϕ v' =
      v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v')   ≡⟨ ⋯-assoc v wkᵣ (ϕ ,ₖ v') ⟩
      v ⋯ ((ϕ ,ₖ v') ∘ₖ wkᵣ) ≡⟨ cong (v ⋯_) (wk-cancels-,ₖ-∘ ϕ v') ⟩
      v ⋯ ϕ                  ∎

  wk-kitᵣ : WkDistKit {{kitᵣ}} {{kitᵣᵣ}} {{kitᵣᵣ}}
  wk-kitᵣ = record
    { comm-↑-wk = λ ϕ → refl
    ; wk-cancels-,ₖ-∘ = λ ϕ v → refl
    }

  wk-kitₛ : WkDistKit {{kitₛ}} {{kitₛᵣ}} {{kitᵣₛ}}
  wk-kitₛ = record
    { comm-↑-wk = λ ϕ → refl
    ; wk-cancels-,ₖ-∘ = λ ϕ v → refl
    }

  private instance _ = wk-kitᵣ
  private instance _ = wk-kitₛ

  open WkDistKit {{...}}

  open WkDistKit wk-kitᵣ public renaming (dist-↑-f to dist-↑-ren; wk-cancels-,ₖ to wk-cancels-,ᵣ) using ()
  open WkDistKit wk-kitₛ public renaming (dist-↑-f to dist-↑-sub; wk-cancels-,ₖ to wk-cancels-,ₛ) using ()

  record KitAssocLemmas : Set₁ where
    open ComposeKit {{...}}

    field
      ⋯-id : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

    ⋯-idₛ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitₛ}} ≡ v
    ⋯-idₛ = ⋯-id

    ⋯-idᵣ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitᵣ}} ≡ v
    ⋯-idᵣ = ⋯-id

    ren→sub : ∀ (e : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
              e ⋯ᵣ ρ ≡ e ⋯ₛ (idₛ ₛ∘ᵣ ρ)
    ren→sub e ρ =
      e ⋯ᵣ ρ           ≡⟨ sym (⋯-idₛ (e ⋯ᵣ ρ)) ⟩
      e ⋯ᵣ ρ ⋯ₛ idₛ    ≡⟨ ⋯-assoc e ρ vr ⟩
      e ⋯ₛ (idₛ ₛ∘ᵣ ρ) ∎

    wk-cancels-⦅⦆ :
      ∀ {{𝕂 : Kit}}
        {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
        {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
        {{_ : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}} }} {µ M m}
        (v : µ ⊢ M) (v' : µ ◆[ 𝕂 ] m→SM m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡ v
    wk-cancels-⦅⦆ v v' =
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡⟨ wk-cancels-,ₖ v idₖ v' ⟩
      v ⋯ idₖ          ≡⟨ ⋯-id v ⟩
      v                ∎

    wk-cancels-⦅⦆ᵣ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ∋ m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ᵣ ≡ v
    wk-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

    wk-cancels-⦅⦆ₛ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ⊢ m→M m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ₛ ≡ v
    wk-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

    -- TODO: prove for other combinations between ρ and σ.
    ↑∘⦅⦆-is-,ₛ : ∀ {µ₁ µ₂ m} (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      ⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m) ≡ σ ,ₛ t
    ↑∘⦅⦆-is-,ₛ t σ = fun-ext₂ λ where
      _ (here refl) → ⋯-var (here refl) ⦅ t ⦆
      _ (there x) → wk-cancels-⦅⦆ₛ (σ _ x) t

    -- TODO: prove for other combinations between ρ and σ.
    ⋯↑⋯⦅⦆-is-⋯,ₛ : ∀ {µ₁ µ₂ m} (t' : (µ₁ ▷ m) ⊢ M) (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      t' ⋯ (σ ↑ m) ⋯ ⦅ t ⦆ₛ ≡ t' ⋯ (σ ,ₛ t)
    ⋯↑⋯⦅⦆-is-⋯,ₛ {m = m} t' t σ =
      t' ⋯ₛ (σ ↑ m) ⋯ₛ ⦅ t ⦆ₛ    ≡⟨ ⋯-assoc t' (σ ↑ m) ⦅ t ⦆ₛ ⟩
      t' ⋯ₛ (⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m)) ≡⟨ cong (t' ⋯_) (↑∘⦅⦆-is-,ₛ t σ) ⟩
      t' ⋯ₛ (σ ,ₛ t)             ∎

    dist-ᵣ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
      ρ ᵣ∘ᵣ ⦅ x ⦆ ≡ ⦅ ρ _ x ⦆ ᵣ∘ᵣ (ρ ↑ m)
    dist-ᵣ∘ᵣ-⦅⦆ x σ = fun-ext₂ λ where
      _ (here refl) → refl
      _ (there y) → refl

    dist-ᵣ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
      ρ ᵣ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ ρ ⦆ ₛ∘ᵣ (ρ ↑ m)
    dist-ᵣ∘ₛ-⦅⦆ t σ = fun-ext₂ λ where
      _ (here refl) → refl
      _ (there x) → ⋯-var x σ

    dist-ₛ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      σ ₛ∘ᵣ ⦅ x ⦆ ≡ ⦅ σ _ x ⦆ ₛ∘ₛ (σ ↑ m)
    dist-ₛ∘ᵣ-⦅⦆ x σ = fun-ext₂ λ where
      _ (here refl) → sym (⋯-var (here refl) ⦅ σ _ x ⦆)
      _ (there y) →
        σ _ y                             ≡⟨ sym (⋯-id (σ _ y)) ⟩
        σ _ y ⋯ ((idₖ ,ₖ (σ _ x)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ y) wk ⦅ σ _ x ⦆) ⟩
        (σ _ y ⋯ wk) ⋯ (idₖ ,ₖ (σ _ x))   ∎

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

    dist-⦅⦆ᵣ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
      t ⋯ ⦅ x ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ ρ _ x ⦆
    dist-⦅⦆ᵣ-⋯ᵣ t x ρ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ x ρ) t

    dist-⦅⦆ₛ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
      t ⋯ ⦅ t' ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ t' ⋯ ρ ⦆
    dist-⦅⦆ₛ-⋯ᵣ t t' ρ = ∘≡∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t' ρ) t

    dist-⦅⦆ᵣ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      t ⋯ ⦅ x ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ σ _ x ⦆
    dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘≡∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

    dist-⦅⦆ₛ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      t ⋯ ⦅ t' ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ t' ⋯ σ ⦆
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
