module Examples.SystemF-Raw.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Examples.SystemF-Raw.Definitions
open Kit {{...}}

-- Soundness -------------------------------------------------------------------

postulate
  fun-ext : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) →
    f ≡ g

fun-ext₂ : ∀ {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

id↑≡id : ∀ {{K : Kit}} m µ →
  idₖ {µ = µ} {{K}} ↑ m ≡ idₖ {µ = m ∷ µ} {{K}}
id↑≡id m µ = fun-ext₂ λ where
  _ (here _)  → refl
  _ (there x) → wk-id/` m x

⋯-id : ∀ {{K : Kit}} (t : Term µ m) →
  t ⋯ idₖ {{K}} ≡ t
⋯-id               (` x)                             = id/`/id x
⋯-id {µ = µ} {{K}} (λx t)   rewrite id↑≡id {{K}} 𝕧 µ = cong λx_ (⋯-id t)
⋯-id {µ = µ} {{K}} (Λα t)   rewrite id↑≡id {{K}} 𝕥 µ = cong Λα_ (⋯-id t)
⋯-id {µ = µ} {{K}} (∀α t)   rewrite id↑≡id {{K}} 𝕥 µ = cong ∀α_ (⋯-id t)
⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

⋯ₜ-id : ∀ {{K : Kit}} (T : Type µ m) →
  T ⋯ₜ idₖ {{K}} ≡ T
⋯ₜ-id {m = 𝕧} T = ⋯-id T
⋯ₜ-id {m = 𝕥} T = refl

dist-lift-∘ᵣᵣ : ∀ m (ρ₁ : µ₁ →ᵣ µ₂) (ρ₂ : µ₂ →ᵣ µ₃) →
  (ρ₂ ∘ᵣ ρ₁) ↑ m ≡ (ρ₂ ↑ m) ∘ᵣ (ρ₁ ↑ m)
dist-lift-∘ᵣᵣ m ρ₁ ρ₂ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → refl

assoc-⋯ᵣ-⋯ᵣ : (v : Term µ₁ m) (ρ₁ : µ₁ →ᵣ µ₂) (ρ₂ : µ₂ →ᵣ µ₃) →
  v ⋯ (ρ₂ ∘ᵣ ρ₁) ≡ v ⋯ ρ₁ ⋯ ρ₂
assoc-⋯ᵣ-⋯ᵣ (` x)     ρ₁ ρ₂ = refl
assoc-⋯ᵣ-⋯ᵣ (λx v)    ρ₁ ρ₂ = cong λx_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (Λα v)    ρ₁ ρ₂ = cong Λα_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (∀α v)    ρ₁ ρ₂ = cong ∀α_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (v₁ · v₂) ρ₁ ρ₂ = cong₂ _·_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)
assoc-⋯ᵣ-⋯ᵣ (v₁ ∙ v₂) ρ₁ ρ₂ = cong₂ _∙_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)
assoc-⋯ᵣ-⋯ᵣ (v₁ ⇒ v₂) ρ₁ ρ₂ = cong₂ _⇒_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)

dist-lift-ren : ∀ (v : Term µ₁ m') (ρ : µ₁ →ᵣ µ₂) →
  v ⋯ wk ⋯ (ρ ↑ m) ≡ v ⋯ ρ ⋯ wk
dist-lift-ren {m = m} v ρ =
  v ⋯ wk ⋯ (ρ ↑ m)  ≡⟨ sym (assoc-⋯ᵣ-⋯ᵣ v wk (ρ ↑ m))  ⟩
  v ⋯ (ρ ↑ m) ∘ᵣ wk ≡⟨ refl ⟩
  v ⋯ wk ∘ᵣ ρ       ≡⟨ assoc-⋯ᵣ-⋯ᵣ v ρ wk ⟩
  v ⋯ ρ ⋯ wk        ∎

dist-lift-∘ₛᵣ : ∀ m (ρ : µ₁ →ᵣ µ₂) (σ : µ₂ →ₛ µ₃) →
  (σ ∘ₛ ρ) ↑ m ≡ (σ ↑ m) ∘ₛ (ρ ↑ m)
dist-lift-∘ₛᵣ m ρ σ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → refl

dist-lift-∘ᵣₛ : ∀ m (σ : µ₁ →ₛ µ₂) (ρ : µ₂ →ᵣ µ₃) →
  (ρ ∘ₛ σ) ↑ m ≡ (ρ ↑ m) ∘ₛ (σ ↑ m)
dist-lift-∘ᵣₛ m σ ρ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → sym (dist-lift-ren (σ _ x) ρ)

assoc-⋯ᵣ-⋯ₛ : (v : Term µ₁ m) (ρ : µ₁ →ᵣ µ₂) (σ : µ₂ →ₛ µ₃) →
  (v ⋯ ρ) ⋯ σ ≡ v ⋯ (σ ∘ₛ ρ)
assoc-⋯ᵣ-⋯ₛ (` x)     ρ σ = refl
assoc-⋯ᵣ-⋯ₛ (λx v)    ρ σ = cong λx_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (Λα v)    ρ σ = cong Λα_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (∀α v)    ρ σ = cong ∀α_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (v₁ · v₂) ρ σ = cong₂ _·_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)
assoc-⋯ᵣ-⋯ₛ (v₁ ∙ v₂) ρ σ = cong₂ _∙_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)
assoc-⋯ᵣ-⋯ₛ (v₁ ⇒ v₂) ρ σ = cong₂ _⇒_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)

assoc-⋯ₛ-⋯ᵣ : (v : Term µ₁ m) (σ : µ₁ →ₛ µ₂) (ρ : µ₂ →ᵣ µ₃) →
  (v ⋯ σ) ⋯ ρ ≡ v ⋯ (ρ ∘ₛ σ)
assoc-⋯ₛ-⋯ᵣ (` x)     σ ρ = refl
assoc-⋯ₛ-⋯ᵣ (λx v)    σ ρ = cong λx_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (Λα v)    σ ρ = cong Λα_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (∀α v)    σ ρ = cong ∀α_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (v₁ · v₂) σ ρ = cong₂ _·_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)
assoc-⋯ₛ-⋯ᵣ (v₁ ∙ v₂) σ ρ = cong₂ _∙_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)
assoc-⋯ₛ-⋯ᵣ (v₁ ⇒ v₂) σ ρ = cong₂ _⇒_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)

-- This lemma is the reason why we can't start with assoc-⋯ₛ-⋯ₛ and derive the rest.
-- It's only needed in the ₛₛ case but not in ᵣ-ₛ-combinations.
dist-lift-sub : ∀ (v : Term µ₁ m') (σ : µ₁ →ₛ µ₂) →
  v ⋯ wk ⋯ (σ ↑ m) ≡ v ⋯ σ ⋯ wk
dist-lift-sub {m = m} v σ =
  v ⋯ wk ⋯ (σ ↑ m)   ≡⟨ assoc-⋯ᵣ-⋯ₛ v wk (σ ↑ m) ⟩
  v ⋯ (σ ↑ m) ∘ₛ wk ≡⟨ refl ⟩
  v ⋯ wk ∘ₛ σ       ≡⟨ sym (assoc-⋯ₛ-⋯ᵣ v σ wk) ⟩
  v ⋯ σ ⋯ wk         ∎

dist-lift-∘ₛ : ∀ m (σ₁ : µ₁ →ₛ µ₂) (σ₂ : µ₂ →ₛ µ₃) →
  (σ₂ ∘ₛ σ₁) ↑ m ≡ (σ₂ ↑ m) ∘ₛ (σ₁ ↑ m)
dist-lift-∘ₛ m σ₁ σ₂ = fun-ext₂ λ where
  m' (here px) → refl
  m' (there x) →
    ((σ₂ ∘ₛ σ₁) ↑ m) m' (there x)       ≡⟨⟩
    (σ₂ ∘ₛ σ₁) m' x ⋯ wk                ≡⟨⟩
    σ₁ m' x ⋯ σ₂ ⋯ wk                   ≡⟨ sym (dist-lift-sub (σ₁ m' x) σ₂) ⟩
    σ₁ m' x ⋯ wk ⋯ (σ₂ ↑ m)             ≡⟨⟩
    (σ₁ ↑ m) m' (there x) ⋯ (σ₂ ↑ m)    ≡⟨⟩
    ((σ₂ ↑ m) ∘ₛ (σ₁ ↑ m)) m' (there x) ∎

assoc-⋯ₛ-⋯ₛ : (v : Term µ₁ m) (σ₁ : µ₁ →ₛ µ₂) (σ₂ : µ₂ →ₛ µ₃) →
  (v ⋯ σ₁) ⋯ σ₂ ≡ v ⋯ (σ₂ ∘ₛ σ₁)
assoc-⋯ₛ-⋯ₛ (` x)    σ₁ σ₂ = refl
assoc-⋯ₛ-⋯ₛ (λx v)   σ₁ σ₂ = cong λx_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (Λα v)   σ₁ σ₂ = cong Λα_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (∀α v)   σ₁ σ₂ = cong ∀α_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (v · v₁) σ₁ σ₂ = cong₂ _·_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)
assoc-⋯ₛ-⋯ₛ (v ∙ v₁) σ₁ σ₂ = cong₂ _∙_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)
assoc-⋯ₛ-⋯ₛ (v ⇒ v₁) σ₁ σ₂ = cong₂ _⇒_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)

sub-lift-id : (v : Term µ₁ m) (v' : Term µ₂ m') (σ : µ₁ →ₛ µ₂) →
  v ⋯ wk ⋯ (σ ,ₛ v') ≡ v ⋯ σ
sub-lift-id v v' σ = assoc-⋯ᵣ-⋯ₛ v wk (σ ,ₛ v')

tsub-lift-id : (v : Type µ₁ m) (v' : Term µ₂ m') (σ : µ₁ →ₛ µ₂) →
  wkt v ⋯ₜ (σ ,ₛ v') ≡ v ⋯ₜ σ
tsub-lift-id {m = 𝕧} v v' σ = sub-lift-id v v' σ
tsub-lift-id {m = 𝕥} v v' σ = refl

dist-lift-tsub : ∀ (v : Type µ₁ m') (σ : µ₁ →ₛ µ₂) →
  v ⋯ₜ wk ⋯ₜ (σ ↑ m) ≡ v ⋯ₜ σ ⋯ₜ wk
dist-lift-tsub {m' = 𝕧} v σ = dist-lift-sub v σ
dist-lift-tsub {m' = 𝕥} v σ = refl

dist-⋯-⋯' : ∀ (t : Term µ₁ 𝕥) (σ : µ₁ →ₛ µ₂) →
  σ ∘ₛ ⦅ t ⦆ ≡ ⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ 𝕥)
dist-⋯-⋯' t σ = fun-ext₂ λ where
  _ (here refl) → refl
  _ (there x) →
    σ _ x                  ≡⟨ sym (⋯-id (σ _ x)) ⟩
    σ _ x ⋯ idₖ            ≡⟨ sym (assoc-⋯ᵣ-⋯ₛ (σ _ x) wk (⦅ t ⋯ σ ⦆)) ⟩
    σ _ x ⋯ wk ⋯ ⦅ t ⋯ σ ⦆ ∎

dist-⋯-⋯ : ∀ (t₂ : Term (𝕥 ∷ µ₁) 𝕥) (t : Term µ₁ 𝕥) (σ : µ₁ →ₛ µ₂) →
  t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ 𝕥) ⋯ ⦅ t ⋯ σ ⦆
dist-⋯-⋯ t₂ t σ =
  t₂ ⋯ ⦅ t ⦆ ⋯ σ              ≡⟨ assoc-⋯ₛ-⋯ₛ t₂ ⦅ t ⦆ σ ⟩
  t₂ ⋯ σ ∘ₛ ⦅ t ⦆             ≡⟨ cong (t₂ ⋯_) (dist-⋯-⋯' t σ) ⟩
  t₂ ⋯ (⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ 𝕥)) ≡⟨ sym (assoc-⋯ₛ-⋯ₛ t₂ (σ ↑ 𝕥) (⦅ t ⋯ σ ⦆)) ⟩
  t₂ ⋯ σ ↑ 𝕥 ⋯ ⦅ t ⋯ σ ⦆      ∎

-- TODO: get rid of the next two lemmas
dist-⋯-⋯ᵣ' : ∀ (t : Term µ₁ 𝕥) (ρ : µ₁ →ᵣ µ₂) →
  ρ ∘ₛ ⦅ t ⦆ ≡ (⦅ t ⋯ ρ ⦆ ∘ₛ (ρ ↑ 𝕥))
dist-⋯-⋯ᵣ' t σ = fun-ext₂ λ where
  _ (here refl) → refl
  _ (there x) → refl

dist-⋯-⋯ᵣ : ∀ (t₂ : Term (𝕥 ∷ µ₁) 𝕥) (t : Term µ₁ 𝕥) (ρ : µ₁ →ᵣ µ₂) →
  t₂ ⋯ ⦅ t ⦆ ⋯ ρ ≡ t₂ ⋯ (ρ ↑ 𝕥) ⋯ ⦅ t ⋯ ρ ⦆
dist-⋯-⋯ᵣ t₂ t σ =
  t₂ ⋯ ⦅ t ⦆ ⋯ σ              ≡⟨ assoc-⋯ₛ-⋯ᵣ t₂ ⦅ t ⦆ σ ⟩
  t₂ ⋯ σ ∘ₛ ⦅ t ⦆             ≡⟨ cong (t₂ ⋯_) (dist-⋯-⋯ᵣ' t σ) ⟩
  t₂ ⋯ (⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ 𝕥)) ≡⟨ sym (assoc-⋯ᵣ-⋯ₛ t₂ (σ ↑ 𝕥) (⦅ t ⋯ σ ⦆)) ⟩
  t₂ ⋯ σ ↑ 𝕥 ⋯ ⦅ t ⋯ σ ⦆      ∎

-- Order Preserving Embeddings (required for "weakening preserves typing")
data OPE : µ₁ →ᵣ µ₂ → Ctx µ₁ → Ctx µ₂ → Set where
  ope-id : ∀ {Γ : Ctx µ} →
    OPE idₖ Γ Γ
  ope-keep  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : Type µ₁ m} →
    OPE  ρ       Γ₁        Γ₂ →
    OPE (ρ ↑ m) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ₜ ρ))
  ope-drop  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : Type µ₂ m} →
    OPE  ρ            Γ₁  Γ₂ →
    OPE (wk ∘ᵣ ρ) Γ₁ (Γ₂ ,, T)

-- TODO: works equally well with m instead of 𝕧, but requires even more ⋯ₜ versions of ⋯ lemmas...
ope-pres-telescope : ∀ {ρ : µ₁ →ᵣ µ₂} (x : µ₁ ∋ 𝕧) →
  OPE ρ Γ₁ Γ₂ →
  wk-drop-∈ (ρ 𝕧 x) (Γ₂ (ρ 𝕧 x)) ≡ wk-drop-∈ x (Γ₁ x) ⋯ ρ
ope-pres-telescope x           ope-id         = sym (⋯-id _)
ope-pres-telescope (here refl) (ope-keep {ρ = ρ} {T = T} ope) = sym (dist-lift-ren T ρ)
ope-pres-telescope (there x)   (ope-keep {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk ≡⟨ cong (_⋯ wk) (ope-pres-telescope x ope) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ ρ ⋯ wk         ≡⟨ sym (dist-lift-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ ρ ↑ _     ∎
ope-pres-telescope x           (ope-drop {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ₜ wk ≡⟨ cong (_⋯ₜ wk) (ope-pres-telescope x ope) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ ρ        ⋯ₜ wk ≡⟨ sym (assoc-⋯ᵣ-⋯ᵣ (wk-drop-∈ x (Γ₁ x)) ρ wk) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ wk ∘ᵣ ρ        ∎

ope-pres-⊢ : ∀ {v : Term µ₁ m} {t : Type µ₁ m} {ρ : µ₁ →ᵣ µ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ v     ∶ t →
  Γ₂ ⊢ v ⋯ ρ ∶ t ⋯ₜ ρ
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢v)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-lift-ren t₂ ρ) (ope-pres-⊢ (ope-keep ope) ⊢v))
ope-pres-⊢                       ope (τ-Λ ⊢v)                   = τ-Λ (ope-pres-⊢ (ope-keep ope) ⊢v)
ope-pres-⊢                       ope (τ-· ⊢v₁ ⊢v₂)              = τ-· (ope-pres-⊢ ope ⊢v₁) (ope-pres-⊢ ope ⊢v₂)
ope-pres-⊢               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢v) = subst (_ ⊢ _ ∶_) (sym (dist-⋯-⋯ᵣ t₂ t ρ)) (τ-∙ (ope-pres-⊢ ope ⊢v))
ope-pres-⊢                       ope τ-𝕥                        = τ-𝕥

wk-pres-⊢ : ∀ {m'} {v : Term µ m} {t : Type µ m} (T : Type µ m') →
  Γ₂        ⊢ v      ∶ t →
  (Γ₂ ,, T) ⊢ v ⋯ wk ∶ wkt t
wk-pres-⊢ T ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (T : Type µ₁ m) →
  Γ₂               ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ,, (T ⋯ₜ σ)) ⊢* (σ ↑ m) ∶ (Γ₁ ,, T)
lift-⊢* {m = 𝕧} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-lift-sub T σ))
lift-⊢* {m = 𝕥} {σ = σ} T ⊢σ (here refl) = τ-𝕥
lift-⊢* {m = m} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
  subst ((Γ₂ ,, (T ⋯ₜ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ₜ wk ⋯ₜ (σ ↑ m) ≡⟨ dist-lift-tsub _ σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ₜ σ ⋯ₜ wk       ∎))
        (wk-pres-⊢ (T ⋯ₜ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {v : Term µ₁ m} {t : Type µ₁ m} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ v ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ v ⋯ σ ∶ t ⋯ₜ σ
sub-pres-⊢ {m = 𝕥}         ⊢v                 ⊢σ = τ-𝕥
sub-pres-⊢ {m = 𝕧}         (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {m = 𝕧} {σ = σ} (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-lift-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
sub-pres-⊢ {m = 𝕧}         (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {m = 𝕧}         (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)
sub-pres-⊢ {m = 𝕧} {σ = σ} (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ              by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⋯-⋯ t₂ t σ)) (
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ 𝕥) ⋯ ⦅ t ⋯ σ ⦆    by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

_,*_ : ∀ {σ : µ₁ →ₛ µ₂} {T : Type µ₁ m₁} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  v ∶ T ⋯ₜ σ →
  Γ₂ ⊢* σ ,ₛ v ∶ Γ₁ ,, T
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (here refl) = subst (Γ₂ ⊢ v ∶_)     (sym (tsub-lift-id _ _ _)) ⊢v
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (there x)   = subst (Γ₂ ⊢ σ _ x ∶_) (sym (tsub-lift-id _ _ _)) (⊢σ x)

⊢*-id : ∀ {Γ : Ctx µ} →
  Γ ⊢* idₖ ∶ Γ
⊢*-id {µ = m ∷ µ} {Γ = Γ} {𝕥} x = τ-𝕥
⊢*-id {µ = m ∷ µ} {Γ = Γ} {𝕧} x rewrite ⋯-id {{K = kitₛ}} (wk-telescope Γ x) = τ-`  refl 

sub₁-pres-⊢ : ∀ {Γ : Ctx µ} {E₁ : Term (m₂ ∷ µ) m₁} {E₂ : µ ⊢ m₂} {T₂ : Type (m₂ ∷ µ) m₁} {T₁ : Type µ m₂} →
  Γ ,, T₁ ⊢ E₁ ∶ T₂ →
  Γ ⊢ E₂ ∶ T₁ →
  Γ ⊢ E₁ ⋯ ⦅ E₂ ⦆ ∶ T₂ ⋯ₜ ⦅ E₂ ⦆
sub₁-pres-⊢ {Γ = Γ} {E₂ = E₂} ⊢E₁ ⊢E₂ = sub-pres-⊢ ⊢E₁ (⊢*-id ,* subst (Γ ⊢ E₂ ∶_) (sym (⋯ₜ-id _)) ⊢E₂)

wk-cancels-⦅⦆ₛ : ∀ (e : µ ⊢ m) (e' : µ ⊢ m') →
  e ⋯ᵣ wk ⋯ₛ ⦅ e' ⦆ ≡ e
wk-cancels-⦅⦆ₛ e e' =
  e ⋯ᵣ wk ⋯ₛ ⦅ e' ⦆   ≡⟨ assoc-⋯ᵣ-⋯ₛ e wk ⦅ e' ⦆ ⟩
  e ⋯ₛ (⦅ e' ⦆ ∘ₛ wk) ≡⟨ refl ⟩
  e ⋯ₛ idₛ            ≡⟨ ⋯-id e ⟩
  e                   ∎

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢e₁) ⊢e₂)  β-λ        = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ₛ _ _) (sub₁-pres-⊢ ⊢e₁ ⊢e₂)
subject-reduction (τ-∙ (τ-Λ ⊢e))       β-Λ        = sub₁-pres-⊢ ⊢e τ-𝕥
subject-reduction (τ-λ ⊢e)            (ξ-λ  e↪e') = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-Λ ⊢e)            (ξ-Λ  e↪e') = τ-Λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)       (ξ-·₁ e↪e') = τ-· (subject-reduction ⊢e₁ e↪e') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)       (ξ-·₂ e↪e') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e↪e')
subject-reduction (τ-∙ ⊢e)            (ξ-∙  e↪e') = τ-∙ (subject-reduction ⊢e e↪e')
