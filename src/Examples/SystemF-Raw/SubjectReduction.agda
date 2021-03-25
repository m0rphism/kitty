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

id↑≡id : ∀ {{K : Kit}} k κ →
  K-id {κ = κ} K ↑ k ≡ K-id {κ = k ∷ κ} K
id↑≡id k κ = fun-ext₂ λ where
  _ (here _)  → refl
  _ (there x) → wk-vr k x

⋯-id : ∀ {{K : Kit}} (v : Term κ k) →
  v ⋯ K-id K ≡ v
⋯-id               (` x)                             = tm-vr x
⋯-id {κ = κ} {{K}} (λ→ t)   rewrite id↑≡id {{K}} ★ κ = cong λ→_ (⋯-id t)
⋯-id {κ = κ} {{K}} (Λ→ t)   rewrite id↑≡id {{K}} ■ κ = cong Λ→_ (⋯-id t)
⋯-id {κ = κ} {{K}} (∀→ t)   rewrite id↑≡id {{K}} ■ κ = cong ∀→_ (⋯-id t)
⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

⋯ₜ-id : ∀ {{K : Kit}} (v : Type κ k) →
  v ⋯ₜ K-id K ≡ v
⋯ₜ-id {k = ★} v = ⋯-id v
⋯ₜ-id {k = ■} v = refl

dist-lift-∘ᵣᵣ : ∀ k (ρ₁ : κ₁ →ᵣ κ₂) (ρ₂ : κ₂ →ᵣ κ₃) →
  (ρ₂ ∘ᵣ ρ₁) ↑ k ≡ (ρ₂ ↑ k) ∘ᵣ (ρ₁ ↑ k)
dist-lift-∘ᵣᵣ k ρ₁ ρ₂ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → refl

assoc-⋯ᵣ-⋯ᵣ : (v : Term κ₁ k) (ρ₁ : κ₁ →ᵣ κ₂) (ρ₂ : κ₂ →ᵣ κ₃) →
  v ⋯ (ρ₂ ∘ᵣ ρ₁) ≡ v ⋯ ρ₁ ⋯ ρ₂
assoc-⋯ᵣ-⋯ᵣ (` x)     ρ₁ ρ₂ = refl
assoc-⋯ᵣ-⋯ᵣ (λ→ v)    ρ₁ ρ₂ = cong λ→_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (Λ→ v)    ρ₁ ρ₂ = cong Λ→_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (∀→ v)    ρ₁ ρ₂ = cong ∀→_
  (v ⋯ (ρ₂ ∘ᵣ ρ₁) ↑ _         ≡⟨ cong (v ⋯_) (dist-lift-∘ᵣᵣ _ ρ₁ ρ₂) ⟩
   v ⋯ ((ρ₂ ↑ _) ∘ᵣ (ρ₁ ↑ _)) ≡⟨ assoc-⋯ᵣ-⋯ᵣ v (ρ₁ ↑ _) (ρ₂ ↑ _) ⟩
   v ⋯ ρ₁ ↑ _ ⋯ ρ₂ ↑ _        ∎)
assoc-⋯ᵣ-⋯ᵣ (v₁ · v₂) ρ₁ ρ₂ = cong₂ _·_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)
assoc-⋯ᵣ-⋯ᵣ (v₁ ∙ v₂) ρ₁ ρ₂ = cong₂ _∙_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)
assoc-⋯ᵣ-⋯ᵣ (v₁ ⇒ v₂) ρ₁ ρ₂ = cong₂ _⇒_ (assoc-⋯ᵣ-⋯ᵣ v₁ ρ₁ ρ₂) (assoc-⋯ᵣ-⋯ᵣ v₂ ρ₁ ρ₂)

dist-lift-ren : ∀ (v : Term κ₁ k') (ρ : κ₁ →ᵣ κ₂) →
  v ⋯ there' ⋯ (ρ ↑ k) ≡ v ⋯ ρ ⋯ there'
dist-lift-ren {k = k} v ρ =
  v ⋯ there' ⋯ (ρ ↑ k)  ≡⟨ sym (assoc-⋯ᵣ-⋯ᵣ v there' (ρ ↑ k))  ⟩
  v ⋯ (ρ ↑ k) ∘ᵣ there' ≡⟨ refl ⟩
  v ⋯ there' ∘ᵣ ρ       ≡⟨ assoc-⋯ᵣ-⋯ᵣ v ρ there' ⟩
  v ⋯ ρ ⋯ there'        ∎

dist-lift-∘ₛᵣ : ∀ k (ρ : κ₁ →ᵣ κ₂) (σ : κ₂ →ₛ κ₃) →
  (σ ∘ₛ ρ) ↑ k ≡ (σ ↑ k) ∘ₛ (ρ ↑ k)
dist-lift-∘ₛᵣ k ρ σ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → refl

dist-lift-∘ᵣₛ : ∀ k (σ : κ₁ →ₛ κ₂) (ρ : κ₂ →ᵣ κ₃) →
  (ρ ∘ₛ σ) ↑ k ≡ (ρ ↑ k) ∘ₛ (σ ↑ k)
dist-lift-∘ᵣₛ k σ ρ = fun-ext₂ λ where
  _ (here px) → refl
  _ (there x) → sym (dist-lift-ren (σ _ x) ρ)

assoc-⋯ᵣ-⋯ₛ : (v : Term κ₁ k) (ρ : κ₁ →ᵣ κ₂) (σ : κ₂ →ₛ κ₃) →
  (v ⋯ ρ) ⋯ σ ≡ v ⋯ (σ ∘ₛ ρ)
assoc-⋯ᵣ-⋯ₛ (` x)     ρ σ = refl
assoc-⋯ᵣ-⋯ₛ (λ→ v)    ρ σ = cong λ→_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (Λ→ v)    ρ σ = cong Λ→_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (∀→ v)    ρ σ = cong ∀→_
  (v ⋯ (ρ ↑ _) ⋯ (σ ↑ _)    ≡⟨ assoc-⋯ᵣ-⋯ₛ v (ρ ↑ _) (σ ↑ _) ⟩
   v ⋯ ((σ ↑ _) ∘ₛ (ρ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛᵣ _ ρ σ)) ⟩
   v ⋯ ((σ ∘ₛ ρ) ↑ _)       ∎)
assoc-⋯ᵣ-⋯ₛ (v₁ · v₂) ρ σ = cong₂ _·_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)
assoc-⋯ᵣ-⋯ₛ (v₁ ∙ v₂) ρ σ = cong₂ _∙_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)
assoc-⋯ᵣ-⋯ₛ (v₁ ⇒ v₂) ρ σ = cong₂ _⇒_ (assoc-⋯ᵣ-⋯ₛ v₁ ρ σ) (assoc-⋯ᵣ-⋯ₛ v₂ ρ σ)

assoc-⋯ₛ-⋯ᵣ : (v : Term κ₁ k) (σ : κ₁ →ₛ κ₂) (ρ : κ₂ →ᵣ κ₃) →
  (v ⋯ σ) ⋯ ρ ≡ v ⋯ (ρ ∘ₛ σ)
assoc-⋯ₛ-⋯ᵣ (` x)     σ ρ = refl
assoc-⋯ₛ-⋯ᵣ (λ→ v)    σ ρ = cong λ→_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (Λ→ v)    σ ρ = cong Λ→_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (∀→ v)    σ ρ = cong ∀→_
  (v ⋯ (σ ↑ _) ⋯ (ρ ↑ _)     ≡⟨ assoc-⋯ₛ-⋯ᵣ v (σ ↑ _) (ρ ↑ _) ⟩
   v ⋯ ((ρ ↑ _) ∘ᵣₛ (σ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ᵣₛ _ σ ρ)) ⟩
   v ⋯ (ρ ∘ₛ σ) ↑ _          ∎)
assoc-⋯ₛ-⋯ᵣ (v₁ · v₂) σ ρ = cong₂ _·_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)
assoc-⋯ₛ-⋯ᵣ (v₁ ∙ v₂) σ ρ = cong₂ _∙_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)
assoc-⋯ₛ-⋯ᵣ (v₁ ⇒ v₂) σ ρ = cong₂ _⇒_ (assoc-⋯ₛ-⋯ᵣ v₁ σ ρ) (assoc-⋯ₛ-⋯ᵣ v₂ σ ρ)

-- This lemma is the reason why we can't start with assoc-⋯ₛ-⋯ₛ and derive the rest.
-- It's only needed in the ₛₛ case but not in ᵣ-ₛ-combinations.
dist-lift-sub : ∀ (v : Term κ₁ k') (σ : κ₁ →ₛ κ₂) →
  v ⋯ there' ⋯ (σ ↑ k) ≡ v ⋯ σ ⋯ there'
dist-lift-sub {k = k} v σ =
  v ⋯ there' ⋯ (σ ↑ k)   ≡⟨ assoc-⋯ᵣ-⋯ₛ v there' (σ ↑ k) ⟩
  v ⋯ (σ ↑ k) ∘ₛ there' ≡⟨ refl ⟩
  v ⋯ there' ∘ₛ σ       ≡⟨ sym (assoc-⋯ₛ-⋯ᵣ v σ there') ⟩
  v ⋯ σ ⋯ there'         ∎

dist-lift-∘ₛ : ∀ k (σ₁ : κ₁ →ₛ κ₂) (σ₂ : κ₂ →ₛ κ₃) →
  (σ₂ ∘ₛ σ₁) ↑ k ≡ (σ₂ ↑ k) ∘ₛ (σ₁ ↑ k)
dist-lift-∘ₛ k σ₁ σ₂ = fun-ext₂ λ where
  k' (here px) → refl
  k' (there x) →
    ((σ₂ ∘ₛ σ₁) ↑ k) k' (there x)       ≡⟨⟩
    (σ₂ ∘ₛ σ₁) k' x ⋯ there'            ≡⟨⟩
    σ₁ k' x ⋯ σ₂ ⋯ there'               ≡⟨ sym (dist-lift-sub (σ₁ k' x) σ₂) ⟩
    σ₁ k' x ⋯ there' ⋯ (σ₂ ↑ k)         ≡⟨⟩
    (σ₁ ↑ k) k' (there x) ⋯ (σ₂ ↑ k)    ≡⟨⟩
    ((σ₂ ↑ k) ∘ₛ (σ₁ ↑ k)) k' (there x) ∎

-- This is only true because of parallel substitution. Otherwise
-- σ₂ might replace variables which σ₁ did not affect.
assoc-⋯ₛ-⋯ₛ : (v : Term κ₁ k) (σ₁ : κ₁ →ₛ κ₂) (σ₂ : κ₂ →ₛ κ₃) →
  (v ⋯ σ₁) ⋯ σ₂ ≡ v ⋯ (σ₂ ∘ₛ σ₁)
assoc-⋯ₛ-⋯ₛ (` x)    σ₁ σ₂ = refl
assoc-⋯ₛ-⋯ₛ (λ→ v)   σ₁ σ₂ = cong λ→_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (Λ→ v)   σ₁ σ₂ = cong Λ→_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (∀→ v)   σ₁ σ₂ = cong ∀→_
  (v ⋯ (σ₁ ↑ _) ⋯ (σ₂ ↑ _)    ≡⟨ assoc-⋯ₛ-⋯ₛ v (σ₁ ↑ _) (σ₂ ↑ _) ⟩
   v ⋯ ((σ₂ ↑ _) ∘ₛ (σ₁ ↑ _)) ≡⟨ cong (v ⋯_) (sym (dist-lift-∘ₛ _ σ₁ σ₂)) ⟩
   v ⋯ ((σ₂ ∘ₛ σ₁) ↑ _)       ∎)
assoc-⋯ₛ-⋯ₛ (v · v₁) σ₁ σ₂ = cong₂ _·_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)
assoc-⋯ₛ-⋯ₛ (v ∙ v₁) σ₁ σ₂ = cong₂ _∙_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)
assoc-⋯ₛ-⋯ₛ (v ⇒ v₁) σ₁ σ₂ = cong₂ _⇒_ (assoc-⋯ₛ-⋯ₛ v σ₁ σ₂) (assoc-⋯ₛ-⋯ₛ v₁ σ₁ σ₂)

-- sub-lift-id : {{K : Kit}} → {v : Term κ₁ k} {v' : Kit._◆_ K κ₂ k'} {σ : κ₁ –[ K ]→ κ₂} →
--   wk v ⋯ (σ ,ₖ v') ≡ v ⋯ σ
-- sub-lift-id {v = v} {v' = v'} {σ = σ} = {! assoc-⋯ᵣ-⋯ₛ v there' (σ ,ₖ v') !}

sub-lift-id : (v : Term κ₁ k) (v' : Term κ₂ k') (σ : κ₁ →ₛ κ₂) →
  wk v ⋯ (σ ,ₛ v') ≡ v ⋯ σ
sub-lift-id v v' σ = assoc-⋯ᵣ-⋯ₛ v there' (σ ,ₛ v')

tsub-lift-id : (v : Type κ₁ k) (v' : Term κ₂ k') (σ : κ₁ →ₛ κ₂) →
  wkt v ⋯ₜ (σ ,ₛ v') ≡ v ⋯ₜ σ
tsub-lift-id {k = ★} v v' σ = sub-lift-id v v' σ
tsub-lift-id {k = ■} v v' σ = refl

dist-lift-tsub : ∀ (v : Type κ₁ k') (σ : κ₁ →ₛ κ₂) →
  v ⋯ₜ there' ⋯ₜ (σ ↑ k) ≡ v ⋯ₜ σ ⋯ₜ there'
dist-lift-tsub {k' = ★} v σ = dist-lift-sub v σ
dist-lift-tsub {k' = ■} v σ = refl

-- We only need this for types, i.e. where k = k' = ■.
-- dist-⋯-⋯ : ∀ (t₂ : Term (k' ∷ κ₁) k) (t : Term κ₁ k') (σ : κ₁ →ₛ κ₂) →
--   t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ liftₛ k' σ ⋯ ⦅ t ⋯ σ ⦆
-- dist-⋯-⋯ = {!!}

dist-⋯-⋯' : ∀ (t : Term κ₁ ■) (σ : κ₁ →ₛ κ₂) →
  σ ∘ₛ ⦅ t ⦆ ≡ (⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ ■))
dist-⋯-⋯' t σ = fun-ext₂ λ where
  _ (here refl) → refl
  _ (there x) →
    σ _ x                      ≡⟨ sym (⋯-id (σ _ x)) ⟩
    σ _ x ⋯ σ-id               ≡⟨ sym (assoc-⋯ᵣ-⋯ₛ (σ _ x) there' (⦅ t ⋯ σ ⦆)) ⟩
    σ _ x ⋯ there' ⋯ ⦅ t ⋯ σ ⦆ ∎

dist-⋯-⋯ : ∀ (t₂ : Term (■ ∷ κ₁) ■) (t : Term κ₁ ■) (σ : κ₁ →ₛ κ₂) →
  t₂ ⋯ ⦅ t ⦆ ⋯ σ ≡ t₂ ⋯ (σ ↑ ■) ⋯ ⦅ t ⋯ σ ⦆
dist-⋯-⋯ t₂ t σ =
  t₂ ⋯ ⦅ t ⦆ ⋯ σ              ≡⟨ assoc-⋯ₛ-⋯ₛ t₂ ⦅ t ⦆ σ ⟩
  t₂ ⋯ σ ∘ₛ ⦅ t ⦆             ≡⟨ cong (t₂ ⋯_) (dist-⋯-⋯' t σ) ⟩
  t₂ ⋯ (⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ ■)) ≡⟨ sym (assoc-⋯ₛ-⋯ₛ t₂ (σ ↑ ■) (⦅ t ⋯ σ ⦆)) ⟩
  t₂ ⋯ σ ↑ ■ ⋯ ⦅ t ⋯ σ ⦆      ∎

-- TODO: get rid of the next too lemmas
dist-⋯-⋯ᵣ' : ∀ (t : Term κ₁ ■) (ρ : κ₁ →ᵣ κ₂) →
  ρ ∘ₛ ⦅ t ⦆ ≡ (⦅ t ⋯ ρ ⦆ ∘ₛ (ρ ↑ ■))
dist-⋯-⋯ᵣ' t σ = fun-ext₂ λ where
  _ (here refl) → refl
  _ (there x) → refl

dist-⋯-⋯ᵣ : ∀ (t₂ : Term (■ ∷ κ₁) ■) (t : Term κ₁ ■) (ρ : κ₁ →ᵣ κ₂) →
  t₂ ⋯ ⦅ t ⦆ ⋯ ρ ≡ t₂ ⋯ (ρ ↑ ■) ⋯ ⦅ t ⋯ ρ ⦆
dist-⋯-⋯ᵣ t₂ t σ =
  t₂ ⋯ ⦅ t ⦆ ⋯ σ              ≡⟨ assoc-⋯ₛ-⋯ᵣ t₂ ⦅ t ⦆ σ ⟩
  t₂ ⋯ σ ∘ₛ ⦅ t ⦆             ≡⟨ cong (t₂ ⋯_) (dist-⋯-⋯ᵣ' t σ) ⟩
  t₂ ⋯ (⦅ t ⋯ σ ⦆ ∘ₛ (σ ↑ ■)) ≡⟨ sym (assoc-⋯ᵣ-⋯ₛ t₂ (σ ↑ ■) (⦅ t ⋯ σ ⦆)) ⟩
  t₂ ⋯ σ ↑ ■ ⋯ ⦅ t ⋯ σ ⦆      ∎

-- Order Preserving Embeddings for Contexts. Required by ope-pres-⊢, where we can't
-- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
-- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
-- constructor).
-- Also arbitrary renamings would allow swapping types in the context which
-- could violate the telescoping (I think).
data OPE : κ₁ →ᵣ κ₂ → Ctx κ₁ → Ctx κ₂ → Set where
  ope-id : ∀ {Γ : Ctx κ} →
    OPE ρ-id Γ Γ
  ope-keep  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₁ k} →
    OPE  ρ       Γ₁        Γ₂ →
    OPE (ρ ↑ k) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ₜ ρ))
  ope-drop  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₂ k} →
    OPE  ρ            Γ₁  Γ₂ →
    OPE (there' ∘ᵣ ρ) Γ₁ (Γ₂ ,, T)

-- TODO: works equally well with k instead of ★, but requires even more ⋯ₜ versions of ⋯ lemmas...
ope-pres-telescope : ∀ {ρ : κ₁ →ᵣ κ₂} (x : κ₁ ∋ ★) →
  OPE ρ Γ₁ Γ₂ →
  wk-drop-∈ (ρ ★ x) (Γ₂ (ρ ★ x)) ≡ wk-drop-∈ x (Γ₁ x) ⋯ ρ
ope-pres-telescope x           ope-id         = sym (⋯-id _)
ope-pres-telescope (here refl) (ope-keep {ρ = ρ} {T = T} ope) = sym (dist-lift-ren T ρ)
ope-pres-telescope (there x)   (ope-keep {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk (wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x))) ≡⟨ cong wk (ope-pres-telescope x ope) ⟩
  wk (wk-drop-∈ x (Γ₁ x) ⋯ ρ)         ≡⟨ sym (dist-lift-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
  wk (wk-drop-∈ x (Γ₁ x)) ⋯ ρ ↑ _     ∎
ope-pres-telescope x           (ope-drop {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ₜ there' ≡⟨ cong (_⋯ₜ there') (ope-pres-telescope x ope) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ ρ        ⋯ₜ there' ≡⟨ sym (assoc-⋯ᵣ-⋯ᵣ (wk-drop-∈ x (Γ₁ x)) ρ there') ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ there' ∘ᵣ ρ        ∎

ope-pres-⊢ : ∀ {v : Term κ₁ k} {t : Type κ₁ k} {ρ : κ₁ →ᵣ κ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ v     ∶ t →
  Γ₂ ⊢ v ⋯ ρ ∶ t ⋯ₜ ρ
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
ope-pres-⊢ {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢v)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-lift-ren t₂ ρ) (ope-pres-⊢ (ope-keep ope) ⊢v))
ope-pres-⊢                       ope (τ-Λ ⊢v)                   = τ-Λ (ope-pres-⊢ (ope-keep ope) ⊢v)
ope-pres-⊢                       ope (τ-· ⊢v₁ ⊢v₂)              = τ-· (ope-pres-⊢ ope ⊢v₁) (ope-pres-⊢ ope ⊢v₂)
ope-pres-⊢               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢v) = subst (_ ⊢ _ ∶_) (sym (dist-⋯-⋯ᵣ t₂ t ρ)) (τ-∙ (ope-pres-⊢ ope ⊢v))
ope-pres-⊢                       ope τ-★                        = τ-★

wk-pres-⊢ : ∀ {k'} {v : Term κ k} {t : Type κ k} (T : Type κ k') →
  Γ₂        ⊢ v    ∶ t →
  (Γ₂ ,, T) ⊢ wk v ∶ wkt t
wk-pres-⊢ T ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : κ₁ →ₛ κ₂} (T : Type κ₁ k) →
  Γ₂               ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ,, (T ⋯ₜ σ)) ⊢* (σ ↑ k) ∶ (Γ₁ ,, T)
lift-⊢* {k = ★} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-lift-sub T σ))
lift-⊢* {k = ■} {σ = σ} T ⊢σ (here refl) = τ-★
lift-⊢* {k = k} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
  subst ((Γ₂ ,, (T ⋯ₜ σ)) ⊢ (σ _ x ⋯ there') ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ₜ there' ⋯ₜ (σ ↑ k) ≡⟨ dist-lift-tsub _ σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ₜ σ ⋯ₜ there'       ∎))
        (wk-pres-⊢ (T ⋯ₜ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {v : Term κ₁ k} {t : Type κ₁ k} {σ : κ₁ →ₛ κ₂} →
  Γ₁ ⊢ v ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ v ⋯ σ ∶ t ⋯ₜ σ
sub-pres-⊢ {k = ■}         ⊢v                 ⊢σ = τ-★
sub-pres-⊢ {k = ★}         (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {k = ★} {σ = σ} (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-lift-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
sub-pres-⊢ {k = ★}         (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {k = ★}         (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)
sub-pres-⊢ {k = ★} {σ = σ} (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ            by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⋯-⋯ t₂ t σ)) (
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ ■) ⋯ ⦅ t ⋯ σ ⦆    by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

_,*_ : ∀ {σ : κ₁ →ₛ κ₂} {T : Type κ₁ k₁} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  v ∶ T ⋯ₜ σ →
  Γ₂ ⊢* σ ,ₛ v ∶ Γ₁ ,, T
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (here refl) = subst (Γ₂ ⊢ v ∶_)     (sym (tsub-lift-id _ _ _)) ⊢v
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (there x)   = subst (Γ₂ ⊢ σ _ x ∶_) (sym (tsub-lift-id _ _ _)) (⊢σ x)

⊢*-σ-id : ∀ {Γ : Ctx κ} →
  Γ ⊢* σ-id ∶ Γ
⊢*-σ-id {κ = k ∷ κ} {Γ = Γ} {■} x = τ-★
⊢*-σ-id {κ = k ∷ κ} {Γ = Γ} {★} x rewrite ⋯-id {{K = kitₛ}} (wk-telescope Γ x) = τ-` refl

vsub-pres-⊢ : ∀ {Γ : Ctx κ} {e₁ : Term (★ ∷ κ) ★} {e₂ : Term κ ★} {t₁ t₂ : Type κ ★} →
  Γ ,, t₁ ⊢ e₁ ∶ wk t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂
vsub-pres-⊢ {e₁ = e₁} {e₂ = e₂} {t₂ = t₂} ⊢e₁ ⊢e₂ =
  subst (_ ⊢ _ ∶_)
        (wk t₂ ⋯ ⦅ e₂ ⦆ ≡⟨ sub-lift-id t₂ _ _ ⟩
         t₂ ⋯ σ-id      ≡⟨ ⋯-id t₂ ⟩
         t₂             ∎)
        (_ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ wk t₂ ⋯ₜ ⦅ e₂ ⦆ by
         sub-pres-⊢ {σ = ⦅ e₂ ⦆}
           ⊢e₁
           (⊢*-σ-id ,* (subst (_ ⊢ _ ∶_) (sym (⋯-id _)) ⊢e₂)))

tsub-pres-⊢ : ∀ {Γ : Ctx κ} {e : Term (■ ∷ κ) ★} {t₂ : Term (■ ∷ κ) ■} {t : Type κ ★} →
  Γ ,, tt ⊢ e ∶ t₂ →
  Γ ⊢ t ∶ tt →
  Γ ⊢ e ⋯ ⦅ t ⦆ ∶ t₂ ⋯ ⦅ t ⦆
tsub-pres-⊢ ⊢e ⊢t = sub-pres-⊢ ⊢e (⊢*-σ-id ,* ⊢t)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢e₁) ⊢e₂)  β-λ        = vsub-pres-⊢ ⊢e₁ ⊢e₂
subject-reduction (τ-∙ (τ-Λ ⊢e))       β-Λ        = tsub-pres-⊢ ⊢e τ-★
subject-reduction (τ-λ ⊢e)            (ξ-λ  e↪e') = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-Λ ⊢e)            (ξ-Λ  e↪e') = τ-Λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)       (ξ-·₁ e↪e') = τ-· (subject-reduction ⊢e₁ e↪e') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)       (ξ-·₂ e↪e') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e↪e')
subject-reduction (τ-∙ ⊢e)            (ξ-∙  e↪e') = τ-∙ (subject-reduction ⊢e e↪e')
