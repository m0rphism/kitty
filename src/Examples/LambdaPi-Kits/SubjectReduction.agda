module Examples.LambdaPi-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Examples.LambdaPi-Kits.Definitions
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (_++_; [])
open import Data.Product renaming (_,_ to _,×_)

mutual
  ⇓-refl-neutral : (n : Value µ 𝕟) →
    ⟦ n ⟧ ⇓ neutral n
  ⇓-refl-neutral (` x) = ⇓-`
  ⇓-refl-neutral (n · v) = ⇓-·ₙ (⇓-refl-neutral n) (⇓-refl-val v)

  ⇓-refl-val : (τ : Value µ 𝕧) →
    ⟦ τ ⟧ ⇓ τ
  ⇓-refl-val (λ→ τ)      = ⇓-λ (⇓-refl-val τ)
  ⇓-refl-val (Π τ₁ τ₂)   = ⇓-Π (⇓-refl-val τ₁) (⇓-refl-val τ₂)
  ⇓-refl-val ★           = ⇓-★
  ⇓-refl-val (neutral τ) = ⇓-refl-neutral τ

⇓-deterministic :
  t ⇓ v₁ →
  t ⇓ v₂ →
  v₁ ≡ v₂
⇓-deterministic (⇓-λ t⇓v₁) (⇓-λ t⇓v₂) =
  cong λ→_ (⇓-deterministic t⇓v₁ t⇓v₂)
⇓-deterministic (⇓-Π t⇓v₁₁ t⇓v₁₂) (⇓-Π t⇓v₂₁ t⇓v₂₂) =
  cong₂ Π (⇓-deterministic t⇓v₁₁ t⇓v₂₁) (⇓-deterministic t⇓v₁₂ t⇓v₂₂)
⇓-deterministic ⇓-` ⇓-` = refl
⇓-deterministic (⇓-·ᵥ t⇓v₁₁ t⇓v₁₂ t⇓v₁) (⇓-·ᵥ t⇓v₂₁ t⇓v₂₂ t⇓v₂)
    with ⇓-deterministic t⇓v₁₁ t⇓v₂₁ |  ⇓-deterministic t⇓v₁₂ t⇓v₂₂
... | refl | refl = ⇓-deterministic t⇓v₁ t⇓v₂
⇓-deterministic (⇓-·ᵥ t⇓v₁₁ t⇓v₁₂ t⇓v₁) (⇓-·ₙ t⇓v₂₁ t⇓v₂₂)
    with ⇓-deterministic t⇓v₁₁ t⇓v₂₁
... | ()
⇓-deterministic (⇓-·ₙ t⇓v₁₁ t⇓v₁₂) (⇓-·ᵥ t⇓v₂₁ t⇓v₂₂ t⇓v₂)
    with ⇓-deterministic t⇓v₁₁ t⇓v₂₁
... | ()
⇓-deterministic (⇓-·ₙ t⇓v₁₁ t⇓v₁₂) (⇓-·ₙ t⇓v₂₁ t⇓v₂₂)
    with ⇓-deterministic t⇓v₁₁ t⇓v₂₁ |  ⇓-deterministic t⇓v₁₂ t⇓v₂₂
... | refl | refl = refl
⇓-deterministic ⇓-★ ⇓-★ = refl

subst-pres-ty₁ : {Γ : Ctx µ} →
  Γ ,, τ₂ ⊢ e₁ ∶ τ₁ →
  Γ ⊢ e₂ ∶ τ₂ →
  ⟦ τ₁ ⟧ ⋯ ⦅ e₂ ⦆ ⇓ τ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ τ
subst-pres-ty₁ = {!!}

_⇓ₛ_ : (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ⇓ₛ σ₂ = ∀ m x → ∃[ v ] (σ₁ m x ⇓' v × σ₂ m x ≡ ⟦ v ⟧')

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
postulate
  fun-ext-i : ∀ {ℓ₁ ℓ₂} →
    {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : {x : A} → B x} →
    (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

↑≡' : ∀ (ρ : µ₁ →ᵣ µ₂) m m' x → (ρ ↑ᵣ m) m' x ≡ (ρ ValueSubst.↑ᵣ m) m' x
↑≡' ρ m m' (here px) = refl
↑≡' ρ m m' (there x) = refl

↑≡ : (λ {µ₁} {µ₂} → _↑ᵣ_ {µ₁ = µ₁} {µ₂ = µ₂}) ≡ (λ {µ₁} {µ₂} → ValueSubst._↑ᵣ_  {µ₁ = µ₁} {µ₂ = µ₂})
↑≡ = fun-ext-i (λ µ₁ → fun-ext-i (λ µ₂ → fun-ext (λ ρ → fun-ext (λ m → fun-ext (λ m' → fun-ext (λ x → ↑≡' ρ m m' x))))))

⇓-↑ : {t : Term µ₁ 𝕥} {ρ : µ₁ →ᵣ µ₂} →
  t ⇓ v →
  (t ⋯ ρ) ⇓ v ValueSubst.⋯ ρ
⇓-↑ (⇓-λ t⇓v)              rewrite ↑≡ = ⇓-λ (⇓-↑ t⇓v)
⇓-↑ (⇓-Π t₁⇓v₁ t₂⇓v₂)      rewrite ↑≡ = ⇓-Π (⇓-↑ t₁⇓v₁) (⇓-↑ t₂⇓v₂)
⇓-↑ ⇓-`                               = ⇓-refl-val _
⇓-↑ (⇓-·ᵥ t₁⇓v₁ t₂⇓v₂ t⇓v) rewrite ↑≡ = ⇓-·ᵥ (⇓-↑ t₁⇓v₁) (⇓-↑ t₂⇓v₂) {!⇓-↑ t⇓v!}
⇓-↑ (⇓-·ₙ t₁⇓n₁ t₂⇓v₂)                = ⇓-·ₙ (⇓-↑ t₁⇓n₁) (⇓-↑ t₂⇓v₂)
⇓-↑ ⇓-★                               = ⇓-★

⋯-⟦⟧-comm : ∀ (v : Value µ₁ M) (ρ : µ₁ →ᵣ µ₂) → ⟦ v ⟧ ⋯ ρ ≡ ⟦ v ValueSubst.⋯ ρ ⟧
⋯-⟦⟧-comm (` x) ρ       = refl
⋯-⟦⟧-comm (v₁ · v₂) ρ   = cong₂ _·_ (⋯-⟦⟧-comm v₁ ρ) (⋯-⟦⟧-comm v₂ ρ)
⋯-⟦⟧-comm (λ→ v) ρ      rewrite ↑≡ = cong λ→_ (⋯-⟦⟧-comm v _)
⋯-⟦⟧-comm (Π v₁ v₂) ρ   rewrite ↑≡ = cong₂ Π (⋯-⟦⟧-comm v₁ ρ) (⋯-⟦⟧-comm v₂ _)
⋯-⟦⟧-comm ★ ρ           = refl
⋯-⟦⟧-comm (neutral v) ρ = ⋯-⟦⟧-comm v ρ

⇓ₛ-↑ : {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  σ₁ ⇓ₛ σ₂ →
  (σ₁ ↑ₛ m) ⇓ₛ (σ₂ ↑ₛ m)
⇓ₛ-↑ ⇓σ₁ 𝕥 (here px) = neutral (` here px) ,× ⇓-` ,× refl
⇓ₛ-↑ ⇓σ₁ 𝕥 (there x) with ⇓σ₁ 𝕥 x
⇓ₛ-↑ ⇓σ₁ 𝕥 (there x) | v' ,× ⇓x ,× eq =
  v' ValueSubst.⋯ wk ,× ⇓-↑ ⇓x ,× trans (cong (_⋯ wk) eq) (⋯-⟦⟧-comm v' wk)

id⇓ₛid : idₛ ⇓ₛ idₛ {µ}
id⇓ₛid 𝕥 x = neutral (` x) ,× ⇓-refl-val _ ,× refl

⇓ₛ-ext : {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  σ₁ ⇓ₛ σ₂ →
  t ⇓ v →
  (σ₁ ,ₖ t) ⇓ₛ (σ₂ ,ₖ ⟦ v ⟧)
⇓ₛ-ext σ₁⇓σ₂ t⇓v 𝕥 (here refl) = _ ,× t⇓v ,× refl
⇓ₛ-ext σ₁⇓σ₂ t⇓v 𝕥 (there x) = σ₁⇓σ₂ 𝕥 x

eval-subst-eval : (t₁ : Term µ₁ 𝕥) {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  t₁ ⋯ σ₁ ⇓ v₁ →
  σ₁ ⇓ₛ σ₂ →
  t₁ ⋯ σ₂ ⇓ v₁
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ with ⇓σ₁ _ x
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ | v' ,× ⇓x ,× eq with ⇓-deterministic ⇓t₁ ⇓x
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ | v' ,× ⇓x ,× eq | refl rewrite eq = ⇓-refl-val v'
eval-subst-eval (t₁ · t₂) (⇓-·ᵥ ⇓t₁ ⇓t₂ ⇓t) ⇓σ₁ = ⇓-·ᵥ (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ ⇓σ₁) ⇓t
eval-subst-eval (t₁ · t₂) (⇓-·ₙ ⇓t₁ ⇓t₂)    ⇓σ₁ = ⇓-·ₙ (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ ⇓σ₁)
eval-subst-eval (λ→ t₁)   (⇓-λ ⇓t₁)         ⇓σ₁ = ⇓-λ (eval-subst-eval t₁ ⇓t₁ (⇓ₛ-↑ ⇓σ₁))
eval-subst-eval (Π t₁ t₂) (⇓-Π ⇓t₁ ⇓t₂)     ⇓σ₁ = ⇓-Π (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ (⇓ₛ-↑ ⇓σ₁))
eval-subst-eval ★         ⇓t₁               ⇓σ₁ = ⇓t₁

eval-subst-eval₁ : (t₁ : Term (µ , 𝕥) 𝕥) {t₂ : Term µ 𝕥} →
  t₁ ⋯ ⦅ t₂ ⦆ ⇓ v₁ →
  t₂ ⇓ v₂ →
  t₁ ⋯ ⦅ ⟦ v₂ ⟧ ⦆ ⇓ v₁
eval-subst-eval₁ t₁ ⇓t₁ ⇓t₂ = eval-subst-eval t₁ ⇓t₁ (⇓ₛ-ext id⇓ₛid ⇓t₂)

subject-reduction :
  Γ ⊢ e ∶ τ →
  e ⇓ v →
  Γ ⊢ ⟦ v ⟧ ∶ τ
subject-reduction (τ-λ ⊢t₁ t₁⇓τ₁ ⊢e) (⇓-λ e⇓v) =
  τ-λ ⊢t₁ t₁⇓τ₁ (subject-reduction ⊢e e⇓v )
subject-reduction (τ-Π t₁⇓τ₃ ⊢t₁ ⊢t₂) (⇓-Π t₁⇓τ₁ t₂⇓τ₂)
    with ⇓-deterministic t₁⇓τ₁ t₁⇓τ₃
... | refl =
  τ-Π (⇓-refl-val _) (subject-reduction ⊢t₁ t₁⇓τ₁) (subject-reduction ⊢t₂ t₂⇓τ₂)
subject-reduction ⊢e ⇓-` = ⊢e
subject-reduction (τ-· {τ₂ = τ₂} ⊢e₁ ⊢e₂ τ₂e₂⇓τ) (⇓-·ᵥ e₁⇓λv₁ e₂⇓v₂ v₁v₂⇓v)
    with subject-reduction ⊢e₁ e₁⇓λv₁ | subject-reduction ⊢e₂ e₂⇓v₂
... | τ-λ ⊢t₁ t₁⇓τ₁ ⊢v₁ | ⊢v₂ =
  subject-reduction (subst-pres-ty₁ ⊢v₁ ⊢v₂ (eval-subst-eval₁ ⟦ τ₂ ⟧ τ₂e₂⇓τ e₂⇓v₂)) v₁v₂⇓v
subject-reduction (τ-· {τ₂ = τ₂} ⊢e₁ ⊢e₂ τ₂e₂⇓τ) (⇓-·ₙ e₁⇓n e₂⇓v₂) =
  τ-· (subject-reduction ⊢e₁ e₁⇓n) (subject-reduction ⊢e₂ e₂⇓v₂) (eval-subst-eval₁ ⟦ τ₂ ⟧ τ₂e₂⇓τ e₂⇓v₂)
subject-reduction ⊢e ⇓-★ = ⊢e
