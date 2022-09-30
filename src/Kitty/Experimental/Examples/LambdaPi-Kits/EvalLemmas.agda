module Kitty.Experimental.Examples.LambdaPi-Kits.EvalLemmas where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Experimental.Examples.LambdaPi-Kits.Definitions
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

_⇓ₛ_ : (σ₁ σ₂ : µ₁ →ₛ µ₂) → Set
σ₁ ⇓ₛ σ₂ = ∀ m x → ∃[ v ] (σ₁ m x ⇓' v × σ₂ m x ≡ ⟦ v ⟧')

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
postulate
  fun-ext-i : ∀ {ℓ₁ ℓ₂} →
    {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : {x : A} → B x} →
    (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

↑≡'' : ∀ (ρ : µ₁ →ᵣ µ₂) m m' x → (ρ ↑ m) m' x ≡ (ρ ↑ᵥ m) m' x
↑≡'' ρ m m' (here px) = refl
↑≡'' ρ m m' (there x) = refl

↑≡' : ∀ (ρ : µ₁ →ᵣ µ₂) m → (ρ ↑ m) ≡ (ρ ↑ᵥ m)
↑≡' ρ m = fun-ext (λ m' → fun-ext (λ x → ↑≡'' ρ m m' x))

↑≡ : (λ {µ₁} {µ₂} → _↑_ {µ₁ = µ₁} {µ₂ = µ₂}) ≡ (λ {µ₁} {µ₂} → ValueSubst._↑_  {µ₁ = µ₁} {µ₂ = µ₂})
↑≡ = fun-ext-i (λ µ₁ → fun-ext-i (λ µ₂ → fun-ext (λ ρ → fun-ext (λ m → fun-ext (λ m' → fun-ext (λ x → ↑≡'' ρ m m' x))))))

⋯-⟦⟧-comm : ∀ (v : Value µ₁ M) (ρ : µ₁ →ᵣ µ₂) → ⟦ v ⟧ ⋯ ρ ≡ ⟦ v ⋯ᵥ ρ ⟧
⋯-⟦⟧-comm (` x) ρ       = refl
⋯-⟦⟧-comm (v₁ · v₂) ρ   = cong₂ _·_ (⋯-⟦⟧-comm v₁ ρ) (⋯-⟦⟧-comm v₂ ρ)
⋯-⟦⟧-comm (λ→ v) ρ      rewrite ↑≡ = cong λ→_ (⋯-⟦⟧-comm v _)
⋯-⟦⟧-comm (Π v₁ v₂) ρ   rewrite ↑≡ = cong₂ Π (⋯-⟦⟧-comm v₁ ρ) (⋯-⟦⟧-comm v₂ _)
⋯-⟦⟧-comm ★ ρ           = refl
⋯-⟦⟧-comm (neutral v) ρ = ⋯-⟦⟧-comm v ρ

lem : ∀ (v₁ : Value (µ₁ ▷ 𝕥) M) (v₂ : Value µ₁ M) (ρ : µ₁ →ᵣ µ₂) →
  ⟦ v₁ ⟧ ⋯ ⦅ ⟦ v₂ ⟧ ⦆ ⋯ ρ
  ≡
  ⟦ v₁ ⋯ᵥ ρ ↑ᵥ 𝕥 ⟧ ⋯ ⦅ ⟦ v₂ ⋯ᵥ ρ ⟧ ⦆
lem {µ₁ = µ₁} {M = M} v₁ v₂ ρ rewrite sym (↑≡' ρ 𝕥) =
  ⟦ v₁ ⟧ ⋯ ⦅ ⟦ v₂ ⟧ ⦆ ⋯ ρ
    ≡⟨ dist-⦅⦆ₛ-⋯ᵣ ⟦ v₁ ⟧ ⟦ v₂ ⟧ ρ ⟩
  ⟦ v₁ ⟧ ⋯ ρ ↑ 𝕥 ⋯ ⦅ ⟦ v₂ ⟧ ⋯ ρ ⦆ₛ
    ≡⟨ cong₂ _⋯_ (⋯-⟦⟧-comm v₁ (ρ ↑ 𝕥)) (cong ⦅_⦆ₛ (⋯-⟦⟧-comm v₂ ρ)) ⟩
  ⟦ v₁ ⋯ᵥ ρ ↑ 𝕥 ⟧ ⋯ ⦅ ⟦ v₂ ⋯ᵥ ρ ⟧ ⦆
    ∎

⇓-↑ : {t : Term µ₁ 𝕥} {ρ : µ₁ →ᵣ µ₂} →
  t ⇓ v →
  (t ⋯ ρ) ⇓ v ⋯ᵥ ρ
⇓-↑ (⇓-λ t⇓v)              rewrite ↑≡ = ⇓-λ (⇓-↑ t⇓v)
⇓-↑ (⇓-Π t₁⇓v₁ t₂⇓v₂)      rewrite ↑≡ = ⇓-Π (⇓-↑ t₁⇓v₁) (⇓-↑ t₂⇓v₂)
⇓-↑ ⇓-`                               = ⇓-refl-val _
⇓-↑ {ρ = ρ} (⇓-·ᵥ {v₁ = v₁} {v₂ = v₂} t₁⇓v₁ t₂⇓v₂ t⇓v) = ⇓-·ᵥ (⇓-↑ t₁⇓v₁) (⇓-↑ t₂⇓v₂) (subst (_⇓ _) (lem v₁ v₂ ρ) (⇓-↑ t⇓v))
⇓-↑ (⇓-·ₙ t₁⇓n₁ t₂⇓v₂)                = ⇓-·ₙ (⇓-↑ t₁⇓n₁) (⇓-↑ t₂⇓v₂)
⇓-↑ ⇓-★                               = ⇓-★

⇓ₛ-↑ : {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  σ₁ ⇓ₛ σ₂ →
  (σ₁ ↑ₛ m) ⇓ₛ (σ₂ ↑ₛ m)
⇓ₛ-↑ ⇓σ₁ 𝕥 (here px) = neutral (` here px) ,× ⇓-` ,× refl
⇓ₛ-↑ ⇓σ₁ 𝕥 (there x) with ⇓σ₁ 𝕥 x
⇓ₛ-↑ ⇓σ₁ 𝕥 (there x) | v' ,× ⇓x ,× eq =
  v' ⋯ᵥ wk ,× ⇓-↑ ⇓x ,× trans (cong (_⋯ wk) eq) (⋯-⟦⟧-comm v' wk)

id⇓ₛid : idₛ ⇓ₛ idₛ {µ}
id⇓ₛid 𝕥 x = neutral (` x) ,× ⇓-refl-val _ ,× refl

⇓ₛ-ext : {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  σ₁ ⇓ₛ σ₂ →
  t ⇓ v →
  (σ₁ ,ₖ t) ⇓ₛ (σ₂ ,ₖ ⟦ v ⟧)
⇓ₛ-ext σ₁⇓σ₂ t⇓v 𝕥 (here refl) = _ ,× t⇓v ,× refl
⇓ₛ-ext σ₁⇓σ₂ t⇓v 𝕥 (there x) = σ₁⇓σ₂ 𝕥 x

postulate
  eval-subst-evalₗ : (t : Term µ₁ 𝕥) {σ : µ₁ →ₛ µ₂} →
    ⟦ v' ⟧ ⋯ₛ σ ⇓ v →
    t ⇓ v' →
    t ⋯ₛ σ ⇓ v
-- eval-subst-evalₗ t⋯σ⇓v t⇓v' = {!!}

eval-subst-eval : (t₁ : Term µ₁ 𝕥) {σ₁ σ₂ : µ₁ →ₛ µ₂} →
  t₁ ⋯ₛ σ₁ ⇓ v₁ →
  σ₁ ⇓ₛ σ₂ →
  t₁ ⋯ₛ σ₂ ⇓ v₁
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ with ⇓σ₁ _ x
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ | v' ,× ⇓x ,× eq with ⇓-deterministic ⇓t₁ ⇓x
eval-subst-eval (` x)     ⇓t₁               ⇓σ₁ | v' ,× ⇓x ,× eq | refl rewrite eq = ⇓-refl-val v'
eval-subst-eval (t₁ · t₂) (⇓-·ᵥ ⇓t₁ ⇓t₂ ⇓t) ⇓σ₁ = ⇓-·ᵥ (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ ⇓σ₁) ⇓t
eval-subst-eval (t₁ · t₂) (⇓-·ₙ ⇓t₁ ⇓t₂)    ⇓σ₁ = ⇓-·ₙ (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ ⇓σ₁)
eval-subst-eval (λ→ t₁)   (⇓-λ ⇓t₁)         ⇓σ₁ = ⇓-λ (eval-subst-eval t₁ ⇓t₁ (⇓ₛ-↑ ⇓σ₁))
eval-subst-eval (Π t₁ t₂) (⇓-Π ⇓t₁ ⇓t₂)     ⇓σ₁ = ⇓-Π (eval-subst-eval t₁ ⇓t₁ ⇓σ₁) (eval-subst-eval t₂ ⇓t₂ (⇓ₛ-↑ ⇓σ₁))
eval-subst-eval ★         ⇓t₁               ⇓σ₁ = ⇓t₁

eval-subst-eval₁ : (t₁ : Term (µ ▷ 𝕥) 𝕥) {t₂ : Term µ 𝕥} →
  t₁ ⋯ₛ ⦅ t₂ ⦆ₛ ⇓ v₁ →
  t₂ ⇓ v₂ →
  t₁ ⋯ₛ ⦅ ⟦ v₂ ⟧ ⦆ₛ ⇓ v₁
eval-subst-eval₁ t₁ ⇓t₁ ⇓t₂ = eval-subst-eval t₁ ⇓t₁ (⇓ₛ-ext id⇓ₛid ⇓t₂)

infixr 1 _by_
_by_ : (T : Set) → T → T
T by t = t

⊢*id :
  Γ ⊢* idₛ ∶ Γ
⊢*id {Γ = Γ} x =
  wk-telescope Γ x ,×
  (subst (_⇓ wk-telescope Γ x) (sym (⋯-idₛ ⟦ wk-telescope Γ x ⟧)) (⇓-refl-val _)) ,×
  τ-` refl

⊢*-ext : {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {σ : µ₁ →ₛ µ₂} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ e ∶ τ →
  ⟦ τ' ⟧ ⋯ σ ⇓ τ →
  Γ₂ ⊢* σ ,ₖ e ∶ Γ₁ ▶ τ'
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (here refl) =
  let Γx⋯σ⇓τ =
        ⟦ wk-telescope (Γ₁ ▶ τ') (here refl) ⟧ ⋯ (σ ,ₖ e) ⇓ τ
          by
        ⟦ τ' ⋯ᵥ wk ⟧ ⋯ (σ ,ₛ e) ⇓ τ
          by subst (λ h → h ⋯ (σ ,ₖ e) ⇓ τ) (⋯-⟦⟧-comm τ' wk) (
        ⟦ τ' ⟧ ⋯ wk ⋯ (σ ,ₛ e) ⇓ τ
          by subst (_⇓ τ) (sym (wk-cancels-,ₛ ⟦ τ' ⟧ σ e)) (
        ⟦ τ' ⟧ ⋯ σ  ⇓ τ
          by τ'σ⇓τ))
  in τ ,× Γx⋯σ⇓τ ,× ⊢e
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (there x) with ⊢σ x
⊢*-ext {e = e} {τ = τ} {τ' = τ'} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢e τ'σ⇓τ (there x) | τ₁' ,× ⇓τ₁' ,× ⊢' =
  let Γx⋯σ⇓τ =
        ⟦ wk-telescope (Γ₁ ▶ τ') (there x) ⟧ ⋯ (σ ,ₛ e) ⇓ τ₁'
          by
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⋯ᵥ wk ⟧ ⋯ (σ ,ₛ e) ⇓ τ₁'
          by subst (λ h → h ⋯ (σ ,ₖ e) ⇓ τ₁') (⋯-⟦⟧-comm (ValueSubst.wk-drop-∈ x (Γ₁ x)) wk) (
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ wk ⋯ (σ ,ₛ e) ⇓ τ₁'
          by subst (_⇓ τ₁') (sym (wk-cancels-,ₛ ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ σ e)) (
        ⟦ ValueSubst.wk-drop-∈ x (Γ₁ x) ⟧ ⋯ σ ⇓ τ₁'
          by
        ⇓τ₁'))
  in τ₁' ,× Γx⋯σ⇓τ ,× ⊢'

ren-pres-⇓ : (ρ : µ₁ →ᵣ µ₂) →
  e     ⇓ v →
  e ⋯ ρ ⇓ v ⋯ᵥ ρ
ren-pres-⇓ ρ (⇓-λ e⇓v)              rewrite sym ↑≡ = ⇓-λ (ren-pres-⇓ (ρ ↑ 𝕥) e⇓v)
ren-pres-⇓ ρ (⇓-Π e₁⇓v₁ e₂⇓v₂)      rewrite sym ↑≡ = ⇓-Π (ren-pres-⇓ ρ e₁⇓v₁) (ren-pres-⇓ (ρ ↑ 𝕥) e₂⇓v₂)
ren-pres-⇓ ρ ⇓-`                    = ⇓-`
ren-pres-⇓ {v = v} ρ (⇓-·ᵥ {v₁ = v₁} {v₂ = v₂} e₁⇓v₁ e₂⇓v₂ e⇓v) =
  let X = ⟦ v₁ ⋯ᵥ ρ ↑ᵥ 𝕥 ⟧ ⋯ ⦅ ⟦ v₂ ⋯ᵥ ρ ⟧ ⦆ ⇓ v ⋯ᵥ ρ
            by subst (λ ■ → ■ ⋯ ⦅ ⟦ v₂ ⋯ᵥ ρ ⟧ ⦆ ⇓ v ⋯ᵥ ρ) (⋯-⟦⟧-comm v₁ (ρ ↑ᵥ 𝕥)) (
          ⟦ v₁ ⟧ ⋯ ρ ↑ᵥ 𝕥 ⋯ ⦅ ⟦ v₂ ⋯ᵥ ρ ⟧ ⦆ ⇓ v ⋯ᵥ ρ
            by subst (λ ■ → ⟦ v₁ ⟧ ⋯ ρ ↑ᵥ 𝕥 ⋯ ⦅ ■ ⦆ ⇓ v ⋯ᵥ ρ) (⋯-⟦⟧-comm v₂ ρ) (
          ⟦ v₁ ⟧ ⋯ ρ ↑ᵥ 𝕥 ⋯ₛ ⦅ ⟦ v₂ ⟧ ⋯ ρ ⦆ ⇓ v ⋯ᵥ ρ
            by subst (λ ■ → ⟦ v₁ ⟧ ⋯ ■ ρ 𝕥 ⋯ₛ ⦅ ⟦ v₂ ⟧ ⋯ ρ ⦆ ⇓ v ⋯ᵥ ρ) ↑≡ (
          ⟦ v₁ ⟧ ⋯ ρ ↑ 𝕥 ⋯ₛ ⦅ ⟦ v₂ ⟧ ⋯ ρ ⦆ ⇓ v ⋯ᵥ ρ
            by subst (λ ■ → ■ ⇓ v ⋯ᵥ ρ) (dist-⦅⦆ₛ-⋯ᵣ ⟦ v₁ ⟧ ⟦ v₂ ⟧ ρ) (
          ⟦ v₁ ⟧ ⋯ ⦅ ⟦ v₂ ⟧ ⦆ ⋯ ρ ⇓ v ⋯ᵥ ρ
            by ren-pres-⇓ ρ e⇓v))))
  in ⇓-·ᵥ (ren-pres-⇓ ρ e₁⇓v₁) (ren-pres-⇓ ρ e₂⇓v₂) X
ren-pres-⇓ ρ (⇓-·ₙ e₁⇓n₁ e₂⇓v₂)     = ⇓-·ₙ (ren-pres-⇓ ρ e₁⇓n₁) (ren-pres-⇓ ρ e₂⇓v₂)
ren-pres-⇓ ρ ⇓-★                    = ⇓-★
