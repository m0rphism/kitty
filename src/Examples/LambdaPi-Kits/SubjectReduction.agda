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

subject-reduction :
  Γ ⊢ e ∶ τ →
  e ⇓ v →
  Γ ⊢ ⟦ v ⟧ ∶ τ
subject-reduction (τ-λ ⊢t₁ t₁⇓τ₁ ⊢e) (⇓-λ e⇓v) =
  τ-λ ⊢t₁ t₁⇓τ₁ (subject-reduction ⊢e e⇓v )
subject-reduction (τ-Π t₁⇓τ₃ ⊢t₁ ⊢t₂) (⇓-Π t₁⇓τ₁ t₂⇓τ₂)
    with ⇓-deterministic t₁⇓τ₁ t₁⇓τ₃
... | refl = τ-Π (⇓-refl-val _) (subject-reduction ⊢t₁ t₁⇓τ₃) (subject-reduction ⊢t₂ t₂⇓τ₂)
subject-reduction ⊢e ⇓-` = ⊢e
subject-reduction ⊢e (⇓-·ᵥ e₁⇓λv₁ e₂⇓v₂ v₁v₂⇓v) = {!!}
subject-reduction (τ-· ⊢e₁ ⊢e₂ τ₂e₂⇓τ) (⇓-·ₙ e₁⇓n e₂⇓v) =
  τ-· (subject-reduction ⊢e₁ e₁⇓n) (subject-reduction ⊢e₂ e₂⇓v) {!τ₂e₂⇓τ!}
subject-reduction ⊢e ⇓-★ = ⊢e
