module Examples.SystemFLin-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)
open import Substructural.Usage

open import Examples.SystemFLin-Kits.Definitions

-- K≡★ : ∀ (K : Term µ 𝕜) → K ≡ ★
-- K≡★ (`[_]_ {m = 𝕖} () x)
-- K≡★ (`[_]_ {m = 𝕥} () x)
-- K≡★ ★ = refl

-- wk-⊢' : ∀ {E : Term µ₁ M} {T : Type µ₁ M} {ρ : µ₁ →ᵣ µ₂} →
--   OPE ρ Γ₁ Γ₂ →
--   Γ₁ ⊢ E     ∶ T →
--   Γ₂ ⊢ E ⋯ ρ ∶ T ⋯ ρ
-- wk-⊢'               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
-- wk-⊢' {T = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (wk-⊢' (ope-keep ope) ⊢e))
-- wk-⊢'                       ope (τ-Λ ⊢e)                   = τ-Λ (wk-⊢' (ope-keep ope) ⊢e)
-- wk-⊢'                       ope (τ-· ⊢e₁ ⊢e₂)              = τ-· (wk-⊢' ope ⊢e₁) (wk-⊢' ope ⊢e₂)
-- wk-⊢'               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢e) = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ᵣ t₂ t ρ)) (τ-∙ (wk-⊢' ope ⊢e))
-- wk-⊢'                       ope τ-𝕥                        = τ-𝕥
-- wk-⊢'                       ope τ-𝕜                        = τ-𝕜

-- wk-⊢ : ∀ {m'} {E : Term µ M} {T : Type µ M} (T' : Type µ (m→M m')) →
--   Γ₂         ⊢ E      ∶ T →
--   (Γ₂ ,, T') ⊢ wk _ E ∶ wk _ T
-- wk-⊢ T ⊢v =  wk-⊢' (ope-drop ope-id) ⊢v

-- lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (T : Type µ₁ (m→M m)) →
--   Γ₂              ⊢*  σ      ∶ Γ₁ →
--   (Γ₂ ,, (T ⋯ σ)) ⊢* (σ ↑ m) ∶ (Γ₁ ,, T)
-- lift-⊢* {m = 𝕖} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-↑-sub T σ))
-- lift-⊢* {m = 𝕥} {Γ₂ = Γ₂} {σ = σ} T ⊢σ (here refl) rewrite K≡★ T = τ-𝕥
-- lift-⊢* {m = m} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
--   subst ((Γ₂ ,, (T ⋯ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
--         (sym (wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ (σ ↑ m) ≡⟨ dist-↑-sub (wk-drop-∈ x (Γ₁ x)) σ ⟩
--               wk-drop-∈ x (Γ₁ x) ⋯ σ ⋯ wk       ∎))
--         (wk-⊢ (T ⋯ σ) (⊢σ x))

sub-pres-⊢' : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {E : Term (m ∷ µ₁) M}  {E' : Term µ₁ (m→M m)} {T : Type (m ∷ µ₁) M} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ▶ T' ; Ψ₁ ▶ᵤ u ⊢ E ∶ T →
  Γ₁ ; Ψ₁ ⊢ E' ∶ T' →
  Γ₁ ; Ψ₁ ⊢ E ⋯ ⦅ E' ⦆ ∶ T ⋯ ⦅ E' ⦆
sub-pres-⊢' = {!!}

sub-pres-⊢ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {E : Term µ₁ M} {T : Type µ₁ M} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ; Ψ₁ ⊢ E ∶ T →
  Γ₂ ; Ψ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ; Ψ₂ ⊢ E ⋯ σ ∶ T ⋯ σ
  -- Γ₂ ; Ψ₁ + Ψ₂ ⊢ E ⋯ σ ∶ T ⋯ σ
sub-pres-⊢ = {!!}
-- sub-pres-⊢ {M = 𝕥} {T = ★}         ⊢v                     ⊢σ = τ-𝕥
-- sub-pres-⊢ {M = 𝕜} {E = ★} {T = ★} ⊢v                     ⊢σ = τ-𝕜
-- sub-pres-⊢ {M = 𝕖}                     (τ-` {x = x} refl) ⊢σ = ⊢σ x
-- sub-pres-⊢ {M = 𝕖} {σ = σ}             (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
-- sub-pres-⊢ {M = 𝕖}                     (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
-- sub-pres-⊢ {M = 𝕖}                     (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)
-- sub-pres-⊢ {M = 𝕖} {σ = σ}             (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
--   _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ            by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⦅⦆ₛ-⋯ₛ t₂ t σ)) (
--   _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ 𝕥) ⋯ ⦅ t ⋯ σ ⦆    by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

-- _,*_ : ∀ {σ : µ₁ →ₛ µ₂} {T : Type µ₁ (m→M m₁)} →
--   Γ₂ ⊢* σ ∶ Γ₁ →
--   Γ₂ ⊢  E ∶ T ⋯ σ →
--   Γ₂ ⊢* σ ,ₛ E ∶ Γ₁ ,, T
-- _,*_ {Γ₂ = Γ₂} {E = E} {T = T} ⊢σ ⊢E (here refl) = subst (Γ₂ ⊢ E ∶_) (sym (wk-cancels-,ₛ T _ _)) ⊢E
-- _,*_ {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢v (there x) = subst (Γ₂ ⊢ σ _ x ∶_) (sym (wk-cancels-,ₛ (wk-drop-∈ x (Γ₁ x)) _ _)) (⊢σ x)

-- ⊢*-idₛ : Γ ⊢* idₛ ∶ Γ
-- ⊢*-idₛ {Γ = Γ} {𝕥} x rewrite K≡★ (wk-telescope Γ x) = τ-𝕥
-- ⊢*-idₛ {Γ = Γ} {𝕖} x rewrite ⋯-id {{𝕂 = kitₛ}} (wk-telescope Γ x) = τ-` refl

-- vsub-pres-⊢ : ∀ {Γ : Ctx µ} {e₁ : Term (𝕖 ∷ µ) 𝕖} {e₂ : Term µ 𝕖} {t₁ t₂ : Type µ 𝕖} →
--   Γ ,, t₁ ⊢ e₁ ∶ wk _ t₂ →
--   Γ ⊢ e₂ ∶ t₁ →
--   Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂
-- vsub-pres-⊢ {Γ = Γ} {e₁ = e₁} {e₂ = e₂} {t₂ = t₂} ⊢e₁ ⊢e₂ =
--   subst (_ ⊢ _ ∶_)
--         (wk _ t₂ ⋯ ⦅ e₂ ⦆ ≡⟨ wk-cancels-,ₛ t₂ _ _ ⟩
--          t₂ ⋯ idₛ         ≡⟨ ⋯-id t₂ ⟩
--          t₂               ∎)
--         (Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ wk _ t₂ ⋯ ⦅ e₂ ⦆ by
--           sub-pres-⊢ {σ = ⦅ e₂ ⦆}
--             ⊢e₁
--             (⊢*-idₛ ,* (subst (Γ ⊢ e₂ ∶_) (sym (⋯-id _)) ⊢e₂)))

-- tsub-pres-⊢ : ∀ {Γ : Ctx µ} {e : Term (𝕥 ∷ µ) 𝕖} {t₂ : Term (𝕥 ∷ µ) 𝕥} {t : Type µ 𝕖} →
--   Γ ,, ★ ⊢ e ∶ t₂ →
--   Γ ⊢ t ∶ ★ →
--   Γ ⊢ e ⋯ ⦅ t ⦆ ∶ t₂ ⋯ ⦅ t ⦆
-- tsub-pres-⊢ ⊢e ⊢t = sub-pres-⊢ ⊢e (⊢*-idₛ ,* ⊢t)

subject-reduction :
  Γ ; Ψ ⊢ e ∶ t →
  e ↪ e' →
  Γ ; Ψ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢t Ψ*⟦u⟧ ⊢e₁) ⊢e₂)  β-λ        = {!vsub-pres-⊢ ⊢e₁ ⊢e₂!}
subject-reduction (τ-∙ (τ-Λ ⊢e) ⊢t )            β-Λ        = {!tsub-pres-⊢ ⊢e τ-𝕥!}
subject-reduction (τ-λ ⊢t Ψ*⟦u⟧ ⊢e)            (ξ-λ  e↪e') = τ-λ ⊢t Ψ*⟦u⟧ (subject-reduction ⊢e e↪e')
subject-reduction (τ-Λ ⊢e)                     (ξ-Λ  e↪e') = τ-Λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)                (ξ-·₁ e↪e') = τ-· (subject-reduction ⊢e₁ e↪e') ⊢e₂
subject-reduction (τ-· ⊢e₁ ⊢e₂)                (ξ-·₂ e↪e') = τ-· ⊢e₁ (subject-reduction ⊢e₂ e↪e')
subject-reduction (τ-∙ ⊢e  ⊢t)                 (ξ-∙  e↪e') = τ-∙ (subject-reduction ⊢e e↪e') ⊢t
