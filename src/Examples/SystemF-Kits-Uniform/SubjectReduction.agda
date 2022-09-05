module Examples.SystemF-Kits-Uniform.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Examples.SystemF-Kits-Uniform.Definitions

K≡★ : ∀ (K : Term µ 𝕜) → K ≡ ★
K≡★ (`[_]_ {m = 𝕖} () x)
K≡★ (`[_]_ {m = 𝕥} () x)
K≡★ ★ = refl

ope-pres-⊢ : ∀ {E : Term µ₁ M} {T : Type µ₁ M} {ρ : µ₁ →ᵣ µ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ E     ∶ T →
  Γ₂ ⊢ E ⋯ ρ ∶ T ⋯ ρ
ope-pres-⊢               {ρ = ρ} ope (τ-` refl)                        = τ-` (ope-pres-telescope _ ope)
ope-pres-⊢ {T = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢e)                          = τ-λ (ope-pres-⊢ (ope-keep ope) ⊢e)
ope-pres-⊢                       ope (τ-Λ ⊢e)                          = τ-Λ (ope-pres-⊢ (ope-keep ope) ⊢e)
ope-pres-⊢               {ρ = ρ} ope (τ-· {t₂ = t₂} {e₂ = e₂} ⊢e₁ ⊢e₂) = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ᵣ t₂ e₂ ρ)) (τ-· (ope-pres-⊢ ope ⊢e₁) (ope-pres-⊢ ope ⊢e₂))
ope-pres-⊢               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢e)        = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ᵣ t₂ t ρ)) (τ-∙ (ope-pres-⊢ ope ⊢e))
ope-pres-⊢                       ope τ-𝕥                               = τ-𝕥
ope-pres-⊢                       ope τ-𝕜                               = τ-𝕜

wk-pres-⊢ : ∀ {m'} {E : Term µ M} {T : Type µ M} (T' : Type µ (m→M m')) →
  Γ₂        ⊢ E      ∶ T →
  (Γ₂ ▶ T') ⊢ wk _ E ∶ wk _ T
wk-pres-⊢ T ⊢v =  ope-pres-⊢ (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : µ₁ →ₛ µ₂} (T : Type µ₁ (m→M m)) →
  Γ₂             ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ▶ (T ⋯ σ)) ⊢* (σ ↑ m) ∶ (Γ₁ ▶ T)
lift-⊢* {m = 𝕖} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-↑-sub T σ))
lift-⊢* {m = 𝕥} {Γ₂ = Γ₂} {σ = σ} T ⊢σ (here refl) rewrite K≡★ T = τ-𝕥
lift-⊢* {m = m} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
  subst ((Γ₂ ▶ (T ⋯ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ (σ ↑ m) ≡⟨ dist-↑-sub (wk-drop-∈ x (Γ₁ x)) σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ σ ⋯ wk       ∎))
        (wk-pres-⊢ (T ⋯ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {E : Term µ₁ M} {T : Type µ₁ M} {σ : µ₁ →ₛ µ₂} →
  Γ₁ ⊢ E ∶ T →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ E ⋯ σ ∶ T ⋯ σ
sub-pres-⊢ {M = 𝕥} {T = ★}         ⊢v                     ⊢σ = τ-𝕥
sub-pres-⊢ {M = 𝕜} {E = ★} {T = ★} ⊢v                     ⊢σ = τ-𝕜
sub-pres-⊢ {M = 𝕖}                     (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {M = 𝕖}                     (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {M = 𝕖}                     (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {M = 𝕖} {σ = σ}             (τ-· {e₁ = e₁} {t₂ = t₂} {e₂ = e₂} ⊢e₁ ⊢e₂)      ⊢σ =
  _ ⊢ e₁ · e₂ ⋯ σ ∶ t₂ ⋯ ⦅ e₂ ⦆ ⋯ σ            by subst (_ ⊢ e₁ · e₂ ⋯ σ ∶_) (sym (dist-⦅⦆ₛ-⋯ₛ t₂ e₂ σ)) (
  _ ⊢ e₁ · e₂ ⋯ σ ∶ t₂ ⋯ (σ ↑ 𝕖) ⋯ ⦅ e₂ ⋯ σ ⦆    by τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ))
sub-pres-⊢ {M = 𝕖} {σ = σ}             (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ               by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⦅⦆ₛ-⋯ₛ t₂ t σ)) (
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ 𝕥) ⋯ ⦅ t ⋯ σ ⦆       by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

_,*_ : ∀ {σ : µ₁ →ₛ µ₂} {T : Type µ₁ (m→M m₁)} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  E ∶ T ⋯ σ →
  Γ₂ ⊢* σ ,ₛ E ∶ Γ₁ ▶ T
_,*_ {Γ₂ = Γ₂} {E = E} {T = T} ⊢σ ⊢E (here refl) = subst (Γ₂ ⊢ E ∶_) (sym (wk-cancels-,ₛ T _ _)) ⊢E
_,*_ {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} ⊢σ ⊢v (there x) = subst (Γ₂ ⊢ σ _ x ∶_) (sym (wk-cancels-,ₛ (wk-drop-∈ x (Γ₁ x)) _ _)) (⊢σ x)

⊢*-idₛ : Γ ⊢* idₛ ∶ Γ
⊢*-idₛ {Γ = Γ} {𝕥} x rewrite K≡★ (wk-telescope Γ x)   = τ-𝕥
⊢*-idₛ {Γ = Γ} {𝕖} x rewrite ⋯-idₛ (wk-telescope Γ x) = τ-` refl

sub₁-pres-⊢ : ∀ {Γ : Ctx µ} {E₁ : Term (µ ▷ m₂) M₁} {E₂ : Term µ (m→M m₂)} {T₂ : Type (µ ▷ m₂) M₁} {T₁ : Type µ (m→M m₂)} →
  Γ ▶ T₁ ⊢ E₁ ∶ T₂ →
  Γ ⊢ E₂ ∶ T₁ →
  Γ ⊢ E₁ ⋯ ⦅ E₂ ⦆ ∶ T₂ ⋯ ⦅ E₂ ⦆
sub₁-pres-⊢ {Γ = Γ} {E₂ = E₂} ⊢E₁ ⊢E₂ = sub-pres-⊢ ⊢E₁ (⊢*-idₛ ,* subst (Γ ⊢ E₂ ∶_) (sym (⋯-id _)) ⊢E₂)

open import Data.List using (_++_)

sub-𝕖-in-𝕥-id-var : ∀ (α : (µ ▷ 𝕖 ▷▷ µ') ∋ 𝕥) (e₁ e₂ : Term µ 𝕖) → (⦅ e₁ ⦆ ↑* µ') 𝕥 α ≡ (⦅ e₂ ⦆ ↑* µ') 𝕥 α
sub-𝕖-in-𝕥-id-var {µ' = []}      (there α)   e₁ e₂ = refl
sub-𝕖-in-𝕥-id-var {µ' = µ' ▷ .𝕥} (here refl) e₁ e₂ = refl
sub-𝕖-in-𝕥-id-var {µ' = µ' ▷ m}  (there α)   e₁ e₂ = cong (_⋯ wk) (sub-𝕖-in-𝕥-id-var α e₁ e₂)

sub-𝕖-in-𝕥-id : ∀ (t : Term (µ ▷ 𝕖 ▷▷ µ') 𝕥) (e₁ e₂ : Term µ 𝕖) →
  t ⋯ (⦅ e₁ ⦆ ↑* µ') ≡ t ⋯ (⦅ e₂ ⦆ ↑* µ')
sub-𝕖-in-𝕥-id (`[_]_ {m = 𝕥} refl x) e₁ e₂ = sub-𝕖-in-𝕥-id-var x e₁ e₂
sub-𝕖-in-𝕥-id (∀α t)                 e₁ e₂ = cong ∀α_ (sub-𝕖-in-𝕥-id t e₁ e₂)
sub-𝕖-in-𝕥-id (t₁ ⇒ t₂)              e₁ e₂ = cong₂ _⇒_ (sub-𝕖-in-𝕥-id t₁ e₁ e₂) (sub-𝕖-in-𝕥-id t₂ e₁ e₂)

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (τ-· (τ-λ ⊢e₁) ⊢e₂)      β-λ                                = sub₁-pres-⊢ ⊢e₁ ⊢e₂
subject-reduction (τ-∙ (τ-Λ ⊢e))           β-Λ                                = sub₁-pres-⊢ ⊢e τ-𝕥
subject-reduction (τ-λ ⊢e)                (ξ-λ  e↪e')                         = τ-λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-Λ ⊢e)                (ξ-Λ  e↪e')                         = τ-Λ (subject-reduction ⊢e e↪e')
subject-reduction (τ-· ⊢e₁ ⊢e₂)           (ξ-·₁ e₁↪e₁')                       = τ-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (τ-· {t₂ = t₂} ⊢e₁ ⊢e₂) (ξ-·₂ {e₂ = e₂} {e₂' = e₂'} e₂↪e₂') = subst (_ ⊢ _ ∶_) (sym (sub-𝕖-in-𝕥-id t₂ e₂ e₂')) (τ-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂'))
subject-reduction (τ-∙ ⊢e)                (ξ-∙  e↪e')                         = τ-∙ (subject-reduction ⊢e e↪e')
