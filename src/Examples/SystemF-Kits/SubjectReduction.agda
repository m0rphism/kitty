module Examples.SystemF-Kits.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)

open import Examples.SystemF-Kits.Definitions

kit-compose-lemmas : KitComposeLemmas
kit-compose-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term κ K) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                             = tm-vr x
  ⋯-id {κ = κ} {{K}} (λ→ t)   rewrite id↑≡id {{K}} ★ κ = cong λ→_ (⋯-id t)
  ⋯-id {κ = κ} {{K}} (Λ→ t)   rewrite id↑≡id {{K}} ■ κ = cong Λ→_ (⋯-id t)
  ⋯-id {κ = κ} {{K}} (∀→ t)   rewrite id↑≡id {{K}} ■ κ = cong ∀→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               [★]                               = refl

open KitComposeLemmas kit-compose-lemmas using (⋯-id; dist-⦅⦆ₛ-⋯ₛ; dist-⦅⦆ₛ-⋯ᵣ)

-- Order Preserving Embeddings for Contexts. Required by wk-⊢', where we can't
-- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
-- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
-- constructor).
-- Also arbitrary renamings would allow swapping types in the context which
-- could violate the telescoping (I think).
data OPE : κ₁ →ᵣ κ₂ → Ctx κ₁ → Ctx κ₂ → Set where
  ope-id : ∀ {Γ : Ctx κ} →
    OPE idᵣ Γ Γ
  ope-keep  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₁ (k→K k)} →
    OPE  ρ       Γ₁        Γ₂ →
    OPE (ρ ↑ k) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ ρ))
  ope-drop  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₂ (k→K k)} →
    OPE  ρ        Γ₁  Γ₂ →
    OPE (wk ∘ᵣ ρ) Γ₁ (Γ₂ ,, T)

-- TODO: works equally well with k instead of ★, but requires even more ⋯ₜ versions of ⋯ lemmas...
ope-pres-telescope : ∀ {ρ : κ₁ →ᵣ κ₂} (x : κ₁ ∋ ★) →
  OPE ρ Γ₁ Γ₂ →
  wk-drop-∈ (ρ ★ x) (Γ₂ (ρ ★ x)) ≡ wk-drop-∈ x (Γ₁ x) ⋯ ρ
ope-pres-telescope x           ope-id = sym (⋯-id _)
ope-pres-telescope (here refl) (ope-keep {ρ = ρ} {T = T} ope) = sym (dist-↑-ren T ρ)
ope-pres-telescope (there x)   (ope-keep {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk _ (wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x))) ≡⟨ cong (wk _) (ope-pres-telescope x ope) ⟩
  wk _ (wk-drop-∈ x (Γ₁ x) ⋯ ρ)         ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
  wk _ (wk-drop-∈ x (Γ₁ x)) ⋯ ρ ↑ _     ∎
ope-pres-telescope x           (ope-drop {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk ≡⟨ cong (_⋯ wk) (ope-pres-telescope x ope) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ ρ         ⋯ wk ≡⟨ ⋯-assoc (wk-drop-∈ x (Γ₁ x)) ρ wk ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ wk ∘ᵣ ρ        ∎

wk-⊢' : ∀ {v : Term κ₁ K} {t : Type κ₁ K} {ρ : κ₁ →ᵣ κ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ v     ∶ t →
  Γ₂ ⊢ v ⋯ ρ ∶ t ⋯ ρ
wk-⊢'               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
wk-⊢' {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢v)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (wk-⊢' (ope-keep ope) ⊢v))
wk-⊢'                       ope (τ-Λ ⊢v)                   = τ-Λ (wk-⊢' (ope-keep ope) ⊢v)
wk-⊢'                       ope (τ-· ⊢v₁ ⊢v₂)              = τ-· (wk-⊢' ope ⊢v₁) (wk-⊢' ope ⊢v₂)
wk-⊢'               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢v) = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ᵣ t₂ t ρ)) (τ-∙ (wk-⊢' ope ⊢v))
wk-⊢'                       ope τ-★                        = τ-★
wk-⊢'                       ope τ-[★]                      = τ-[★]

wk-⊢ : ∀ {k'} {v : Term κ K} {t : Type κ K} (T : Type κ (k→K k')) →
  Γ₂        ⊢ v      ∶ t →
  (Γ₂ ,, T) ⊢ wk _ v ∶ wk _ t
wk-⊢ T ⊢v =  wk-⊢' (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : κ₁ →ₛ κ₂} (T : Type κ₁ (k→K k)) →
  Γ₂              ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ,, (T ⋯ σ)) ⊢* (σ ↑ k) ∶ (Γ₁ ,, T)
lift-⊢* {k = ★} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-↑-sub T σ))
lift-⊢* {k = ■} {Γ₂ = Γ₂} {σ = σ} T ⊢σ (here refl) rewrite Term●→[★] T = τ-★
lift-⊢* {k = k} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
  subst ((Γ₂ ,, (T ⋯ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ wk ⋯ (σ ↑ k) ≡⟨ dist-↑-sub (wk-drop-∈ x (Γ₁ x)) σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ σ ⋯ wk       ∎))
        (wk-⊢ (T ⋯ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {v : Term κ₁ K} {t : Type κ₁ K} {σ : κ₁ →ₛ κ₂} →
  Γ₁ ⊢ v ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ v ⋯ σ ∶ t ⋯ σ
sub-pres-⊢ {K = ■} {t = [★]}           ⊢v                 ⊢σ = τ-★
sub-pres-⊢ {K = ●} {v = [★]} {t = [★]} ⊢v                 ⊢σ = τ-[★]
sub-pres-⊢ {K = ★}                     (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {K = ★} {σ = σ}             (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
sub-pres-⊢ {K = ★}                     (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {K = ★}                     (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)
sub-pres-⊢ {K = ★} {σ = σ}             (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ            by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⦅⦆ₛ-⋯ₛ t₂ t σ)) (
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ ■) ⋯ ⦅ t ⋯ σ ⦆    by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

_,*_ : ∀ {σ : κ₁ →ₛ κ₂} {T : Type κ₁ (k→K k₁)} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  v ∶ T ⋯ σ →
  Γ₂ ⊢* σ ,ₛ v ∶ Γ₁ ,, T
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} {T = T} ⊢σ ⊢v (here refl) = subst (Γ₂ ⊢ v ∶_)     (sym (wk-cancels-,ₛ T _ _)) ⊢v
_,*_ {Γ₂ = Γ₂} {Γ₁ = Γ₁} {v = v} {σ = σ} {T = T} ⊢σ ⊢v (there x)   = subst (Γ₂ ⊢ σ _ x ∶_) (sym (wk-cancels-,ₛ (wk-drop-∈ x (Γ₁ x)) _ _)) (⊢σ x)

⊢*-idₛ : ∀ {Γ : Ctx κ} →
  Γ ⊢* idₛ ∶ Γ
⊢*-idₛ {κ = k ∷ κ} {Γ = Γ} {■} x rewrite Term●→[★] (wk-telescope Γ x) = τ-★
⊢*-idₛ {κ = k ∷ κ} {Γ = Γ} {★} x rewrite ⋯-id {{𝕂 = kitₛ}} (wk-telescope Γ x) = τ-` refl

vsub-pres-⊢ : ∀ {Γ : Ctx κ} {e₁ : Term (★ ∷ κ) ★} {e₂ : Term κ ★} {t₁ t₂ : Type κ ★} →
  Γ ,, t₁ ⊢ e₁ ∶ wk _ t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂
vsub-pres-⊢ {Γ = Γ} {e₁ = e₁} {e₂ = e₂} {t₂ = t₂} ⊢e₁ ⊢e₂ =
  subst (_ ⊢ _ ∶_)
        (wk _ t₂ ⋯ ⦅ e₂ ⦆ ≡⟨ wk-cancels-,ₛ t₂ _ _ ⟩
         t₂ ⋯ idₛ         ≡⟨ ⋯-id t₂ ⟩
         t₂               ∎)
        (Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ wk _ t₂ ⋯ ⦅ e₂ ⦆ by
          sub-pres-⊢ {σ = ⦅ e₂ ⦆}
            ⊢e₁
            (⊢*-idₛ ,* (subst (Γ ⊢ e₂ ∶_) (sym (⋯-id _)) ⊢e₂)))

tsub-pres-⊢ : ∀ {Γ : Ctx κ} {e : Term (■ ∷ κ) ★} {t₂ : Term (■ ∷ κ) ■} {t : Type κ ★} →
  Γ ,, [★] ⊢ e ∶ t₂ →
  Γ ⊢ t ∶ [★] →
  Γ ⊢ e ⋯ ⦅ t ⦆ ∶ t₂ ⋯ ⦅ t ⦆
tsub-pres-⊢ ⊢e ⊢t = sub-pres-⊢ ⊢e (⊢*-idₛ ,* ⊢t)

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
