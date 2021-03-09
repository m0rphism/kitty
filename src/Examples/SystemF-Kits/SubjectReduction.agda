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
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term κ k) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                             = tm-vr x
  ⋯-id {κ = κ} {{K}} (λ→ t)   rewrite id↑≡id {{K}} ★ κ = cong λ→_ (⋯-id t)
  ⋯-id {κ = κ} {{K}} (Λ→ t)   rewrite id↑≡id {{K}} ■ κ = cong Λ→_ (⋯-id t)
  ⋯-id {κ = κ} {{K}} (∀→ t)   rewrite id↑≡id {{K}} ■ κ = cong ∀→_ (⋯-id t)
  ⋯-id               (t₁ · t₂)                         = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ∙ t₂)                         = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ ⇒ t₂)                         = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

open KitComposeLemmas kit-compose-lemmas using (⋯-id; dist-⦅⦆ₛ-⋯ₛ; dist-⦅⦆ₛ-⋯ᵣ)

⋯ₜ-id : ∀ {{𝕂 : Kit}} (v : Type κ k) → v ⋯ₜ idₖ {{𝕂}} ≡ v
⋯ₜ-id {k = ★} v = ⋯-id v
⋯ₜ-id {k = ■} v = refl

wkₜ-cancels-,ₛ : (v : Type κ₁ k) (v' : Term κ₂ k') (σ : κ₁ →ₛ κ₂) →
  wkₜ v ⋯ₜ (σ ,ₛ v') ≡ v ⋯ₜ σ
wkₜ-cancels-,ₛ {k = ★} v v' σ = wk-cancels-,ₛ v v' σ
wkₜ-cancels-,ₛ {k = ■} v v' σ = refl

dist-↑-renₜ : ∀ (v : Type κ₁ k') (ρ : κ₁ →ᵣ κ₂) →
  v ⋯ₜ wk ⋯ₜ (ρ ↑ k) ≡ v ⋯ₜ ρ ⋯ₜ wk
dist-↑-renₜ {k' = ★} v σ = dist-↑-ren v σ
dist-↑-renₜ {k' = ■} v σ = refl

dist-↑-subₜ : ∀ (v : Type κ₁ k') (σ : κ₁ →ₛ κ₂) →
  v ⋯ₜ wk ⋯ₜ (σ ↑ k) ≡ v ⋯ₜ σ ⋯ₜ wk
dist-↑-subₜ {k' = ★} v σ = dist-↑-sub v σ
dist-↑-subₜ {k' = ■} v σ = refl

-- Order Preserving Embeddings for Contexts. Required by wk-⊢', where we can't
-- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
-- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
-- constructor).
-- Also arbitrary renamings would allow swapping types in the context which
-- could violate the telescoping (I think).
data OPE : κ₁ →ᵣ κ₂ → Ctx κ₁ → Ctx κ₂ → Set where
  ope-id : ∀ {Γ : Ctx κ} →
    OPE idᵣ Γ Γ
  ope-keep  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₁ k} →
    OPE  ρ       Γ₁        Γ₂ →
    OPE (ρ ↑ k) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ₜ ρ))
  ope-drop  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : Type κ₂ k} →
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
  wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ₜ wk ≡⟨ cong (_⋯ₜ wk) (ope-pres-telescope x ope) ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ ρ        ⋯ₜ wk ≡⟨ ⋯-assoc (wk-drop-∈ x (Γ₁ x)) ρ wk ⟩
  wk-drop-∈ x (Γ₁ x) ⋯ₜ wk ∘ᵣ ρ        ∎

wk-⊢' : ∀ {v : Term κ₁ k} {t : Type κ₁ k} {ρ : κ₁ →ᵣ κ₂} →
  OPE ρ Γ₁ Γ₂ →
  Γ₁ ⊢ v     ∶ t →
  Γ₂ ⊢ v ⋯ ρ ∶ t ⋯ₜ ρ
wk-⊢'               {ρ = ρ} ope (τ-` refl)                 = τ-` (ope-pres-telescope _ ope)
wk-⊢' {t = t₁ ⇒ t₂} {ρ = ρ} ope (τ-λ ⊢v)                   = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-ren t₂ ρ) (wk-⊢' (ope-keep ope) ⊢v))
wk-⊢'                       ope (τ-Λ ⊢v)                   = τ-Λ (wk-⊢' (ope-keep ope) ⊢v)
wk-⊢'                       ope (τ-· ⊢v₁ ⊢v₂)              = τ-· (wk-⊢' ope ⊢v₁) (wk-⊢' ope ⊢v₂)
wk-⊢'               {ρ = ρ} ope (τ-∙ {t₂ = t₂} {t = t} ⊢v) = subst (_ ⊢ _ ∶_) (sym (dist-⦅⦆ₛ-⋯ᵣ t₂ t ρ)) (τ-∙ (wk-⊢' ope ⊢v))
wk-⊢'                       ope τ-★                        = τ-★

wk-⊢ : ∀ {k'} {v : Term κ k} {t : Type κ k} (T : Type κ k') →
  Γ₂        ⊢ v      ∶ t →
  (Γ₂ ,, T) ⊢ wk _ v ∶ wkₜ t
wk-⊢ T ⊢v =  wk-⊢' (ope-drop ope-id) ⊢v

lift-⊢* : ∀ {σ : κ₁ →ₛ κ₂} (T : Type κ₁ k) →
  Γ₂               ⊢*  σ      ∶ Γ₁ →
  (Γ₂ ,, (T ⋯ₜ σ)) ⊢* (σ ↑ k) ∶ (Γ₁ ,, T)
lift-⊢* {k = ★} {σ = σ} T ⊢σ (here refl) = τ-` (sym (dist-↑-sub T σ))
lift-⊢* {k = ■} {σ = σ} T ⊢σ (here refl) = τ-★
lift-⊢* {k = k} {Γ₂ = Γ₂} {Γ₁ = Γ₁} {σ = σ} T ⊢σ (there x) =
  subst ((Γ₂ ,, (T ⋯ₜ σ)) ⊢ (σ _ x ⋯ wk) ∶_)
        (sym (wk-drop-∈ x (Γ₁ x) ⋯ₜ wk ⋯ₜ (σ ↑ k) ≡⟨ dist-↑-subₜ _ σ ⟩
              wk-drop-∈ x (Γ₁ x) ⋯ₜ σ ⋯ₜ wk       ∎))
        (wk-⊢ (T ⋯ₜ σ) (⊢σ x))

sub-pres-⊢ : ∀ {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {v : Term κ₁ k} {t : Type κ₁ k} {σ : κ₁ →ₛ κ₂} →
  Γ₁ ⊢ v ∶ t →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢ v ⋯ σ ∶ t ⋯ₜ σ
sub-pres-⊢ {k = ■}         ⊢v                 ⊢σ = τ-★
sub-pres-⊢ {k = ★}         (τ-` {x = x} refl) ⊢σ = ⊢σ x
sub-pres-⊢ {k = ★} {σ = σ} (τ-λ {t₂ = t₂} ⊢e) ⊢σ = τ-λ (subst (_ ⊢ _ ∶_) (dist-↑-sub t₂ σ) (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ)) )
sub-pres-⊢ {k = ★}         (τ-Λ ⊢e)           ⊢σ = τ-Λ (sub-pres-⊢ ⊢e (lift-⊢* _ ⊢σ))
sub-pres-⊢ {k = ★}         (τ-· ⊢e₁ ⊢e₂)      ⊢σ = τ-· (sub-pres-⊢ ⊢e₁ ⊢σ) (sub-pres-⊢ ⊢e₂ ⊢σ)
sub-pres-⊢ {k = ★} {σ = σ} (τ-∙ {e = e} {t₂ = t₂} {t = t} ⊢e) ⊢σ =
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ ⦅ t ⦆ ⋯ σ            by subst (_ ⊢ e ∙ t ⋯ σ ∶_) (sym (dist-⦅⦆ₛ-⋯ₛ t₂ t σ)) (
  _ ⊢ e ∙ t ⋯ σ ∶ t₂ ⋯ (σ ↑ ■) ⋯ ⦅ t ⋯ σ ⦆    by τ-∙ (sub-pres-⊢ ⊢e ⊢σ))

_,*_ : ∀ {σ : κ₁ →ₛ κ₂} {T : Type κ₁ k₁} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₂ ⊢  v ∶ T ⋯ₜ σ →
  Γ₂ ⊢* σ ,ₛ v ∶ Γ₁ ,, T
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (here refl) = subst (Γ₂ ⊢ v ∶_)     (sym (wkₜ-cancels-,ₛ _ _ _)) ⊢v
_,*_ {Γ₂ = Γ₂} {v = v} {σ = σ} ⊢σ ⊢v (there x)   = subst (Γ₂ ⊢ σ _ x ∶_) (sym (wkₜ-cancels-,ₛ _ _ _)) (⊢σ x)

⊢*-idₛ : ∀ {Γ : Ctx κ} →
  Γ ⊢* idₛ ∶ Γ
⊢*-idₛ {κ = k ∷ κ} {Γ = Γ} {■} x = τ-★
⊢*-idₛ {κ = k ∷ κ} {Γ = Γ} {★} x rewrite ⋯-id {{𝕂 = kitₛ}} (wk-telescope Γ x) = τ-` refl

vsub-pres-⊢ : ∀ {Γ : Ctx κ} {e₁ : Term (★ ∷ κ) ★} {e₂ : Term κ ★} {t₁ t₂ : Type κ ★} →
  Γ ,, t₁ ⊢ e₁ ∶ wk _ t₂ →
  Γ ⊢ e₂ ∶ t₁ →
  Γ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ t₂
vsub-pres-⊢ {e₁ = e₁} {e₂ = e₂} {t₂ = t₂} ⊢e₁ ⊢e₂ =
  subst (_ ⊢ _ ∶_)
        (wk _ t₂ ⋯ ⦅ e₂ ⦆ ≡⟨ wk-cancels-,ₛ t₂ _ _ ⟩
         t₂ ⋯ idₛ         ≡⟨ ⋯-id t₂ ⟩
         t₂               ∎)
        (_ ⊢ e₁ ⋯ ⦅ e₂ ⦆ ∶ wk _ t₂ ⋯ₜ ⦅ e₂ ⦆ by
         sub-pres-⊢ {σ = ⦅ e₂ ⦆}
           ⊢e₁
           (⊢*-idₛ ,* (subst (_ ⊢ _ ∶_) (sym (⋯-id _)) ⊢e₂)))

tsub-pres-⊢ : ∀ {Γ : Ctx κ} {e : Term (■ ∷ κ) ★} {t₂ : Term (■ ∷ κ) ■} {t : Type κ ★} →
  Γ ,, tt ⊢ e ∶ t₂ →
  Γ ⊢ t ∶ tt →
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
