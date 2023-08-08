module Kitty.Examples.SystemFSub-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.SystemFSub-Derive.Definitions
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open TypingKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Term.Terms
Injective-Map :
  ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂} →
  S₁ –[ K ]→ S₂ → Set
Injective-Map ϕ = ∀ s (x y : _ ∋ s) → ϕ _ x ≡ ϕ _ y → x ≡ y

wkn-injective : ∀ {S} {s} → Injective-Map  (wknᵣ {S = S} {s = s})
wkn-injective _ _ _ refl = refl

-- ⋯-injective :
--   ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} ⦃ K : Kit _∋/⊢_ ⦄ {S₁} {S₂}
--     {ϕ : S₁ –[ K ]→ S₂} →
--   Injective-Map ϕ →
--   ∀ {st} {s : Sort st} (e₁ e₂ : S₁ ⊢ s) →
--   e₁ ⋯ ϕ ≡ e₂ ⋯ ϕ →
--   e₁ ≡ e₂
-- ⋯-injective ϕ-inj (` x) (` y) eq = cong `_ (ϕ-inj _ x y (`/id-injective eq)) 

there-injective : ∀ {s'} {x y : S ∋ s'} → there {x = s} {xs = S} x ≡ there y → x ≡ y
there-injective refl = refl 

↑-Injective :
  ∀ {S₁} {S₂} {ϕ : S₁ →ᵣ S₂} {s} →
  Injective-Map ϕ →
  Injective-Map (ϕ ↑ s)
↑-Injective inj-ϕ s (here refl) (here refl) eq = refl
↑-Injective inj-ϕ s (here refl) (there y)   ()
↑-Injective inj-ϕ s (there x)   (here refl) ()
↑-Injective inj-ϕ s (there x)   (there y)   eq = cong there (inj-ϕ s x y (there-injective eq))

λx-injective : ∀ {e₁ e₂ : S ▷ 𝕖 ⊢ 𝕖} → (S ⊢ 𝕖 by λx e₁) ≡ (λx e₂) → e₁ ≡ e₂
λx-injective refl = refl 

Λα-injective : ∀ {e₁ e₂ : S ▷ 𝕥 ⊢ 𝕖} → (S ⊢ 𝕖 by Λα e₁) ≡ (Λα e₂) → e₁ ≡ e₂
Λα-injective refl = refl 

∀α-injective : ∀[α⊑ t₁₁ ] t₁₂ ≡ ∀[α⊑ t₂₁ ] t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
∀α-injective refl = refl , refl

·-injective : e₁₁ · e₁₂ ≡ e₂₁ · e₂₂ → e₁₁ ≡ e₂₁ × e₁₂ ≡ e₂₂
·-injective refl = refl , refl

∙-injective : e₁₁ ∙ t₁₂ ≡ e₂₁ ∙ t₂₂ → e₁₁ ≡ e₂₁ × t₁₂ ≡ t₂₂
∙-injective refl = refl , refl

⇒-injective : t₁₁ ⇒ t₁₂ ≡ t₂₁ ⇒ t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
⇒-injective refl = refl , refl

∶⊑-injective : t₁₁ ∶⊑ t₁₂ ≡ t₂₁ ∶⊑ t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
∶⊑-injective refl = refl , refl

⋯-injective :
  ∀ {S₁} {S₂}
    {ϕ : S₁ →ᵣ S₂} →
  Injective-Map ϕ →
  ∀ {st} {s : Sort st} (e₁ e₂ : S₁ ⊢ s) →
  e₁ ⋯ ϕ ≡ e₂ ⋯ ϕ →
  e₁ ≡ e₂
⋯-injective ϕ-inj (` x₁)           (` x₂)           eq = cong `_ (ϕ-inj _ x₁ x₂ (`/id-injective eq))
⋯-injective ϕ-inj (λx e₁)          (λx e₂)          eq = cong λx_ (⋯-injective (↑-Injective ϕ-inj) e₁ e₂ (λx-injective eq))
⋯-injective ϕ-inj (Λα e₁)          (Λα e₂)          eq = cong Λα_ (⋯-injective (↑-Injective ϕ-inj) e₁ e₂ (Λα-injective eq))
⋯-injective ϕ-inj (∀[α⊑ e₁₁ ] e₁₂) (∀[α⊑ e₂₁ ] e₂₂) eq = cong₂ ∀[α⊑_]_
                                                               (⋯-injective ϕ-inj e₁₁ e₂₁ (proj₁ (∀α-injective eq)))
                                                               (⋯-injective (↑-Injective ϕ-inj) e₁₂ e₂₂ (proj₂ (∀α-injective eq)))
⋯-injective ϕ-inj (e₁₁ · e₁₂)      (e₂₁ · e₂₂)      eq = cong₂ _·_ (⋯-injective ϕ-inj e₁₁ e₂₁ (proj₁ (·-injective eq)))
                                                                   (⋯-injective ϕ-inj e₁₂ e₂₂ (proj₂ (·-injective eq)))
⋯-injective ϕ-inj (e₁₁ ∙ e₁₂)      (e₂₁ ∙ e₂₂)      eq = cong₂ _∙_ (⋯-injective ϕ-inj e₁₁ e₂₁ (proj₁ (∙-injective eq)))
                                                                   (⋯-injective ϕ-inj e₁₂ e₂₂ (proj₂ (∙-injective eq)))
⋯-injective ϕ-inj (e₁₁ ⇒ e₁₂)      (e₂₁ ⇒ e₂₂)      eq = cong₂ _⇒_ (⋯-injective ϕ-inj e₁₁ e₂₁ (proj₁ (⇒-injective eq)))
                                                                   (⋯-injective ϕ-inj e₁₂ e₂₂ (proj₂ (⇒-injective eq)))
⋯-injective ϕ-inj `tt              `tt              eq = refl
⋯-injective ϕ-inj 𝟙                𝟙                eq = refl
⋯-injective ϕ-inj (e₁₁ ∶⊑ e₁₂)     (e₂₁ ∶⊑ e₂₂)     eq = cong₂ _∶⊑_ (⋯-injective ϕ-inj e₁₁ e₂₁ (proj₁ (∶⊑-injective eq)))
                                                                    (⋯-injective ϕ-inj e₁₂ e₂₂ (proj₂ (∶⊑-injective eq)))
⋯-injective ϕ-inj ★                ★                eq = refl
⋯-injective ϕ-inj cstr             cstr             eq = refl
⋯-injective ϕ-inj Cstr             Cstr             eq = refl


subst₃ : ∀ {A B C : Set} (f : A → B → C → Set) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a → f y v b
subst₃ _ refl refl refl p = p

mutual
  -- Substitution of type vars needs to respect constraints:
  --   (` α ∶⊑ t) ∈ Γ₁  →  Γ₂ ⊢ ϕ _ α ⊑ t 
  _⊑ₐ⋯_ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
      ⦃ IK : TypingKit K W C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
      {ϕ : S₁ –[ K ]→ S₂} →
    Γ₁ ⊢ t₁ ⊑ₐ t₂ →
    Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
    Γ₂ ⊢ (t₁ ⋯ ϕ) ⊑ₐ (t₂ ⋯ ϕ)
  ⊑ₐ-` t₁⊑t₂ y t₂⊑t₃         ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-` (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ) (y ⊢⋯ ⊢ϕ) (t₂⊑t₃ ⊑ₐ⋯ ⊢ϕ)
  ⊑ₐ-𝟙                       ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-𝟙
  ⊑ₐ-⇒ t₁⊑t₂ t₁⊑t₃           ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-⇒ (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ) (t₁⊑t₃ ⊑ₐ⋯ ⊢ϕ)
  ⊑ₐ-∀ t₁⊑t₂                 ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-∀ (t₁⊑t₂ ⊑ₐ⋯ (⊢ϕ ∋↑/⊢↑ _))
  ⊑ₐ-refl-var                ⊑ₐ⋯ ⊢ϕ = ⊑ₐ-refl

  _⊢⋯_ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W : KitT K ⦄ ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
      ⦃ IK : TypingKit K W C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit K Kₛ Kₛ ⦄
      {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
    Γ₁ ⊢ e ∶ t →
    Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
    Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
  ⊢` ∋x              ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
  ⊢λ {t₂ = t₂} ⊢e    ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
  _⊢⋯_ {Γ₂ = Γ₂} ⦃ K = K ⦄ {ϕ = ϕ} (⊢Λ {t₁ = t₁} {e = e} {t₂ = t₂} ⊢e) ⊢ϕ =
    ⊢Λ (subst₃ (λ ■₁ ■₂ ■₃ → Γ₂ ▶ ★ ▶ ■₁ ⊢ ■₂ ∶ ■₃)
               (((# 0) ∶⊑ (t₁ ⋯ᵣ wkn)) ⋯ (ϕ ↑ _)                         ≡⟨⟩
                (`/id (id/` ⦃ K ⦄ (here refl)) ∶⊑ (t₁ ⋯ᵣ wkn ⋯ (ϕ ↑ _))) ≡⟨ cong (_∶⊑ (t₁ ⋯ᵣ wkn ⋯ ϕ ↑ _))
                                                                                 (id/`/id ⦃ K ⦄ (here refl)) ⟩
                ((# 0) ∶⊑ (t₁ ⋯ᵣ wkn ⋯ (ϕ ↑ _)))                         ≡⟨ cong ((# 0) ∶⊑_) (dist-↑-f t₁ ϕ) ⟩
                ((# 0) ∶⊑ (t₁ ⋯ ϕ ⋯ᵣ wkn))                               ∎)
               (e ⋯ᵣ wkn ⋯ (ϕ ↑ _ ↑ _) ≡⟨ dist-↑-f e (ϕ ↑ _) ⟩
                e ⋯ (ϕ ↑ _) ⋯ᵣ wkn     ∎)
               (t₂ ⋯ᵣ wkn ⋯ (ϕ ↑ _ ↑ _) ≡⟨ dist-↑-f t₂ (ϕ ↑ _) ⟩
                t₂ ⋯ (ϕ ↑ _) ⋯ᵣ wkn     ∎)
               (⊢e ⊢⋯ ((⊢ϕ ∋↑/⊢↑ _) ∋↑/⊢↑ _)))
  ⊢· ⊢e₁ ⊢e₂         ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
  _⊢⋯_ {Γ₂ = Γ₂} ⦃ K = K ⦄ {ϕ = ϕ} (⊢∙ {t = t} {t₁ = t₁} {t₂ = t₂} {e₁ = e} ⊢t₁ ⊢t₂ t₂⊑t ⊢e) ⊢ϕ =
    subst₂ (Γ₂ ⊢_∶_)
           refl
           (t₁ ⋯ (ϕ ↑ _) ⋯ ⦅ t₂ ⋯ ϕ ⦆ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ t₁ t₂ _) ⟩
            t₁ ⋯ ⦅ t₂ ⦆ₛ ⋯ ϕ           ∎)
           (⊢∙ (subst₂ (λ ■₁ ■₂ → Γ₂ ▶ ★ ▶ ■₁ ⊢ ■₂ ∶ ★)
                       ((((# 0) ∶⊑ (t ⋯ᵣ wkn)) ⋯ (ϕ ↑ _)) ≡⟨ cong (_∶⊑ (t ⋯ᵣ wkn ⋯ ϕ ↑ _))
                                                                  (id/`/id ⦃ K ⦄ (here refl)) ⟩
                        ((# 0) ∶⊑ (t ⋯ᵣ wkn ⋯ (ϕ ↑ _)))  ≡⟨ cong ((# 0) ∶⊑_) (dist-↑-f t ϕ) ⟩
                        ((# 0) ∶⊑ (t ⋯ ϕ ⋯ᵣ wkn)) ∎)
                       (t₁ ⋯ᵣ wkn ⋯ (ϕ ↑ _ ↑ _) ≡⟨ dist-↑-f t₁ (ϕ ↑ _) ⟩
                       t₁ ⋯ (ϕ ↑ _) ⋯ᵣ wkn ∎)
                       (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _ ∋↑/⊢↑ _))) (⊢t₂ ⊢⋯ ⊢ϕ) (t₂⊑t ⊑ₐ⋯ ⊢ϕ) (⊢e ⊢⋯ ⊢ϕ))
  ⊢tt                ⊢⋯ ⊢ϕ = ⊢tt
  ⊢τ                 ⊢⋯ ⊢ϕ = ⊢τ
  ⊢cstr t₁⊑t₂        ⊢⋯ ⊢ϕ = ⊢cstr (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ)
  ⊢⊑ ⊢e t₁⊑t₂        ⊢⋯ ⊢ϕ = ⊢⊑ (⊢e ⊢⋯ ⊢ϕ) (t₁⊑t₂ ⊑ₐ⋯ ⊢ϕ)

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

ren-pres-↪ : {e e' : S ⊢ s'} (ρ : S →ᵣ S') →
  e ↪ e' →
  e ⋯ᵣ ρ ↪ e' ⋯ᵣ ρ
ren-pres-↪ {e = e} {e' = e'} ρ e↪e' with #e ← e ⋯ᵣ ρ in eq-e | #e' ← e' ⋯ᵣ ρ in eq-e' with e↪e' | eq-e | eq-e'
... | β-λ {e₁ = e₁} {e₂ = e₂} | refl | refl = subst ((λx (e₁ ⋯ ρ ↑ _)) · (e₂ ⋯ ρ) ↪_)
                                                    (e₁ ⋯ᵣ (ρ ↑ _) ⋯ₛ ⦅ e₂ ⋯ ρ ⦆'ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ e₁ e₂ ρ) ⟩
                                                     e₁ ⋯ₛ ⦅ e₂ ⦆'ₛ ⋯ᵣ ρ ∎)
                                                    β-λ
... | β-Λ {e₁ = e₁} {t₂ = t₂} | refl | refl = subst ((Λα (e₁ ⋯ ρ ↑ _)) ∙ (t₂ ⋯ ρ) ↪_)
                                                    (e₁ ⋯ᵣ (ρ ↑ _) ⋯ₛ ⦅ t₂ ⋯ ρ ⦆'ₛ ≡⟨ sym (dist-⦅⦆ₛ-⋯ e₁ t₂ ρ) ⟩
                                                     e₁ ⋯ₛ ⦅ t₂ ⦆'ₛ ⋯ᵣ ρ ∎)
                                                    β-Λ
... | ξ-λ e↪e''  | refl | refl = ξ-λ (ren-pres-↪ (ρ ↑ _) e↪e'')
... | ξ-Λ e↪e''  | refl | refl = ξ-Λ (ren-pres-↪ (ρ ↑ _) e↪e'')
... | ξ-·₁ e↪e'' | refl | refl = ξ-·₁ (ren-pres-↪ ρ e↪e'')
... | ξ-·₂ e↪e'' | refl | refl = ξ-·₂ (ren-pres-↪ ρ e↪e'')
... | ξ-∙₁ e↪e'' | refl | refl = ξ-∙₁ (ren-pres-↪ ρ e↪e'')

Valid : Ctx S → Set
Valid {S} Γ =
  ∀ (x : S ∋ 𝕔) {t₁ t₂} →
  Γ ∋ x ∶ (t₁ ∶⊑ t₂) →
  ∃[ y ] t₁ ≡ ` y

∶⊑-wkn : ∀ {t₁ t₂ : S ▷ s ⊢ 𝕥} (t : S ⊢ ℂ) →
  (t₁ ∶⊑ t₂) ≡ t ⋯ wknᵣ →
  ∃[ t₁' ] ∃[ t₂' ] t₁ ≡ t₁' ⋯ wknᵣ × t₂ ≡ t₂' ⋯ wknᵣ
∶⊑-wkn (t₁' ∶⊑ t₂') refl = t₁' , t₂' , refl , refl

data Valid-Type {S} : S ⊢ s → Set where
  instance Valid-𝕥 : ∀ {t : S ⊢ 𝕥} → Valid-Type t
  instance Valid-𝕜 : ∀ {t : S ⊢ 𝕜} → Valid-Type t
  instance Valid-𝕔 : ∀ {α : S ∋ 𝕥} {t : S ⊢ 𝕥} → Valid-Type ((` α) ∶⊑ t)

Valid-▶ : ∀ {Γ : Ctx S} →
  Valid Γ →
  (t : S ∶⊢ s) →
  ⦃ _ : Valid-Type t ⦄ →
  Valid (_▶_ {s = s} Γ t)
Valid-▶ {Γ = Γ} ⊢Γ _ ⦃ Valid-𝕔 {α = α} {t = t} ⦄ (here refl) {t₁} {t₂} ∋x
 with trans (sym (wk-telescope-here Γ ((` α) ∶⊑ t))) ∋x
... | refl = there α , refl
Valid-▶ {Γ = Γ} ⊢Γ t ⦃ Vt ⦄ (there x) {t₁} {t₂} ∋x
 with ∶⊑-wkn (wk-telescope Γ x) (
        (t₁ ∶⊑ t₂)                     ≡⟨ sym ∋x ⟩
        wk-telescope (Γ ▶ t) (there x) ≡⟨ wk-telescope-there Γ t x ⟩
        wk-telescope Γ x ⋯ wknᵣ        ∎)
... | t₁ , t₂ , refl , refl
 with ⊢Γ x (wk-telescope Γ x ≡⟨ ⋯-injective wkn-injective _ _ ∋x ⟩ (t₁ ∶⊑ t₂) ∎)
... | y , eq =
  there y , cong (_⋯ wknᵣ) eq

invert-λ : {Γ : Ctx S} →
  Γ ⊢ λx e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    Γ ⊢ (t₁ ⇒ t₂) ⊑ₐ t ×
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkn
invert-λ (⊢λ ⊢e) = _ , _ , ⊑ₐ-refl , ⊢e
invert-λ (⊢⊑ ⊢e t₃⊑t) with invert-λ ⊢e
... | t₁ , t₂ , [t₁⇒t₂]⊑t₃ , ⊢e = _ , _ , ⊑ₐ-trans [t₁⇒t₂]⊑t₃ t₃⊑t , ⊢e

invert-Λ : {Γ : Ctx S} →
  Γ ⊢ Λα e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ₐ t ×
    Γ ▶ ★ ▶ (# 0 ∶⊑ (t₁ ⋯ᵣ wkn)) ⊢ (e ⋯ᵣ wkn {s = 𝕔}) ∶ (t₂ ⋯ᵣ wkn)
invert-Λ (⊢Λ ⊢e) = _ , _ , ⊑ₐ-refl , ⊢e
invert-Λ (⊢⊑ ⊢e t₃⊑t) with invert-Λ ⊢e
... | t₁ , t₂ , [t₁⇒t₂]⊑t₃ , ⊢e = _ , _ , ⊑ₐ-trans [t₁⇒t₂]⊑t₃ t₃⊑t , ⊢e

-- This is the key for getting the inversion lemmas to work:
-- By requiring `Valid Γ` we know that a subtype of a type variable
-- has to be also a type variable, so it cannot be a ∀- or ⇒-type.
invert-⊑` : ∀ {Γ : Ctx S} {α : S ∋ 𝕥} →
  Valid Γ →
  Γ ⊢ t ⊑ₐ (` α) →
  ∃[ β ] t ≡ ` β
invert-⊑` ⊢Γ ⊑ₐ-refl-var = _ , refl
invert-⊑` ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr t₁⊑t₂) st₂)
 with invert-⊑` ⊢Γ st₂
... | β₁ , refl
 with invert-⊑` ⊢Γ t₁⊑t₂
... | β₂ , refl
 with invert-⊑` ⊢Γ st₁
... | β₃ , refl
 = β₃ , refl
invert-⊑` ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂)
 with ⊢Γ c ∋c
... | y , refl
 with invert-⊑` ⊢Γ st₁
... | β₂ , refl
 = β₂ , refl

open import Data.Sum using (_⊎_; inj₁; inj₂)
invert-⊑⇒' : {Γ : Ctx S} →
  Valid Γ →
  Γ ⊢ t ⊑ₐ (t₁' ⇒ t₂') →
  (∃[ t₁ ] ∃[ t₂ ] t ≡ t₁ ⇒ t₂ × Γ ⊢ t₁' ⊑ₐ t₁ × Γ ⊢ t₂ ⊑ₐ t₂') ⊎ (∃[ α ] t ≡ ` α)
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂) with ⊢Γ c ∋c
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂) | α , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) with invert-⊑⇒' ⊢Γ st₃
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) with invert-⊑` ⊢Γ st₂
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) | β , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁'⊑t₁ , t₂⊑t₂') with invert-⊑⇒' ⊢Γ st₂
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁'⊑t₁ , t₂⊑t₂') | inj₂ (α , refl) = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁'⊑t₁ , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) with invert-⊑⇒' ⊢Γ st₁
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁'⊑t₁ , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) | inj₂ (α , refl) = inj₂ (α , refl)
invert-⊑⇒' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁'⊑t₁ , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) | inj₁ (t₁y , t₂y , refl , t₁x⊑t₁y , t₂y⊑t₂x) = inj₁ (_ , _ , refl , ⊑ₐ-trans t₁'⊑t₁ (⊑ₐ-trans t₁⊑t₁x t₁x⊑t₁y) , ⊑ₐ-trans t₂y⊑t₂x (⊑ₐ-trans t₂x⊑t₂ t₂⊑t₂'))
invert-⊑⇒' ⊢Γ (⊑ₐ-⇒ st₁ st₂) = inj₁ (_ , _ , refl , st₁ , st₂)

-- Not true in general, because the input subtyping could be a faulty
-- assumption instead of an arrow subtyping rule.
-- For this to hold we need to forbid faulty assumptions, or add rules
-- which allow to close faulty assumptions under inversion.
invert-⊑⇒ : {Γ : Ctx S} →
  Valid Γ →
  Γ ⊢ (t₁ ⇒ t₂) ⊑ₐ (t₁' ⇒ t₂') →
  Γ ⊢ t₁' ⊑ₐ t₁ × Γ ⊢ t₂ ⊑ₐ t₂'
invert-⊑⇒ ⊢Γ st with invert-⊑⇒' ⊢Γ st
... | inj₁ (_ , _ , refl , st₁ , st₂) = st₁ , st₂

-- TODO: Exactly the same proof as for ⇒
invert-⊑∀' : {Γ : Ctx S} {t₁' : S ⊢ 𝕥} {t₂' : S ▷ 𝕥 ⊢ 𝕥} →
  Valid Γ →
  Γ ⊢ t ⊑ₐ (∀[α⊑ t₁' ] t₂') →
  (∃[ t₁ ] ∃[ t₂ ] t ≡ (∀[α⊑ t₁ ] t₂) × t₁ ≡ t₁' × Γ ▶ ★ ⊢ t₂ ⊑ₐ t₂') ⊎ (∃[ α ] t ≡ ` α)
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂) with ⊢Γ c ∋c
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂) | α , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) with invert-⊑∀' ⊢Γ st₃
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) with invert-⊑` ⊢Γ st₂
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) | β , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂') with invert-⊑∀' ⊢Γ st₂
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂') | inj₂ (α , refl) = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) with invert-⊑∀' ⊢Γ st₁
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) | inj₂ (α , refl) = inj₂ (α , refl)
invert-⊑∀' ⊢Γ (⊑ₐ-` {c = cstr} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂') | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) | inj₁ (t₁y , t₂y , refl , refl , t₂y⊑t₂x) = inj₁ (_ , _ , refl , refl , ⊑ₐ-trans t₂y⊑t₂x (⊑ₐ-trans t₂x⊑t₂ t₂⊑t₂'))
invert-⊑∀' ⊢Γ (⊑ₐ-∀ st) = inj₁ (_ , _ , refl , refl , st)

invert-⊑∀ : {Γ : Ctx S} {t₁ t₁' : S ⊢ 𝕥} {t₂ t₂' : S ▷ 𝕥 ⊢ 𝕥} →
  Valid Γ →
  Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ₐ (∀[α⊑ t₁' ] t₂') →
  t₁ ≡ t₁' × Γ ▶ ★ ⊢ t₂ ⊑ₐ t₂'
invert-⊑∀ ⊢Γ st with invert-⊑∀' ⊢Γ st
... | inj₁ (_ , _ , refl , refl , st) = refl , st

subject-reduction :
  Valid Γ →
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction ⊢Γ (⊢· {e₂ = e₂} ⊢e₁ ⊢e₂) β-λ
 with invert-λ ⊢e₁
... | t₁ , t₂ , st , ⊢e₁'
 with invert-⊑⇒ ⊢Γ st
... | st₁ , st₂
 = let st₂' = subst (_ ⊢_⊑ₐ _) (
                t₂                   ≡⟨ sym (wk-cancels-⦅⦆ t₂ e₂) ⟩
                t₂ ⋯ᵣ wkn ⋯ ⦅ e₂ ⦆'ₛ ∎
              ) st₂ in
   ⊢⊑ (⊢e₁' ⊢⋯ₛ ⊢⦅ ⊢⊑ ⊢e₂ st₁ ⦆ₛ) st₂'
subject-reduction {Γ = Γ} ⊢Γ (⊢∙ {t = t-bound} {t₁ = t-body} {t₂ = t-arg} {e₁ = Λα e₁} ⊢t-body ⊢t-arg t-arg⊑t-bound ⊢e)   β-Λ
 with invert-Λ ⊢e
... | _ , t-body' , st , ⊢e'
 with invert-⊑∀ ⊢Γ st
... | refl , t-body'⊑t-body
 = -- First we substitute the type variable at #1, which is under the constraint binding #0
   let ⊢e'' = Γ ▶ (t-arg ∶⊑ t-bound) ⊢ e₁ ⋯ ⦅ t-arg ⦆ₛ ⋯ᵣ wknᵣ ∶ t-body' ⋯ ⦅ t-arg ⦆ₛ ⋯ᵣ wknᵣ
              by subst₃ (λ ■₁ ■₂ ■₃ → Γ ▶ (t-arg ∶⊑ ■₁) ⊢ ■₂ ∶ ■₃)
                        (wk-cancels-⦅⦆ t-bound t-arg)
                        (dist-↑-f e₁ ⦅ t-arg ⦆ₛ)
                        (dist-↑-f t-body' ⦅ t-arg ⦆ₛ)
                        (
              Γ ▶ (t-arg ∶⊑ (t-bound ⋯ wknᵣ ⋯ ⦅ t-arg ⦆ₛ )) ⊢ e₁ ⋯ᵣ wknᵣ ⋯ (⦅ t-arg ⦆ₛ ↑ 𝕔) ∶ t-body' ⋯ᵣ wknᵣ ⋯ (⦅ t-arg ⦆ₛ ↑ 𝕔)
              by ⊢e' ⊢⋯ₛ (⊢⦅ ⊢t-arg ⦆ₛ ⊢↑ ((# 0) ∶⊑ (t-bound ⋯ wknᵣ)))
              ) in
   -- Then we get rid of the constraint binding, since the constraint follows already from Γ
   let ⊢e''' = Γ ⊢ e₁ ⋯ ⦅ t-arg ⦆ₛ ∶ t-body' ⋯ ⦅ t-arg ⦆ₛ
               by subst₂ (Γ ⊢_∶_) (wk-cancels-⦅⦆ (e₁ ⋯ ⦅ t-arg ⦆) cstr) (wk-cancels-⦅⦆ (t-body' ⋯ ⦅ t-arg ⦆) cstr) (
               Γ ⊢ e₁ ⋯ ⦅ t-arg ⦆ₛ ⋯ᵣ wknᵣ ⋯ ⦅ cstr ⦆ₛ ∶ t-body' ⋯ ⦅ t-arg ⦆ ⋯ᵣ wknᵣ ⋯ ⦅ cstr ⦆ₛ 
               by ⊢e'' ⊢⋯ₛ ⊢⦅ ⊢cstr t-arg⊑t-bound ⦆ₛ
               ) in
               -- by entail {t = t-body' ⋯ ⦅ t-arg ⦆ₛ} {e = e₁ ⋯ ⦅ t-arg ⦆ₛ} ⊢e'' t-arg⊑t-bound in
   ⊢⊑ ⊢e''' (t-body'⊑t-body ⊑ₐ⋯ ⊢⦅ ⊢t-arg ⦆ₛ)
subject-reduction ⊢Γ (⊢λ ⊢e)              (ξ-λ e↪e')  = ⊢λ (subject-reduction (Valid-▶ ⊢Γ _) ⊢e e↪e')
subject-reduction ⊢Γ (⊢Λ ⊢e)              (ξ-Λ e↪e')  = ⊢Λ (subject-reduction (Valid-▶ (Valid-▶ ⊢Γ ★) _) ⊢e (ren-pres-↪ wkn e↪e'))
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)         (ξ-·₁ e↪e') = ⊢· (subject-reduction ⊢Γ ⊢e₁ e↪e') ⊢e₂
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)         (ξ-·₂ e↪e') = ⊢· ⊢e₁ (subject-reduction ⊢Γ ⊢e₂ e↪e')
subject-reduction ⊢Γ (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e) (ξ-∙₁ e↪e') = ⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (subject-reduction ⊢Γ ⊢e e↪e')
subject-reduction ⊢Γ (⊢⊑ ⊢e t⊑t')         e↪e'        = ⊢⊑ (subject-reduction ⊢Γ  ⊢e e↪e') t⊑t'
