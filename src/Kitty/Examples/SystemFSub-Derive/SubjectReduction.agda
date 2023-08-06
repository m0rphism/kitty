module Kitty.Examples.SystemFSub-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.SystemFSub-Derive.Definitions
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; ∃-syntax)
open TypingKit ⦃ … ⦄

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

invert-λ : {Γ : Ctx S} →
  Γ ⊢ λx e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    Γ ⊢ (t₁ ⇒ t₂) ⊑ₐ t ×
    Γ ▶ t₁ ⊢ e ∶ t₂ ⋯ᵣ wkn
invert-λ (⊢λ ⊢e) = _ , _ , ⊑ₐ-refl , ⊢e
invert-λ (⊢⊑ ⊢e t₃⊑t) with invert-λ ⊢e
... | t₁ , t₂ , [t₁⇒t₂]⊑t₃ , ⊢e = _ , _ , ⊑ₐ-trans [t₁⇒t₂]⊑t₃ t₃⊑t , ⊢e

-- Not true in general, because the input subtyping could be a faulty
-- assumption instead of an arrow subtyping rule.
-- For this to hold we need to forbid faulty assumptions, or add rules
-- which allow to close faulty assumptions under inversion.
invert-⊑⇒ : {Γ : Ctx S} →
    Γ ⊢ (t₁ ⇒ t₂) ⊑ₐ (t₁' ⇒ t₂') →
    Γ ⊢ t₁' ⊑ₐ t₁ × Γ ⊢ t₂ ⊑ₐ t₂'
invert-⊑⇒ (⊑ₐ-` st₁ x st₂) = {!!}
invert-⊑⇒ (⊑ₐ-⇒ st₁ st₂) = st₁ , st₂

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢λ ⊢e)              (ξ-λ e↪e')  = ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e)              (ξ-Λ e↪e')  = ⊢Λ (subject-reduction ⊢e (ren-pres-↪ wkn e↪e'))
subject-reduction (⊢· ⊢e₁ ⊢e₂)         β-λ         with invert-λ ⊢e₁
...                                                   | t₁ , t₂ , st , ⊢e₁'
                                                      = ⊢⊑ (⊢e₁' ⊢⋯ₛ ⊢⦅ ⊢⊑ ⊢e₂ {!!} ⦆ₛ) {!!}
subject-reduction (⊢· ⊢e₁ ⊢e₂)         (ξ-·₁ e↪e') = ⊢· (subject-reduction ⊢e₁ e↪e') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)         (ξ-·₂ e↪e') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e↪e')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e) β-Λ         = {!!}
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e) (ξ-∙₁ e↪e') = ⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (subject-reduction ⊢e e↪e')
subject-reduction (⊢⊑ ⊢e t⊑t')         e↪e'        = ⊢⊑ (subject-reduction ⊢e e↪e') t⊑t'

-- subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (⊢Λ ⊢e₁))    β-Λ          = {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ!}






