module Kitty.Examples.SystemFSub-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Kitty.Examples.SystemFSub-Derive.Definitions
open import Kitty.Typing.TypingKit compose-traversal ctx-repr
  record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢`; ≡ᶜ-cong-⊢ = λ { refl ⊢e → ⊢e } }
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open TypingKit ⦃ … ⦄
open import Function using () renaming (_∋_ to _by_)

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

λx-injective : ∀ {e₁ e₂ : S ▷ 𝕖 ⊢ 𝕖} → (S ⊢ 𝕖 by λx e₁) ≡ (λx e₂) → e₁ ≡ e₂
λx-injective refl = refl

-- TODO: General case for kitty library:
-- If (_& ϕ) is injective, then (_⋯ ϕ) is injective, too!
wkn-injective : ∀ (e₁ e₂ : S ⊢ s) s' →
  e₁ ⋯ᵣ wkn {s = s'} ≡ e₂ ⋯ᵣ wkn {s = s'} →
  e₁ ≡ e₂
wkn-injective (` x) (` .(id _ x)) s' refl = refl
wkn-injective (λx e₁) (λx e₂) s' eq = cong λx_ (wkn-injective e₁ e₂ s' {!λx-injective eq!})
wkn-injective (Λα e₁) (Λα e₂) s' eq = {!!}
wkn-injective (∀[α⊑ e₁ ] e₂) (∀[α⊑ e₃ ] e₄) s' eq = {!!}
wkn-injective (e₁ · e₂) (e₃ · e₄) s' eq = {!!}
wkn-injective (e₁ ∙ e₂) (e₃ ∙ e₄) s' eq = {!!}
wkn-injective (e₁ ⇒ e₂) (e₃ ⇒ e₄) s' eq = {!!}
wkn-injective `tt `tt s' eq = {!!}
wkn-injective 𝟙 𝟙 s' eq = {!!}
wkn-injective (e₁ ∶⊑ e₂) (e₃ ∶⊑ e₄) s' eq = {!!}
wkn-injective ★ ★ s' eq = {!!}
wkn-injective Cstr Cstr s' eq = {!!}


entail : ∀ {Γ : Ctx S} {t₁ t₂ : S ⊢ 𝕥} {t : S ⊢ 𝕥} {e : S ⊢ 𝕖} →
  Γ ▶ (t₁ ∶⊑ t₂) ⊢ (e ⋯ᵣ wkn {s = 𝕔}) ∶ (t ⋯ᵣ wkn {s = 𝕔}) →
  Γ ⊢ t₁ ⊑ₐ t₂ →
  Γ ⊢ e ∶ t
entail {t = t} {e = e} ⊢e t₁⊑t₂
 with #e ← e ⋯ᵣ wkn {s = 𝕔} in eq-e | #t ← t ⋯ᵣ wkn {s = 𝕔} in eq-t
 with ⊢e | e | t | eq-e | eq-t
... | ⊢` x              | e | t | eq-e | refl = {!!}
... | ⊢λ ⊢e₁            | e | t | eq-e | eq-t = {!!}
... | ⊢Λ ⊢e₁            | e | t | eq-e | eq-t = {!!}
... | ⊢· ⊢e₁ ⊢e₂        | e | t | eq-e | refl = {!!}
... | ⊢∙ ⊢e₁ ⊢e₂ st ⊢e₃ | e | t | eq-e | eq-t = {!!}
... | ⊢tt               | `tt | 𝟙 | refl | refl = ⊢tt
... | ⊢⊑ ⊢e st          | e | t | refl | refl = ⊢⊑ (entail {!⊢e!} {!st!}) {!!}

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
 with ⊢Γ x (wk-telescope Γ x ≡⟨ wkn-injective _ _ _ ∋x ⟩ (t₁ ∶⊑ t₂) ∎)
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

invert-⊑` : ∀ {Γ : Ctx S} {α : S ∋ 𝕥} →
  Valid Γ →
  Γ ⊢ t ⊑ₐ (` α) →
  ∃[ β ] t ≡ ` β
invert-⊑` ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂)
 with ⊢Γ c ∋c
... | y , refl
 with invert-⊑` ⊢Γ st₁
... | β₂ , refl
 = β₂ , refl
invert-⊑` ⊢Γ ⊑ₐ-refl-var = _ , refl

-- Not true in general, because the input subtyping could be a faulty
-- assumption instead of an arrow subtyping rule.
-- For this to hold we need to forbid faulty assumptions, or add rules
-- which allow to close faulty assumptions under inversion.
invert-⊑⇒ : {Γ : Ctx S} →
  Valid Γ →
  Γ ⊢ (t₁ ⇒ t₂) ⊑ₐ (t₁' ⇒ t₂') →
  Γ ⊢ t₁' ⊑ₐ t₁ × Γ ⊢ t₂ ⊑ₐ t₂'
invert-⊑⇒ ⊢Γ (⊑ₐ-` st₁ x st₂) = {!!}
invert-⊑⇒ ⊢Γ (⊑ₐ-⇒ st₁ st₂) = st₁ , st₂

invert-⊑∀ : {Γ : Ctx S} {t₁ t₁' : S ⊢ 𝕥} {t₂ t₂' : S ▷ 𝕥 ⊢ 𝕥} →
  Valid Γ →
  Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ₐ (∀[α⊑ t₁' ] t₂') →
  Γ ▶ ★ ⊢ t₂ ⊑ₐ t₂'
invert-⊑∀ ⊢Γ (⊑ₐ-∀ st₂) = st₂
invert-⊑∀ ⊢Γ (⊑ₐ-` {c = ` c} st₁ (⊢` ∋c) st₂)
 with ⊢Γ c ∋c
... | y , refl
 with invert-⊑` ⊢Γ st₁
... | β , ()

subject-reduction :
  Valid Γ →
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction ⊢Γ (⊢λ ⊢e)                (ξ-λ e↪e')  = ⊢λ (subject-reduction (Valid-▶ ⊢Γ _) ⊢e e↪e')
subject-reduction ⊢Γ (⊢Λ ⊢e)                (ξ-Λ e↪e')  = ⊢Λ (subject-reduction (Valid-▶ (Valid-▶ ⊢Γ ★) _)
                                                                                ⊢e (ren-pres-↪ wkn e↪e'))
subject-reduction ⊢Γ (⊢· {e₂ = e₂} ⊢e₁ ⊢e₂) β-λ      with invert-λ ⊢e₁
...                                                     | t₁ , t₂ , st , ⊢e₁'
                                                     with invert-⊑⇒ ⊢Γ st
...                                                     | st₁ , st₂
                                                        = let st₂' = subst (_ ⊢_⊑ₐ _) (
                                                                       t₂                   ≡⟨ sym (wk-cancels-⦅⦆ t₂ e₂) ⟩
                                                                       t₂ ⋯ᵣ wkn ⋯ ⦅ e₂ ⦆'ₛ ∎
                                                                     ) st₂ in
                                                          ⊢⊑ (⊢e₁' ⊢⋯ₛ ⊢⦅ ⊢⊑ ⊢e₂ st₁ ⦆ₛ) st₂'
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)           (ξ-·₁ e↪e') = ⊢· (subject-reduction ⊢Γ ⊢e₁ e↪e') ⊢e₂
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)           (ξ-·₂ e↪e') = ⊢· ⊢e₁ (subject-reduction ⊢Γ ⊢e₂ e↪e')
subject-reduction {Γ = Γ} ⊢Γ (⊢∙ {t₁ = t₁} {t₂ = t₂} {e₁ = Λα e₁} ⊢t₁ ⊢t₂ t₂⊑t ⊢e)   β-Λ         = {!!}
-- subject-reduction {Γ = Γ} (⊢∙ {t₁ = t₁} {t₂ = t₂} {e₁ = Λα e₁} ⊢t₁ ⊢t₂ t₂⊑t ⊢e)   β-Λ         with invert-Λ ⊢e
-- ...                                                     | t₁' , t₂' , st , ⊢e'
--                                                      with invert-⊑∀ st
-- ...                                                     | st₂
--                                                         = let ⊢' = subst₂ (Γ ⊢_∶_)
--                                                                           (e₁ ⋯ᵣ wkn ⋯ {!⦅ t₂ ⋯ᵣ wkn ⦆'ₛ ↑ _!} ≡⟨ {!!} ⟩
--                                                                            e₁ ⋯ ⦅ t₂ ⦆'ₛ    ∎)
--                                                                           (t₂' ⋯ᵣ wkn ⋯ {!⦅ t₂ ⋯ᵣ wkn ⦆'ₛ!} ≡⟨ {!!} ⟩
--                                                                            t₂' ⋯ ⦅ t₂ ⦆'ₛ    ∎)
--                                                                           (⊢e' ⊢⋯ₛ ⊢⦅ t₂ ⦆) in
--                                                           ⊢⊑ ⊢' (st₂ ⊑ₐ⋯ ⊢⦅ ⊢t₂ ⦆ₛ)
subject-reduction ⊢Γ (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t ⊢e)   (ξ-∙₁ e↪e') = ⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (subject-reduction ⊢Γ ⊢e e↪e')
subject-reduction ⊢Γ (⊢⊑ ⊢e t⊑t')           e↪e'        = ⊢⊑ (subject-reduction ⊢Γ  ⊢e e↪e') t⊑t'

-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ t₂⊑t (⊢Λ ⊢e₁))    β-Λ          = {!⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ!}






