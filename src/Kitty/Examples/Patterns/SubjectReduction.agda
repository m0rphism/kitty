module Kitty.Examples.Patterns.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; module ≡-Reasoning)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open ≡-Reasoning
open import Kitty.Examples.Patterns.Definitions
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Typing.Typing compose-traversal ctx-repr

-- For functional typing contexts, we need to prove that
-- typing respects extensional equality.
-- This can be reduced to a one liner if one assumes functional
-- extensionality.
≡ᶜ-cong-⊢ : ∀ {Γ₁ Γ₂ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → 
  Γ₁ ≡ᶜ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ e ∶ t
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-` {x = x} ∋x)               = ⊢-` (≡ᶜ-cong-∋ x Γ₁≡Γ₂ ∋x)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-λ ⊢e)                       = ⊢-λ (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶ Γ₁≡Γ₂ refl) ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-· ⊢e₁ ⊢e₂)                  = ⊢-· (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-tt                           = ⊢-tt
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-, ⊢e₁ ⊢e₂)                  = ⊢-, (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₁ ⊢e)                    = ⊢-inj₁ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₂ ⊢e)                    = ⊢-inj₂ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-match ⊢e ⊢cs ex)            = ⊢-match (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢e) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢cs) ex
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-clause {P = P} ⊢p ⊢e)       = ⊢-clause (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)
                                                          (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶▶ {Γ₁' = PatTy→Ctx' P} Γ₁≡Γ₂ ≡ᶜ-refl) ⊢e)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-clause-[]                    = ⊢-clause-[]
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-clause-∷ ⊢c ⊢cs)            = ⊢-clause-∷ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢c) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢cs)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-ttᵖ                          = ⊢-ttᵖ
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-`ᵖ                           = ⊢-`ᵖ
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-,ᵖ {P₁ = P₁} ⊢p₁ ⊢p₂)       = ⊢-,ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p₁) (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶▶ {Γ₁' = PatTy→Ctx' P₁} Γ₁≡Γ₂ ≡ᶜ-refl) ⊢p₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₁ᵖ ⊢p)                   = ⊢-inj₁ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₂ᵖ ⊢p)                   = ⊢-inj₂ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)

typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢-`; ≡ᶜ-cong-⊢ = ≡ᶜ-cong-⊢ }

open Typing typing hiding (_⊢_∶_; ⊢`; ≡ᶜ-cong-⊢)
open import Kitty.Typing.TypingKit compose-traversal ctx-repr typing
open TypingKit ⦃ … ⦄

open import Kitty.Term.MultiSub terms using (_↑*'_; ↑*'~↑*)
mutual
  _⊢⋯_ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ TK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
      {S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
    Γ₁ ⊢ e ∶ t →
    Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
    Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
  ⊢-` ∋x               ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
  ⊢-λ {t₂ = t₂} ⊢e     ⊢⋯ ⊢ϕ = ⊢-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
  ⊢-· ⊢e₁ ⊢e₂          ⊢⋯ ⊢ϕ = ⊢-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
  ⊢-tt                 ⊢⋯ ⊢ϕ = ⊢-tt
  ⊢-, ⊢e₁ ⊢e₂          ⊢⋯ ⊢ϕ = ⊢-, (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
  ⊢-inj₁ ⊢e            ⊢⋯ ⊢ϕ = ⊢-inj₁ (⊢e ⊢⋯ ⊢ϕ)
  ⊢-inj₂ ⊢e            ⊢⋯ ⊢ϕ = ⊢-inj₂ (⊢e ⊢⋯ ⊢ϕ)
  ⊢-match ⊢e₁ ⊢cs ex   ⊢⋯ ⊢ϕ = ⊢-match (⊢e₁ ⊢⋯ ⊢ϕ) (⊢cs ⊢⋯ ⊢ϕ) (Ex⋯ ex)
  _⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢-clause {S' = S'} {P = P} {e = e} {t' = t'} ⊢p ⊢e) ⊢ϕ =
    ⊢-clause (⊢p ⊢⋯ ⊢ϕ)
      (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶▶ (≡ᶜ-refl {Γ = Γ₂}) (PatTy→Ctx'-⋯ P (ϕ ↑* _)))
        (subst₂ ((Γ₂ ▶▶ (PatTy→Ctx' P ⋯Ctx' ϕ)) ⊢_∶_)
          (e ⋯ ϕ ↑* S' ≡⟨ ~-cong-⋯ e (~-sym {f = ϕ ↑*' S'} {g = ϕ ↑* S'} (↑*'~↑* S')) ⟩
            e ⋯ ϕ ↑*' S' ∎)
          (t' ⋯ᵣ wkₖ* S' id ⋯ ϕ ↑* S' ≡⟨ dist-↑*-f t' ϕ ⟩
           t' ⋯ ϕ ⋯ᵣ wkₖ* S' id       ∎)
          (⊢e ⊢⋯ (⊢ϕ ∋↑*/⊢↑* _))))
  ⊢-clause-[]          ⊢⋯ ⊢ϕ = ⊢-clause-[]
  ⊢-clause-∷ ⊢c ⊢cs    ⊢⋯ ⊢ϕ = ⊢-clause-∷ (⊢c ⊢⋯ ⊢ϕ) (⊢cs ⊢⋯ ⊢ϕ)
  ⊢-ttᵖ                ⊢⋯ ⊢ϕ = ⊢-ttᵖ
  ⊢-`ᵖ                 ⊢⋯ ⊢ϕ = ⊢-`ᵖ
  _⊢⋯_ {S₁ = S₁} {S₂ = S₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} (⊢-,ᵖ {S₁ = S₃} {p₁ = p₁} {P₁ = P₁} {p₂ = p₂} {P₂ = P₂} ⊢p₁ ⊢p₂) ⊢ϕ =
    Γ₂ ⊢ (p₁ ,ᵖ p₂) ⋯ ϕ ∶ (P₁ ▶▶ᵖ P₂) ⋯ ϕ
      by subst₂ (Γ₂ ⊢_∶_)

        ((p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑* S₃)  ≡⟨ cong ((p₁ ⋯ ϕ) ,ᵖ_)
                                             (~-cong-⋯ p₂ (~-sym {f = ϕ ↑*' S₃} {g = ϕ ↑* S₃} (↑*'~↑* S₃))) ⟩
         (p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑*' S₃) ≡⟨⟩
         (p₁ ,ᵖ p₂) ⋯ ϕ              ∎)

        ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* S₃) ≡⟨ ▶▶ᵖ⋯ P₁ P₂ ϕ ⟩
         (P₁ ▶▶ᵖ P₂) ⋯ ϕ             ∎)

        (
    Γ₂ ⊢ ((p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑* S₃)) ∶ ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* S₃))
      by ⊢-,ᵖ (⊢p₁ ⊢⋯ ⊢ϕ)
              (⊢p₂ ⊢⋯ ≡ᶜ-cong-∋*/⊢* (≡ᶜ-cong-▶▶ (≡ᶜ-refl {Γ = Γ₂}) (PatTy→Ctx'-⋯ P₁ ϕ)) (⊢ϕ ∋↑*/⊢↑* PatTy→Ctx' P₁))
    )
  ⊢-inj₁ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₁ᵖ (⊢p ⊢⋯ ⊢ϕ)
  ⊢-inj₂ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₂ᵖ (⊢p ⊢⋯ ⊢ϕ)

  open import Data.List.Properties using (++-assoc)
  open import Kitty.Util.SubstProperties
  ▶▶ᵖ⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
      {S₁ S₂ S₃ S₁'} (P₁ : S₁ ⊢ ℙ S₂) (P₂ : (S₁ ▷▷ S₂) ⊢ ℙ S₃) (ϕ : S₁ –[ 𝕂 ]→ S₁') →
    (P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* S₂) ≡ (P₁ ▶▶ᵖ P₂) ⋯ ϕ
  ▶▶ᵖ⋯ {S₁ = S₁} {S₂} {.[]}      {S₁'} P₁ []ᵖ       ϕ = refl
  ▶▶ᵖ⋯ {S₁ = S₁} {S₂} {S₃ ▷ 𝕖}   {S₁'} P₁ (P₂ ▶ᵖ t) ϕ =
    let sub = subst (_⊢ 𝕥) (sym (++-assoc S₃ S₂ S₁)) in
    let sub' = subst (_⊢ 𝕥) (sym (++-assoc S₃ S₂ S₁')) in
    let sub'⁻¹ = subst (_⊢ 𝕥) (++-assoc S₃ S₂ S₁') in
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ▶ᵖ t) ⋯ ϕ ↑* S₂)                           ≡⟨ cong ((P₁ ⋯ ϕ) ▶▶ᵖ_)
                                                                         (~-cong-⋯ (P₂ ▶ᵖ t) (~-sym {f = ϕ ↑*' S₂}
                                                                                                    {g = ϕ ↑* S₂}
                                                                                                    (↑*'~↑* S₂))) ⟩
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ▶ᵖ t) ⋯ ϕ ↑*' S₂)                          ≡⟨⟩
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ⋯ ϕ ↑*' S₂) ▶ᵖ (t ⋯ ϕ ↑*' S₂ ↑*' S₃))      ≡⟨⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' S₂)) ▶ᵖ sub' (t ⋯ ϕ ↑*' S₂ ↑*' S₃) ≡⟨ cong (λ ■ → ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' S₂)) ▶ᵖ sub' ■)
         (t ⋯ ϕ ↑*' S₂ ↑*' S₃              ≡⟨ ~-cong-⋯ t (↑*'~↑* {ϕ = ϕ ↑*' S₂} S₃) ⟩
          t ⋯ ϕ ↑*' S₂ ↑* S₃               ≡⟨ ~-cong-⋯ t (~-cong-↑* {S = S₃} (↑*'~↑* {ϕ = ϕ} S₂)) ⟩
          t ⋯ ϕ ↑* S₂ ↑* S₃                ≡⟨ ⋯-↑*-▷▷ S₂ S₃ t ϕ ⟩
          sub'⁻¹ (sub t ⋯ ϕ ↑* (S₂ ▷▷ S₃)) ≡⟨ cong sub'⁻¹ (~-cong-⋯ (sub t) (~-sym {f = ϕ ↑*' (S₂ ▷▷ S₃)} {g = ϕ ↑* (S₂ ▷▷ S₃)} (↑*'~↑* (S₂ ▷▷ S₃)))) ⟩
          sub'⁻¹ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃)) ∎)
       ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' S₂)) ▶ᵖ sub' (sub'⁻¹ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃)))
                                                                 ≡⟨ cong (((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' S₂)) ▶ᵖ_)
                                                                      (cancel-subst (_⊢ 𝕥) (++-assoc S₃ S₂ S₁') _) ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' S₂)) ▶ᵖ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃)) ≡⟨ cong (λ ■ → ((P₁ ⋯ ϕ) ▶▶ᵖ ■) ▶ᵖ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃)))
                                                                         (~-cong-⋯ P₂ (↑*'~↑* S₂)) ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* S₂)) ▶ᵖ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃))  ≡⟨ cong (_▶ᵖ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃)))
                                                                         (▶▶ᵖ⋯ P₁ P₂ ϕ) ⟩
    ((P₁ ▶▶ᵖ P₂) ⋯ ϕ) ▶ᵖ (sub t ⋯ ϕ ↑*' (S₂ ▷▷ S₃))              ≡⟨⟩
    ((P₁ ▶▶ᵖ P₂) ▶ᵖ sub t) ⋯ ϕ                                   ≡⟨⟩
    (P₁ ▶▶ᵖ (P₂ ▶ᵖ t)) ⋯ ϕ                                       ∎

  open import Kitty.Util.List
  open import Data.List.Relation.Unary.Any using (here; there)
  PatTy→Ctx'-⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
      {S₁ S₂ S'} (P : S₁ ⊢ ℙ S') (ϕ : S₁ –[ 𝕂 ]→ S₂) →
    (PatTy→Ctx' P) ⋯Ctx' ϕ ≡ᶜ PatTy→Ctx' (P ⋯ ϕ)
  PatTy→Ctx'-⋯ []ᵖ        ϕ _ ()
  PatTy→Ctx'-⋯ {S' = S' ▷ m'} (P₁ ▶ᵖ P₂) ϕ m x@(here refl) =
    (PatTy→Ctx' (P₁ ▶ᵖ P₂) ⋯Ctx' ϕ) m x ≡⟨⟩
    P₂ ⋯ (ϕ ↑* S')                      ≡⟨ ~-cong-⋯ P₂ (~-sym {f = ϕ ↑*' S'} {g = ϕ ↑* S'} (↑*'~↑* S')) ⟩
    P₂ ⋯ (ϕ ↑*' S')                     ≡⟨ refl ⟩
    (PatTy→Ctx' ((P₁ ▶ᵖ P₂) ⋯ ϕ)) m x   ∎
  PatTy→Ctx'-⋯ {S' = S' ▷ m'} (P₁ ▶ᵖ P₂) ϕ m x@(there y) =
    (PatTy→Ctx' (P₁ ▶ᵖ P₂) ⋯Ctx' ϕ) m x                   ≡⟨⟩
    PatTy→Ctx' P₁ m y ⋯ (ϕ ↑* drop-∈ x (S' ▷ m'))         ≡⟨⟩
    (PatTy→Ctx' P₁ ⋯Ctx' ϕ ▶' (P₂ ⋯ (ϕ ↑*' _))) m x       ≡⟨ ≡ᶜ-cong-▶' {t₁ = P₂ ⋯ (ϕ ↑*' _)} (PatTy→Ctx'-⋯ P₁ ϕ) refl m x ⟩
    (PatTy→Ctx' (P₁ ⋯ ϕ) ▶' (P₂ ⋯ (ϕ ↑*' _))) m x         ≡⟨⟩
    (PatTy→Ctx' ((P₁ ▶ᵖ P₂) ⋯ ϕ)) m x                     ∎

  Can⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
      {e : S ⊢ 𝕖} {t : S₁ ⊢ 𝕥} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
    Canonical e (t ⋯ ϕ) →
    Canonical e t
  Can⋯ {e = .(λx _)}   {t₁ `→ t₂} {ϕ} C-λ             = C-λ
  Can⋯ {e = .tt}       {𝟙}        {ϕ} C-tt            = C-tt
  Can⋯ {e = .(_ , _)}  {t₁ `× t₂} {ϕ} (C-, can₁ can₂) = C-, (Can⋯ can₁) (Can⋯ can₂)
  Can⋯ {e = .(inj₁ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₁ can)    = C-inj₁ (Can⋯ can)
  Can⋯ {e = .(inj₂ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₂ can)    = C-inj₂ (Can⋯ can)

  Matches⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
      {e : S₁ ⊢ 𝕖} {p : S₂ ⊢ 𝕡 S'} (ϕ : S₂ –[ 𝕂 ]→ S₃) →
    Matches e p →
    Matches e (p ⋯ ϕ)
  Matches⋯ ϕ M-`         = M-`
  Matches⋯ ϕ M-tt        = M-tt
  Matches⋯ ϕ (M-, m₁ m₂) = M-, (Matches⋯ ϕ m₁) (Matches⋯ (ϕ ↑*' _) m₂)
  Matches⋯ ϕ (M-inj₁ m)  = M-inj₁ (Matches⋯ ϕ m)
  Matches⋯ ϕ (M-inj₂ m)  = M-inj₂ (Matches⋯ ϕ m)

  ∈cs-⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
    {c : S₁ ⊢ 𝕔} {cs : S₁ ⊢ 𝕔𝕤} (ϕ : S₁ –[ 𝕂 ]→ S₂) →
    c ∈cs cs →
    (c ⋯ ϕ) ∈cs (cs ⋯ ϕ)
  ∈cs-⋯ ϕ (here refl) = here refl
  ∈cs-⋯ ϕ (there x) = there (∈cs-⋯ ϕ x)

  Ex⋯ :
      ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄
        ⦃ C₁ : ComposeKit 𝕂 Kᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
        ⦃ IK : TypingKit 𝕂 K C₁ C₂ ⦄
        ⦃ C₃ : ComposeKit Kₛ 𝕂 Kₛ ⦄
        ⦃ C₄ : ComposeKit 𝕂 Kₛ Kₛ ⦄
        {cs : S₁ ⊢ 𝕔𝕤} {t : S₁ ⊢ 𝕥} {ϕ : S₁ –[ 𝕂 ]→ S₂} →
    Exhaustive cs t →
    Exhaustive (cs ⋯ ϕ) (t ⋯ ϕ)
  Ex⋯ {cs = cs} {t} {ϕ} ex {e = e} can with ex (Can⋯ {e = e} {t = t} {ϕ = ϕ} can)
  ... | S'' , p , e' , c∈cs , m =
    S'' , p ⋯ ϕ , e' ⋯ (ϕ ↑*' S'') , ∈cs-⋯ ϕ c∈cs , Matches⋯ ϕ m

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

⊢cs→⊢c : ∀ {c : S ⊢ 𝕔} {cs : S ⊢ 𝕔𝕤} {t₁ t₂ : S ⊢ 𝕥} →
  c ∈cs cs →
  Γ ⊢ cs ∶ Clause t₁ t₂ →
  Γ ⊢ c  ∶ Clause t₁ t₂
⊢cs→⊢c (here refl) (⊢-clause-∷ ⊢c ⊢cs) = ⊢c
⊢cs→⊢c (there x)   (⊢-clause-∷ ⊢c ⊢cs) = ⊢cs→⊢c x ⊢cs

-- ⊢matching-sub : ∀ {S S'} {Γ : Ctx S} {e : S ⊢ 𝕖} {t : S ⊢ 𝕥} {p : S ⊢ 𝕡 S'} {P : S ⊢ ℙ S'} →
--   (m : Matches e p) →
--   Γ ⊢ e ∶ t →
--   Γ ⊢ p ∶ P →
--   Γ ⊢* matching-sub m ∶ PatTy→Ctx' P via idₛ
-- ⊢matching-sub = {!!}

⊢matching-sub : ∀ {S S'} {Γ : Ctx S} {e : S ⊢ 𝕖} {t : S ⊢ 𝕥} {p : S ⊢ 𝕡 S'} {P : S ⊢ ℙ S'} →
  (m : Matches e p) →
  Γ ⊢ e ∶ t →
  Γ ⊢ p ∶ P →
  Γ ⊢* (idₛ ∥ₛ matching-sub m) ∶ (Γ ▶▶ PatTy→Ctx' P)
⊢matching-sub m ⊢e ⊢p = {!!}

-- PatTy→Ctx' P             : CtxP' S S'
-- matching-sub m           : S' →ₛ S
-- wkₖ* S' (matching-sub m) : S' →ₛ (S ▷▷ S')
-- idₛ ∥ₛ (matching-sub m)  : (S ▷▷ S') →ₛ S

-- semantics applies  e' ⋯ₛ (idₛ ∥ₛ matching-sub m)  where  {e' : S ▷▷ S' ⊢ 𝕖}
-- so we need  idₛ ∥ₛ matching-sub m  ∶  Γ₁ ▶▶ Γ₁'  ⇒ₖ  Γ₁

-- Goal for  Γ ⊢* matching-sub m ∶ ?  is  Ctx S'

-- Γ ⊢* (idₛ ∥ₛ matching-sub m) ∶ {!PatTy→Ctx' P!}
-- Goal: (s : Sort Var)
--       (x : (S' ++ S) ∋ s) →
--       (drop (suc (depth x)) (S' ++ S) ++ []) ∶⊢ s
-- Have: (s : Sort Var)
--       (x : S' ∋ s) →
--       (drop (suc (depth x)) S' ++ S) ∶⊢ s

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢-· {t₂ = t₂} (⊢-λ ⊢e₁) ⊢e₂) β-λ                   = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction {Γ = Γ} (⊢-match ⊢e ⊢cs ex)           (β-match {e' = e'} c∈cs m refl) with ⊢cs→⊢c c∈cs ⊢cs
...                                                                   | ⊢-clause ⊢p ⊢e'
                                                                      =
  subst (Γ ⊢ e' ⋯ (idₛ ∥ₛ matching-sub m) ∶_)
        {!!}
        (⊢e' ⊢⋯ ⊢matching-sub m ⊢e ⊢p)
subject-reduction (⊢-λ ⊢e)                      (ξ-λ e↪e')            = ⊢-λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁')         = ⊢-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂')         = ⊢-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction {Γ = Γ} (⊢-match ⊢e ⊢cs ex)   (ξ-match e↪e')        = ⊢-match (subject-reduction ⊢e e↪e') ⊢cs ex
