module Kitty.Examples.STLC-Pat.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; module ≡-Reasoning)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open ≡-Reasoning
open import Kitty.Examples.STLC-Pat.Definitions
open import Function using () renaming (_∋_ to _by_)

open import Kitty.Typing.ITerms compose-traversal ctx-repr

≡ᶜ-cong-⊢ : ∀ {µ M} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} → 
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

iterms : ITerms
iterms = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢-`; ≡ᶜ-cong-⊢ = ≡ᶜ-cong-⊢ }
open ITerms iterms using (_⊢*_∶_)

open import Kitty.Typing.IKit compose-traversal ctx-repr iterms
  
open IKit ⦃ … ⦄

open import Kitty.Term.MultiSub terms using (_↑*'_; ↑*'~↑*)
mutual
  _⊢⋯_ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {µ₁ µ₂ M} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Γ₁ ⊢ e ∶ t →
    Γ₂ ∋*/⊢*[ IK ] ϕ ∶ Γ₁ →
    Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
  ⊢-` ∋x               ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ∋x)
  ⊢-λ {t₂ = t₂} ⊢e     ⊢⋯ ⊢ϕ = ⊢-λ (subst (_ ⊢ _ ∶_) (dist-↑-f t₂ _) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
  ⊢-· ⊢e₁ ⊢e₂          ⊢⋯ ⊢ϕ = ⊢-· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
  ⊢-tt                 ⊢⋯ ⊢ϕ = ⊢-tt
  ⊢-, ⊢e₁ ⊢e₂          ⊢⋯ ⊢ϕ = ⊢-, (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
  ⊢-inj₁ ⊢e            ⊢⋯ ⊢ϕ = ⊢-inj₁ (⊢e ⊢⋯ ⊢ϕ)
  ⊢-inj₂ ⊢e            ⊢⋯ ⊢ϕ = ⊢-inj₂ (⊢e ⊢⋯ ⊢ϕ)
  ⊢-match ⊢e₁ ⊢cs ex   ⊢⋯ ⊢ϕ = ⊢-match (⊢e₁ ⊢⋯ ⊢ϕ) (⊢cs ⊢⋯ ⊢ϕ) (Ex⋯ ex)
  _⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢-clause {µ' = µ'} {P = P} {e = e} {t' = t'} ⊢p ⊢e) ⊢ϕ =
    ⊢-clause (⊢p ⊢⋯ ⊢ϕ)
      (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶▶ (≡ᶜ-refl {Γ = Γ₂}) (PatTy→Ctx'-⋯ P (ϕ ↑* _)))
        (subst₂ ((Γ₂ ▶▶ (PatTy→Ctx' P ⋯Ctx' ϕ)) ⊢_∶_)
          (e ⋯ ϕ ↑* µ' ≡⟨ ~-cong-⋯ e (~-sym {f = ϕ ↑*' µ'} {g = ϕ ↑* µ'} (↑*'~↑* µ')) ⟩
            e ⋯ ϕ ↑*' µ' ∎)
          (wk* µ' t' ⋯ ϕ ↑* µ'        ≡⟨ cong (_⋯ ϕ ↑* µ') (wk*-wkₖ* t' µ') ⟩
           t' ⋯ᵣ wkₖ* µ' id ⋯ ϕ ↑* µ' ≡⟨ dist-↑*-f t' ϕ ⟩
           t' ⋯ ϕ ⋯ᵣ wkₖ* µ' id       ≡⟨ sym (wk*-wkₖ* (t' ⋯ ϕ) µ') ⟩
           wk* µ' (t' ⋯ ϕ)            ∎)
          (⊢e ⊢⋯ (⊢ϕ ∋↑*/⊢↑* _))))
  ⊢-clause-[]          ⊢⋯ ⊢ϕ = ⊢-clause-[]
  ⊢-clause-∷ ⊢c ⊢cs    ⊢⋯ ⊢ϕ = ⊢-clause-∷ (⊢c ⊢⋯ ⊢ϕ) (⊢cs ⊢⋯ ⊢ϕ)
  ⊢-ttᵖ                ⊢⋯ ⊢ϕ = ⊢-ttᵖ
  ⊢-`ᵖ                 ⊢⋯ ⊢ϕ = ⊢-`ᵖ
  _⊢⋯_ {µ₁} {µ₂} {_} {Γ₁} {Γ₂} {_} {_} {ϕ} (⊢-,ᵖ {µ₁ = µ₃} {p₁ = p₁} {P₁ = P₁} {p₂ = p₂} {P₂ = P₂} ⊢p₁ ⊢p₂) ⊢ϕ =
    Γ₂ ⊢ (p₁ ,ᵖ p₂) ⋯ ϕ ∶ (P₁ ▶▶ᵖ P₂) ⋯ ϕ
      by subst₂ (Γ₂ ⊢_∶_)

        ((p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑* µ₃)  ≡⟨ cong ((p₁ ⋯ ϕ) ,ᵖ_)
                                             (~-cong-⋯ p₂ (~-sym {f = ϕ ↑*' µ₃} {g = ϕ ↑* µ₃} (↑*'~↑* µ₃))) ⟩
         (p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑*' µ₃) ≡⟨⟩
         (p₁ ,ᵖ p₂) ⋯ ϕ              ∎)

        ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* µ₃) ≡⟨ ▶▶ᵖ⋯ P₁ P₂ ϕ ⟩
         (P₁ ▶▶ᵖ P₂) ⋯ ϕ             ∎)

        (
    Γ₂ ⊢ ((p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ ↑* µ₃)) ∶ ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* µ₃))
      by ⊢-,ᵖ (⊢p₁ ⊢⋯ ⊢ϕ)
              (⊢p₂ ⊢⋯ ≡ᶜ-cong-∋*/⊢* (≡ᶜ-cong-▶▶ (≡ᶜ-refl {Γ = Γ₂}) (PatTy→Ctx'-⋯ P₁ ϕ)) (⊢ϕ ∋↑*/⊢↑* PatTy→Ctx' P₁))
    )
  ⊢-inj₁ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₁ᵖ (⊢p ⊢⋯ ⊢ϕ)
  ⊢-inj₂ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₂ᵖ (⊢p ⊢⋯ ⊢ϕ)

  open import Data.List.Properties using (++-assoc)
  open import Kitty.Util.SubstProperties
  ▶▶ᵖ⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {µ₁ µ₂ µ₃ µ₁'} (P₁ : µ₁ ⊢ ℙ µ₂) (P₂ : (µ₁ ▷▷ µ₂) ⊢ ℙ µ₃) (ϕ : µ₁ –[ 𝕂 ]→ µ₁') →
    (P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* µ₂) ≡ (P₁ ▶▶ᵖ P₂) ⋯ ϕ
  ▶▶ᵖ⋯ {µ₁ = µ₁} {µ₂} {µ₃}       {µ₁'} P₁ (`[_]_ {m = 𝕖} () x) ϕ
  ▶▶ᵖ⋯ {µ₁ = µ₁} {µ₂} {.[]}      {µ₁'} P₁ []ᵖ       ϕ = refl
  ▶▶ᵖ⋯ {µ₁ = µ₁} {µ₂} {µ₃ ▷ 𝕖}   {µ₁'} P₁ (P₂ ▶ᵖ t) ϕ =
    let sub = subst (_⊢ 𝕥) (sym (++-assoc µ₃ µ₂ µ₁)) in
    let sub' = subst (_⊢ 𝕥) (sym (++-assoc µ₃ µ₂ µ₁')) in
    let sub'⁻¹ = subst (_⊢ 𝕥) (++-assoc µ₃ µ₂ µ₁') in
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ▶ᵖ t) ⋯ ϕ ↑* µ₂)                           ≡⟨ cong ((P₁ ⋯ ϕ) ▶▶ᵖ_)
                                                                         (~-cong-⋯ (P₂ ▶ᵖ t) (~-sym {f = ϕ ↑*' µ₂}
                                                                                                    {g = ϕ ↑* µ₂}
                                                                                                    (↑*'~↑* µ₂))) ⟩
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ▶ᵖ t) ⋯ ϕ ↑*' µ₂)                          ≡⟨⟩
    (P₁ ⋯ ϕ) ▶▶ᵖ ((P₂ ⋯ ϕ ↑*' µ₂) ▶ᵖ (t ⋯ ϕ ↑*' µ₂ ↑*' µ₃))      ≡⟨⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' µ₂)) ▶ᵖ sub' (t ⋯ ϕ ↑*' µ₂ ↑*' µ₃) ≡⟨ cong (λ ■ → ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' µ₂)) ▶ᵖ sub' ■)
         (t ⋯ ϕ ↑*' µ₂ ↑*' µ₃              ≡⟨ ~-cong-⋯ t (↑*'~↑* {ϕ = ϕ ↑*' µ₂} µ₃) ⟩
          t ⋯ ϕ ↑*' µ₂ ↑* µ₃               ≡⟨ ~-cong-⋯ t (~-cong-↑* {µ = µ₃} (↑*'~↑* {ϕ = ϕ} µ₂)) ⟩
          t ⋯ ϕ ↑* µ₂ ↑* µ₃                ≡⟨ ⋯-↑*-▷▷ µ₂ µ₃ t ϕ ⟩
          sub'⁻¹ (sub t ⋯ ϕ ↑* (µ₂ ▷▷ µ₃)) ≡⟨ cong sub'⁻¹ (~-cong-⋯ (sub t) (~-sym {f = ϕ ↑*' (µ₂ ▷▷ µ₃)} {g = ϕ ↑* (µ₂ ▷▷ µ₃)} (↑*'~↑* (µ₂ ▷▷ µ₃)))) ⟩
          sub'⁻¹ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃)) ∎)
       ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' µ₂)) ▶ᵖ sub' (sub'⁻¹ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃)))
                                                                 ≡⟨ cong (((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' µ₂)) ▶ᵖ_)
                                                                      (cancel-subst (_⊢ 𝕥) (++-assoc µ₃ µ₂ µ₁') _) ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑*' µ₂)) ▶ᵖ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃)) ≡⟨ cong (λ ■ → ((P₁ ⋯ ϕ) ▶▶ᵖ ■) ▶ᵖ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃)))
                                                                         (~-cong-⋯ P₂ (↑*'~↑* µ₂)) ⟩
    ((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ ↑* µ₂)) ▶ᵖ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃))  ≡⟨ cong (_▶ᵖ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃)))
                                                                         (▶▶ᵖ⋯ P₁ P₂ ϕ) ⟩
    ((P₁ ▶▶ᵖ P₂) ⋯ ϕ) ▶ᵖ (sub t ⋯ ϕ ↑*' (µ₂ ▷▷ µ₃))              ≡⟨⟩
    ((P₁ ▶▶ᵖ P₂) ▶ᵖ sub t) ⋯ ϕ                                   ≡⟨⟩
    (P₁ ▶▶ᵖ (P₂ ▶ᵖ t)) ⋯ ϕ                                       ∎

  open import Kitty.Util.List
  open import Data.List.Relation.Unary.Any using (here; there)
  PatTy→Ctx'-⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {µ₁ µ₂ µ'} (P : µ₁ ⊢ ℙ µ') (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
    (PatTy→Ctx' P) ⋯Ctx' ϕ ≡ᶜ PatTy→Ctx' (P ⋯ ϕ)
  PatTy→Ctx'-⋯ (`[_]_ {m = 𝕖} () _) ϕ
  PatTy→Ctx'-⋯ []ᵖ        ϕ _ ()
  PatTy→Ctx'-⋯ {µ' = µ' ▷ m'} (P₁ ▶ᵖ P₂) ϕ m x@(here refl) =
    (PatTy→Ctx' (P₁ ▶ᵖ P₂) ⋯Ctx' ϕ) m x ≡⟨⟩
    P₂ ⋯ (ϕ ↑* µ')                      ≡⟨ ~-cong-⋯ P₂ (~-sym {f = ϕ ↑*' µ'} {g = ϕ ↑* µ'} (↑*'~↑* µ')) ⟩
    P₂ ⋯ (ϕ ↑*' µ')                     ≡⟨ refl ⟩
    (PatTy→Ctx' ((P₁ ▶ᵖ P₂) ⋯ ϕ)) m x   ∎
  PatTy→Ctx'-⋯ {µ' = µ' ▷ m'} (P₁ ▶ᵖ P₂) ϕ m x@(there y) =
    (PatTy→Ctx' (P₁ ▶ᵖ P₂) ⋯Ctx' ϕ) m x                   ≡⟨⟩
    PatTy→Ctx' P₁ m y ⋯ (ϕ ↑* drop-∈ x (µ' ▷ m'))         ≡⟨⟩
    (PatTy→Ctx' P₁ ⋯Ctx' ϕ ▶' (P₂ ⋯ (ϕ ↑*' _))) m x       ≡⟨ ≡ᶜ-cong-▶' {t₁ = P₂ ⋯ (ϕ ↑*' _)} (PatTy→Ctx'-⋯ P₁ ϕ) refl m x ⟩
    (PatTy→Ctx' (P₁ ⋯ ϕ) ▶' (P₂ ⋯ (ϕ ↑*' _))) m x         ≡⟨⟩
    (PatTy→Ctx' ((P₁ ▶ᵖ P₂) ⋯ ϕ)) m x                     ∎

  -- Can⋯' :
  --   ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
  --     ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
  --     ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
  --     ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
  --     {e : µ ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
  --   Canonical e t →
  --   Canonical e (t ⋯ ϕ)
  -- Can⋯' ϕ C-λ             = C-λ
  -- Can⋯' ϕ C-tt            = C-tt
  -- Can⋯' ϕ (C-, can₁ can₂) = C-, (Can⋯' ϕ can₁) (Can⋯' ϕ can₂)
  -- Can⋯' ϕ (C-inj₁ can)    = C-inj₁ (Can⋯' ϕ can)
  -- Can⋯' ϕ (C-inj₂ can)    = C-inj₂ (Can⋯' ϕ can)

  Can⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {e : µ ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Canonical e (t ⋯ ϕ) →
    Canonical e t
  Can⋯ {e = e}         {`[_]_ {m = 𝕖} () x} {ϕ} can
  Can⋯ {e = .(λx _)}   {t₁ `→ t₂} {ϕ} C-λ             = C-λ
  Can⋯ {e = .tt}       {𝟙}        {ϕ} C-tt            = C-tt
  Can⋯ {e = .(_ , _)}  {t₁ `× t₂} {ϕ} (C-, can₁ can₂) = C-, (Can⋯ can₁) (Can⋯ can₂)
  Can⋯ {e = .(inj₁ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₁ can)    = C-inj₁ (Can⋯ can)
  Can⋯ {e = .(inj₂ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₂ can)    = C-inj₂ (Can⋯ can)

  Matches⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {e : µ₁ ⊢ 𝕖} {p : µ₂ ⊢ 𝕡 µ'} (ϕ : µ₂ –[ 𝕂 ]→ µ₃) →
    Matches e p →
    Matches e (p ⋯ ϕ)
  Matches⋯ ϕ M-`         = M-`
  Matches⋯ ϕ M-tt        = M-tt
  Matches⋯ ϕ (M-, m₁ m₂) = M-, (Matches⋯ ϕ m₁) (Matches⋯ (ϕ ↑*' _) m₂)
  Matches⋯ ϕ (M-inj₁ m)  = M-inj₁ (Matches⋯ ϕ m)
  Matches⋯ ϕ (M-inj₂ m)  = M-inj₂ (Matches⋯ ϕ m)

  -- ∈cs-⋯ :
  --   ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
  --     ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
  --     ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
  --     ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
  --   {p : µ₁ ⊢ 𝕡 µ'} {e : µ₁ ▷▷ µ' ⊢ 𝕖} {cs : µ₁ ⊢ 𝕔𝕤} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
  --   (p ⇒ e) ∈cs cs →
  --   ((p ⋯ ϕ) ⇒ (e ⋯ ϕ ↑* µ')) ∈cs (cs ⋯ ϕ)
  -- ∈cs-⋯ = {!!}

  ∈cs-⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
    {c : µ₁ ⊢ 𝕔} {cs : µ₁ ⊢ 𝕔𝕤} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
    c ∈cs cs →
    (c ⋯ ϕ) ∈cs (cs ⋯ ϕ)
  ∈cs-⋯ ϕ (here refl) = here refl
  ∈cs-⋯ ϕ (there x) = there (∈cs-⋯ ϕ x)

  Ex⋯ :
      ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {cs : µ₁ ⊢ 𝕔𝕤} {t : µ₁ ⊢ 𝕥} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Exhaustive cs t →
    Exhaustive (cs ⋯ ϕ) (t ⋯ ϕ)
  Ex⋯ {cs = cs} {t} {ϕ} ex {e = e} can with ex (Can⋯ {e = e} {t = t} {ϕ = ϕ} can)
  ... | µ'' , p , e' , c∈cs , m =
    µ'' , p ⋯ ϕ , e' ⋯ (ϕ ↑*' µ'') , ∈cs-⋯ ϕ c∈cs , Matches⋯ ϕ m

open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

⊢cs→⊢c : ∀ {c : µ ⊢ 𝕔} {cs : µ ⊢ 𝕔𝕤} {t₁ t₂ : µ ⊢ 𝕥} →
  c ∈cs cs →
  Γ ⊢ cs ∶ Clause t₁ t₂ →
  Γ ⊢ c  ∶ Clause t₁ t₂
⊢cs→⊢c (here refl) (⊢-clause-∷ ⊢c ⊢cs) = ⊢c
⊢cs→⊢c (there x)   (⊢-clause-∷ ⊢c ⊢cs) = ⊢cs→⊢c x ⊢cs

⊢matching-sub : ∀ {µ µ'} {Γ : Ctx µ} {e : µ ⊢ 𝕖} {t : µ ⊢ 𝕥} {p : µ ⊢ 𝕡 µ'} {P : µ ⊢ ℙ µ'} →
  (m : Matches e p) →
  Γ ⊢ e ∶ t →
  Γ ⊢ p ∶ P →
  Γ ⊢* matching-sub m ∶ PatTy→Ctx' P via idₛ
  -- Γ ⊢* matching-sub m ∶ {!Γ ▶▶ PatTy→Ctx' P!}
⊢matching-sub M-`         ⊢e ⊢p x _ refl = {!!}
   -- Goal : Γ ⊢ x & ⦅ e ⦆ₛ₀ ∶ wk-telescope' (PatTy→Ctx' P) x ⋯ idₛ ,ₖ e
⊢matching-sub M-tt        ⊢e ⊢p x _ refl = {!!}
⊢matching-sub (M-, m₁ m₂) ⊢e ⊢p x _ refl = {!!}
⊢matching-sub (M-inj₁ m)  ⊢e ⊢p x _ refl = {!!}
⊢matching-sub (M-inj₂ m)  ⊢e ⊢p x _ refl = {!!}

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢-· {t₂ = t₂} (⊢-λ ⊢e₁) ⊢e₂) β-λ                   = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆)
subject-reduction {Γ = Γ} (⊢-match ⊢e ⊢cs ex)           (β-match c∈cs m refl) with ⊢cs→⊢c c∈cs ⊢cs
...                                                                   | ⊢-clause ⊢p ⊢e'
                                                                      -- = {!⊢e' ⊢⋯ₛ (⊢id ⊢∥ₛ {!!})!}
                                                                      = subst₂ (Γ ⊢_∶_) refl {!!} (⊢e' ⊢⋯ₛ ({!⊢idₛ ⊢∥ₛ ?!}))
-- Goal: (Γ ⊢* (idₛ ∥ (matching-sub m)) ∶ Γ ▶▶ PatTy→Ctx' P
-- Have: (Γ ⊢* idₛ ∥ _ϕ₂)               ∶ Γ ▶▶ wk*-Ctx _µ _Γ₂
                                                                      -- = subst₂ (_ ⊢_∶_) {!!} {!!}
                                                                      --          (⊢e' ⊢⋯ₛ ({!⊢id!} ⊢∥ₛ {!!}))
subject-reduction (⊢-λ ⊢e)                      (ξ-λ e↪e')            = ⊢-λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢-· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁')         = ⊢-· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢-· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂')         = ⊢-· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
