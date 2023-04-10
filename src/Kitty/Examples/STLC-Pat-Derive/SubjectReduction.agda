module Kitty.Examples.STLC-Pat-Derive.SubjectReduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; module ≡-Reasoning)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open ≡-Reasoning
open import Kitty.Examples.STLC-Pat-Derive.Definitions

open import Kitty.Typing.ITerms compose-traversal kit-type ℂ

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
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-clause-[]                    = ⊢-clause-[]
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-clause-∷ {P = P} ⊢p ⊢e ⊢cs) = ⊢-clause-∷ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)
                                                            (≡ᶜ-cong-⊢ (≡ᶜ-cong-▶▶ {Γ₁' = PatTy→Ctx' P} Γ₁≡Γ₂ ≡ᶜ-refl) ⊢e)
                                                            (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢cs)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-ttᵖ                          = ⊢-ttᵖ
≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢-`ᵖ                           = ⊢-`ᵖ
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-,ᵖ ⊢p₁ ⊢p₂)                 = ⊢-,ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p₁) (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p₂)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₁ᵖ ⊢p)                   = ⊢-inj₁ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)
≡ᶜ-cong-⊢ Γ₁≡Γ₂ (⊢-inj₂ᵖ ⊢p)                   = ⊢-inj₂ᵖ (≡ᶜ-cong-⊢ Γ₁≡Γ₂ ⊢p)

open import Kitty.Typing.IKit compose-traversal kit-type ℂ record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢-`; ≡ᶜ-cong-⊢ = ≡ᶜ-cong-⊢ }
open IKit ⦃ … ⦄

mutual
  _⊢⋯_ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {e : µ₁ ⊢ M} {t : µ₁ ∶⊢ M} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
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
  ⊢-clause-[]          ⊢⋯ ⊢ϕ = ⊢-clause-[]
  ⊢-clause-∷ ⊢p ⊢e ⊢cs ⊢⋯ ⊢ϕ = ⊢-clause-∷ (⊢p ⊢⋯ ⊢ϕ) (⊢e ⊢⋯ (⊢ϕ ∋↑*/⊢↑* _)) (⊢cs ⊢⋯ ⊢ϕ)
  ⊢-ttᵖ                ⊢⋯ ⊢ϕ = ⊢-ttᵖ
  ⊢-`ᵖ                 ⊢⋯ ⊢ϕ = ⊢-`ᵖ
  _⊢⋯_ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢-,ᵖ {p₁ = p₁} {P₁ = P₁} {p₂ = p₂} {P₂ = P₂} ⊢p₁ ⊢p₂) ⊢ϕ =
    subst (Γ₂ ⊢ ((p₁ ⋯ ϕ) ,ᵖ (p₂ ⋯ ϕ)) ∶_)
    (((P₁ ⋯ ϕ) ▶▶ᵖ (P₂ ⋯ ϕ)) ≡⟨ {!!} ⟩
    (P₁ ▶▶ᵖ P₂) ⋯ ϕ         ∎)
    (⊢-,ᵖ (⊢p₁ ⊢⋯ ⊢ϕ) (⊢p₂ ⊢⋯ (⊢ϕ ∋↑*/⊢↑* PatTy→Ctx' P₁)))
  ⊢-inj₁ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₁ᵖ (⊢p ⊢⋯ ⊢ϕ)
  ⊢-inj₂ᵖ ⊢p           ⊢⋯ ⊢ϕ = ⊢-inj₂ᵖ (⊢p ⊢⋯ ⊢ϕ)

  Can⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {e : µ₁ ⊢ 𝕖} {t : µ₁ ⊢ 𝕥} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Canonical e (t ⋯ ϕ) →
    Canonical e t
  Can⋯ {µ₁} {µ₂} {e = e}         {`[_]_ {m = 𝕖} () x} {ϕ} can
  Can⋯ {µ₁} {µ₂} {e = .(λx _)}   {t₁ `→ t₂} {ϕ} C-λ             = C-λ
  Can⋯ {µ₁} {µ₂} {e = .tt}       {𝟙}        {ϕ} C-tt            = C-tt
  Can⋯ {µ₁} {µ₂} {e = .(_ , _)}  {t₁ `× t₂} {ϕ} (C-, can₁ can₂) = C-, (Can⋯ can₁) (Can⋯ can₂)
  Can⋯ {µ₁} {µ₂} {e = .(inj₁ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₁ can)    = C-inj₁ (Can⋯ can)
  Can⋯ {µ₁} {µ₂} {e = .(inj₂ _)} {t₁ `⊎ t₂} {ϕ} (C-inj₂ can)    = C-inj₂ (Can⋯ can)

  -- Matches⋯ :
  --   ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
  --     ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
  --     ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
  --     ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
  --     {e : µ₁ ⊢ 𝕖} {cs : µ₂ ⊢ 𝕔𝕤} (p : µ₂ ⊢ 𝕡 µ') {e' : (µ₂ ▷▷ µ') ⊢ 𝕖} {M : Matches e p} {ϕ : µ₂ –[ 𝕂 ]→ µ₃} →
  --   Matches₁ e cs p e' M →
  --   ∃[ M' ] Matches₁ e (cs ⋯ ϕ) (p ⋯ ϕ) (e' ⋯ ϕ) M'
  -- Matches⋯ = ?

  Ex⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ ⦃ C₁ : ComposeKit 𝕂 kitᵣ 𝕂 ⦄ ⦃ C₂ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ IK : IKit 𝕂 K C₁ C₂ ⦄
      ⦃ C₃ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₄ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      {cs : µ₁ ⊢ 𝕔𝕤} {t : µ₁ ⊢ 𝕥} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} →
    Exhaustive cs t →
    Exhaustive (cs ⋯ ϕ) (t ⋯ ϕ)
  -- Ex⋯ {cs = cs} {t} {ϕ} ex can = {!ex (Can⋯ can)!}
  Ex⋯ {cs = cs} {`[_]_ {m = 𝕖} () x₁} {ϕ} ex can
  Ex⋯ {cs = cs} {t₁ `→ t₂} {ϕ} ex (C-λ {e = e}) = {!ex (C-λ {e = e})!}
  Ex⋯ {cs = cs} {𝟙}        {ϕ} ex can = {!!}
  Ex⋯ {cs = cs} {t₁ `× t₂} {ϕ} ex can = {!!}
  Ex⋯ {cs = cs} {t₁ `⊎ t₂} {ϕ} ex can = {!!}

-- open ITraversal record { _⊢⋯_ = _⊢⋯_ } public hiding (_⊢⋯_)

-- subject-reduction :
--   Γ ⊢ e ∶ t →
--   e ↪ e' →
--   Γ ⊢ e' ∶ t
-- subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆)
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁))         β-Λ          = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆
-- subject-reduction (⊢λ ⊢e)                      (ξ-λ e↪e')    = ⊢λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢Λ ⊢e)                      (ξ-Λ e↪e')    = ⊢Λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
