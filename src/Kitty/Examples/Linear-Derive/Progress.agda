module Kitty.Examples.SystemF-Derive.Progress where

open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Kitty.Examples.SystemF-Derive.Definitions

progress : ∀ {Γ : Ctx S} {e : S ⊢ 𝕖} {t : S ∶⊢ 𝕖} →
  Γ ⊢ e ∶ t →
  Value e ⊎ ∃[ e' ] (e ↪ e')
progress (⊢` ∋x)         = inj₁ (neutral (` _))
progress (⊢λ ⊢e)         = inj₁ (λx _)
progress (⊢Λ ⊢e)         = inj₁ (Λα _)
progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂)
 with progress ⊢e₁        | progress ⊢e₂
... | inj₁ (neutral n)    | inj₁ v₂                 = inj₁ (neutral (n · v₂))
... | inj₁ (λx e)         | inj₁ v₂                 = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ)
... | inj₁ e₁-val         | inj₂ (e₂' , e₂↪e₂')     = inj₂ (e₁ · e₂' , ξ-·₂ e₂↪e₂')
... | inj₂ (e₁' , e₁↪e₁') | _                       = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
progress (⊢∙ {t₂ = t₂} {e₁ = e₁} ⊢t₁ ⊢t₂ ⊢e₁)
 with progress ⊢e₁
... | inj₁ (Λα e)                                   = inj₂ (e ⋯ ⦅ t₂ ⦆ , β-Λ)
... | inj₁ (neutral n)                              = inj₁ (neutral (n ∙t))
... | inj₂ (e₁' , e₁↪e₁')                           = inj₂ (e₁' ∙ t₂ , ξ-∙₁ e₁↪e₁')
