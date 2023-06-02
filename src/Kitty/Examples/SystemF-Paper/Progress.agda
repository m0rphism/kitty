module Kitty.Examples.SystemF-Paper.Progress where

open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Kitty.Examples.SystemF-Derive.Definitions

progress : ∀ {Γ : Ctx µ} {e : µ ⊢ 𝕖} {t : µ ∶⊢ 𝕖} →
  Γ ⊢ e ∶ t →
  Value e ⊎ ∃[ e' ] (e ↪ e')
progress {e = `[_]_ {m = 𝕖} refl x} (⊢` ∋x)         = inj₁ (neutral (`ⁿ _))
progress {e = λx e}                 (⊢λ ⊢e)         = inj₁ (λx _)
progress {e = Λα e}                 (⊢Λ ⊢e)         = inj₁ (Λα _)
progress {e = e₁ · e₂}              (⊢· ⊢e₁ ⊢e₂)
 with progress ⊢e₁        | progress ⊢e₂
... | inj₁ (neutral n)    | inj₁ v₂                 = inj₁ (neutral (n · v₂))
... | inj₁ (λx e)         | inj₁ v₂                 = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ)
... | inj₁ e₁-val         | inj₂ (e₂' , e₂↪e₂')     = inj₂ (e₁ · e₂' , ξ-·₂ e₂↪e₂')
... | inj₂ (e₁' , e₁↪e₁') | _                       = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
progress {e = e₁ ∙ e₂}              (⊢∙ ⊢t₁ ⊢t₂ ⊢e)
 with progress ⊢e
... | inj₁ (Λα e)                                   = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-Λ)
... | inj₁ (neutral n)                              = inj₁ (neutral (n ∙t))
... | inj₂ (e₁' , e₁↪e₁')                           = inj₂ (e₁' ∙ e₂ , ξ-∙₁ e₁↪e₁')
 
