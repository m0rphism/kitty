module Kitty.Examples.LambdaPi-Derive.Progress where

open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Kitty.Examples.LambdaPi-Derive.Definitions

progress : ∀ {Γ : Ctx µ} {e : µ ⊢ M} {t : µ ∶⊢ M} →
  Γ ⊢ e ∶ t →
  Value e ⊎ ∃[ e' ] (e ↪ e')
progress (⊢` {m = 𝕖} x) = inj₁ (neutral (`ⁿ _))
progress (⊢λ ⊢e) = inj₁ (λx _)
progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | inj₁ (neutral n)    | inj₁ v₂             = inj₁ (neutral (n · v₂))
... | inj₁ (λx e)         | inj₁ v₂             = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ)
... | inj₁ e₁-val         | inj₂ (e₂' , e₂↪e₂') = inj₂ (e₁ · e₂' , ξ-·₂ e₂↪e₂')
... | inj₂ (e₁' , e₁↪e₁') | _                   = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
