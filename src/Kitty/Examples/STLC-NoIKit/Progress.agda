module Kitty.Examples.STLC-NoIKit.Progress where

open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Kitty.Examples.STLC-NoIKit.Definitions

progress :
  Γ ⊢ e ∶ t →
  Value e ⊎ ∃[ e' ] (e ↪ e')
progress (τ-` x) = inj₁ (neutral (` _))
progress (τ-λ ⊢e) = inj₁ (λx _)
progress (τ-· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | inj₁ (neutral n)      | inj₁ v₂             = inj₁ (neutral (n · v₂))
... | inj₁ (λx e)           | inj₁ v₂             = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ)
... | inj₁ e₁-val           | inj₂ (e₂' , e₂↪e₂') = inj₂ (e₁ · e₂' , ξ-·₂ e₂↪e₂')
... | inj₂ (e₁' , e₁↪e₁')   | _                   = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
