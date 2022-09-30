module Kitty.Experimental.Examples.SystemFLin-Kits.Progress where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (_∋_ to _by_)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Kitty.Experimental.Examples.SystemFLin-Kits.Definitions hiding (_,_)

progress :
  Γ ⊢ e ∶ t →
  Value e ⊎ ∃[ e' ] (e ↪ e')
progress (τ-` x) = inj₁ (neutral `x)
progress (τ-λ ⊢e) with progress ⊢e
... | inj₁ v           = inj₁ (λ→ v)
... | inj₂ (e' , e↪e') = inj₂ (λ→ e' , ξ-λ e↪e')
progress (τ-Λ ⊢e) with progress ⊢e
... | inj₁ v           = inj₁ (Λ→ v)
... | inj₂ (e' , e↪e') = inj₂ (Λ→ e' , ξ-Λ e↪e')
progress (τ-· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | inj₁ (neutral n)      | inj₁ v₂             = inj₁ (neutral (n · v₂))
... | inj₁ (λ→_ {e = e} v₁) | inj₁ v₂             = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ)
... | inj₁ _                | inj₂ (e₂' , e₂↪e₂') = inj₂ (e₁ · e₂' , ξ-·₂ e₂↪e₂')
... | inj₂ (e₁' , e₁↪e₁')   | _                   = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
progress (τ-∙ {t = t} ⊢e) with progress ⊢e
... | inj₁ (neutral n)     = inj₁ (neutral (n ∙t))
... | inj₁ (Λ→_ {e = e} v) = inj₂ (e ⋯ ⦅ t ⦆ , β-Λ)
... | inj₂ (e' , e↪e')     = inj₂ (e' ∙ t , ξ-∙ e↪e')
