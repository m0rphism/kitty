module Kitty.Examples.STLC.Progress where

-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
-- open ≡-Reasoning
-- open import Data.List using (List; []; _∷_; drop)
-- open import Data.List.Relation.Unary.Any using (here; there)
-- open import Data.Unit using (⊤; tt)
-- open import Function using () renaming (_∋_ to _by_)
-- open import Data.Product using (_×_; ∃-syntax; _,_)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)

-- open import Kitty.Examples.STLC.Definitions

-- progress :
--   Γ ⊢ e ∶ t →
--   Value e ⊎ ∃[ e' ] (e ↪ e')
-- progress (τ-` x) = inj₁ (neutral `x)
-- progress (τ-λ ⊢e) = inj₁ λxe
-- progress (τ-· {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
-- ... | inj₁ (neutral n)      | inj₁ v₂             = inj₁ (neutral (n · v₂))
-- ... | inj₁ (λxe {e = e})    | inj₁ v₂             = inj₂ (e ⋯ ⦅ e₂ ⦆ , β-λ v₂)
-- ... | inj₁ e₁-val           | inj₂ (e₂' , e₂↪e₂') = inj₂ (e₁ · e₂' , ξ-·₂ e₁-val e₂↪e₂')
-- ... | inj₂ (e₁' , e₁↪e₁')   | _                   = inj₂ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
