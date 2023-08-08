module Kitty.Examples.SystemFSub-Derive.LogicalSubtyping where

open import Data.Product using (_,_)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (Terms; SortTy; Var; NoVar)

open import Kitty.Examples.SystemFSub-Derive.Definitions

infix   3  _⊢_⊑ᴸ_

data _⊢_⊑ᴸ_ : Ctx S → S ⊢ s → S ⊢ s → Set where
  ⊑ᴸ-` : {Γ : Ctx S} {c : S ⊢ 𝕔} →
    Γ ⊢ c ∶ (t₁ ∶⊑ t₂) →
    Γ ⊢ t₁ ⊑ᴸ t₂
  ⊑ᴸ-𝟙 :
    Γ ⊢ t ⊑ᴸ 𝟙
  ⊑ᴸ-⇒ :
    Γ ⊢ t₁' ⊑ᴸ t₁ →
    Γ ⊢ t₂  ⊑ᴸ t₂' →
    Γ ⊢ (t₁ ⇒ t₂) ⊑ᴸ (t₁' ⇒ t₂')
  ⊑ᴸ-∀ : {Γ : Ctx S} →
    Γ ▶ ★ ⊢ t₂ ⊑ᴸ t₂' →
    Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ᴸ (∀[α⊑ t₁ ] t₂')
  ⊑ᴸ-refl : 
    Γ ⊢ t ⊑ᴸ t
  ⊑ᴸ-trans : 
    Γ ⊢ t₁ ⊑ᴸ t₂ →
    Γ ⊢ t₂ ⊑ᴸ t₃ →
    Γ ⊢ t₁ ⊑ᴸ t₃

⊑ᴸ→⊑ :
  Γ ⊢ t₁ ⊑ᴸ t₂ → 
  Γ ⊢ t₁ ⊑ t₂
⊑ᴸ→⊑ (⊑ᴸ-` y)                 = ⊑-` ⊑-refl y ⊑-refl
⊑ᴸ→⊑ ⊑ᴸ-𝟙                     = ⊑-𝟙
⊑ᴸ→⊑ (⊑ᴸ-⇒ t₁⊑ᴸt₂ t₁⊑ᴸt₃)     = ⊑-⇒ (⊑ᴸ→⊑ t₁⊑ᴸt₂) (⊑ᴸ→⊑ t₁⊑ᴸt₃)
⊑ᴸ→⊑ (⊑ᴸ-∀ t₁⊑ᴸt₂)            = ⊑-∀ (⊑ᴸ→⊑ t₁⊑ᴸt₂)
⊑ᴸ→⊑ ⊑ᴸ-refl                  = ⊑-refl
⊑ᴸ→⊑ (⊑ᴸ-trans t₁⊑ᴸt₂ t₁⊑ᴸt₃) = ⊑-trans (⊑ᴸ→⊑ t₁⊑ᴸt₂) (⊑ᴸ→⊑ t₁⊑ᴸt₃)

⊑→⊑ᴸ :
  Γ ⊢ t₁ ⊑ t₂ → 
  Γ ⊢ t₁ ⊑ᴸ t₂
⊑→⊑ᴸ (⊑-` t₁⊑t₂ y t₂⊑t₃) = ⊑ᴸ-trans (⊑→⊑ᴸ t₁⊑t₂) (⊑ᴸ-trans (⊑ᴸ-` y) (⊑→⊑ᴸ t₂⊑t₃))
⊑→⊑ᴸ ⊑-𝟙                 = ⊑ᴸ-𝟙
⊑→⊑ᴸ (⊑-⇒ t₁⊑t₂ t₁⊑t₃)   = ⊑ᴸ-⇒ (⊑→⊑ᴸ t₁⊑t₂) (⊑→⊑ᴸ t₁⊑t₃)
⊑→⊑ᴸ (⊑-∀ t₁⊑t₂)         = ⊑ᴸ-∀ (⊑→⊑ᴸ t₁⊑t₂)
⊑→⊑ᴸ ⊑-refl-var          = ⊑ᴸ-refl

