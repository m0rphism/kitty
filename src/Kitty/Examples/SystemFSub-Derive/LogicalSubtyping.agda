module Kitty.Examples.SystemFSub-Derive.LogicalSubtyping where

open import Data.Product using (_,_)
open import Kitty.Term.Prelude using (_∋_; List; []; _▷_) public
open import Kitty.Term.Terms using (Terms; SortTy; Var; NoVar)

open import Kitty.Examples.SystemFSub-Derive.Definitions

infix   3  _⊢_⊑_

data _⊢_⊑_ : Ctx S → S ⊢ s → S ⊢ s → Set where
  ⊑-` : {Γ : Ctx S} {c : S ⊢ 𝕔} →
    Γ ⊢ c ∶ (t₁ ∶⊑ t₂) →
    Γ ⊢ t₁ ⊑ t₂
  ⊑-𝟙 :
    Γ ⊢ t ⊑ 𝟙
  ⊑-⇒ :
    Γ ⊢ t₁' ⊑ t₁ →
    Γ ⊢ t₂  ⊑ t₂' →
    Γ ⊢ (t₁ ⇒ t₂) ⊑ (t₁' ⇒ t₂')
  ⊑-∀ : {Γ : Ctx S} →
    Γ ▶ ★ ⊢ t₂ ⊑ t₂' →
    Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ (∀[α⊑ t₁ ] t₂')
  ⊑-refl : 
    Γ ⊢ t ⊑ t
  ⊑-trans : 
    Γ ⊢ t₁ ⊑ t₂ →
    Γ ⊢ t₂ ⊑ t₃ →
    Γ ⊢ t₁ ⊑ t₃

⊑→⊑ₐ :
  Γ ⊢ t₁ ⊑ t₂ → 
  Γ ⊢ t₁ ⊑ₐ t₂
⊑→⊑ₐ (⊑-` y)               = ⊑ₐ-` ⊑ₐ-refl y ⊑ₐ-refl
⊑→⊑ₐ ⊑-𝟙                   = ⊑ₐ-𝟙
⊑→⊑ₐ (⊑-⇒ t₁⊑t₂ t₁⊑t₃)     = ⊑ₐ-⇒ (⊑→⊑ₐ t₁⊑t₂) (⊑→⊑ₐ t₁⊑t₃)
⊑→⊑ₐ (⊑-∀ t₁⊑t₂)           = ⊑ₐ-∀ (⊑→⊑ₐ t₁⊑t₂)
⊑→⊑ₐ ⊑-refl                = ⊑ₐ-refl
⊑→⊑ₐ (⊑-trans t₁⊑t₂ t₁⊑t₃) = ⊑ₐ-trans (⊑→⊑ₐ t₁⊑t₂) (⊑→⊑ₐ t₁⊑t₃)

⊑ₐ→⊑ :
  Γ ⊢ t₁ ⊑ₐ t₂ → 
  Γ ⊢ t₁ ⊑ t₂
⊑ₐ→⊑ (⊑ₐ-` t₁⊑ₐt₂ y t₂⊑ₐt₃)         = ⊑-trans (⊑ₐ→⊑ t₁⊑ₐt₂) (⊑-trans (⊑-` y) (⊑ₐ→⊑ t₂⊑ₐt₃))
⊑ₐ→⊑ ⊑ₐ-𝟙                           = ⊑-𝟙
⊑ₐ→⊑ (⊑ₐ-⇒ t₁⊑ₐt₂ t₁⊑ₐt₃)           = ⊑-⇒ (⊑ₐ→⊑ t₁⊑ₐt₂) (⊑ₐ→⊑ t₁⊑ₐt₃)
⊑ₐ→⊑ (⊑ₐ-∀ t₁⊑ₐt₂)                  = ⊑-∀ (⊑ₐ→⊑ t₁⊑ₐt₂)
⊑ₐ→⊑ ⊑ₐ-refl-var                    = ⊑-refl

