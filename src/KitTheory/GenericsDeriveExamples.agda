module KitTheory.GenericsDeriveExamples where

open import KitTheory.Prelude
open import KitTheory.Modes
open import KitTheory.Generics
open import KitTheory.GenericsDerive

open import Data.List using (List; []; _∷_)
    
module STLC where

  data VarMode : Set where
    𝕧 : VarMode

  data TermMode : Set where
    𝕥 : TermMode

  m→M : VarMode → TermMode
  m→M 𝕧 = 𝕥

  𝕄 : Modes
  𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

  data _⊢_ : List VarMode → TermMode → Set where
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
    `λ_ : ∀ {µ} → (𝕧 ∷ µ) ⊢ 𝕥 → µ ⊢ 𝕥
    _·_ : ∀ {µ} → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕥

  unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  open FromIso 𝕄 Iso

module SystemF where

  data VarMode : Set where
    𝕖 : VarMode
    𝕥 : VarMode

  data TermMode : Set where
    𝕖 : TermMode
    𝕥 : TermMode

  m→M : VarMode → TermMode
  m→M 𝕖 = 𝕖
  m→M 𝕥 = 𝕥

  𝕄 : Modes
  𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

  data _⊢_ : List VarMode → TermMode → Set where
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
    `λ_ : ∀ {µ} → (𝕖 ∷ µ) ⊢ 𝕖 → µ ⊢ 𝕖
    _·_ : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `Λ_ : ∀ {µ} → (𝕥 ∷ µ) ⊢ 𝕖 → µ ⊢ 𝕖
    _∙_ : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕥 → µ ⊢ 𝕖
    `tt : ∀ {µ} → µ ⊢ 𝕖
    `⊤  : ∀ {µ} → µ ⊢ 𝕥
    _`⇒_ : ∀ {µ} → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕥
    `∀_ : ∀ {µ} → (𝕥 ∷ µ) ⊢ 𝕥 → µ ⊢ 𝕥

  unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  open FromIso 𝕄 Iso

module STLC-Intrinsic where

  data Ty : Set where
    `⊤ : Ty
    _`⇒_ : Ty → Ty → Ty

  m→M : Ty → Ty
  m→M ty = ty

  𝕄 : Modes
  𝕄 = record { VarMode = Ty ; TermMode = Ty ; m→M = m→M }

  data _⊢_ : List Ty → Ty → Set where
    `_  : ∀ {Γ t} → Γ ∋ t → Γ ⊢ m→M t
    `λ_ : ∀ {Γ t₁ t₂} → (t₁ ∷ Γ) ⊢ t₂ → Γ ⊢ (t₁ `⇒ t₂)
    _·_ : ∀ {Γ t₁ t₂} → Γ ⊢ (t₁ `⇒ t₂) → Γ ⊢ t₁ → Γ ⊢ t₂

  -- unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  -- open FromIso 𝕄 Iso

