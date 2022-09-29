{-# OPTIONS -vreflection-debug:10 #-}

module KitTheory.GenericsDeriveExamples where

open import KitTheory.Prelude
open import KitTheory.Modes
open import KitTheory.Generics
open import KitTheory.GenericsDerive

open import Data.List using (List; []; _∷_)

module STLC where

  data VarMode : Set where
    𝕖 : VarMode

  data TermMode : Set where
    𝕖 : TermMode

  m→M : VarMode → TermMode
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

  data _⊢_ : List VarMode → TermMode → Set where
    `_  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
    `λ_ : ∀ {µ} → (µ ▷ 𝕖) ⊢ 𝕖 → µ ⊢ 𝕖
    _·_ : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖

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
    `λ_ : ∀ {µ} → (µ ▷ 𝕖) ⊢ 𝕖 → µ ⊢ 𝕖
    _·_ : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `Λ_ : ∀ {µ} → (µ ▷ 𝕥) ⊢ 𝕖 → µ ⊢ 𝕖
    _∙_ : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕥 → µ ⊢ 𝕖
    `tt : ∀ {µ} → µ ⊢ 𝕖
    `⊤  : ∀ {µ} → µ ⊢ 𝕥
    _`⇒_ : ∀ {µ} → µ ⊢ 𝕥 → µ ⊢ 𝕥 → µ ⊢ 𝕥
    `∀_ : ∀ {µ} → (µ ▷ 𝕥) ⊢ 𝕥 → µ ⊢ 𝕥

  unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  open FromIso 𝕄 Iso

module Patterns where

  data VarMode : Set where
    𝕖 : VarMode

  data TermMode : Set where
    𝕖 : TermMode
    𝕔 : TermMode
    𝕔𝕤 : TermMode

  m→M : VarMode → TermMode
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

  data Pat : List VarMode → Set where
    `_     : (m : VarMode) → Pat ([] ▷ m)
    `tt    : Pat []
    _`,_   : ∀ {µ₁ µ₂} → Pat µ₁ → Pat µ₂ → Pat (µ₁ ▷▷ µ₂)
    `inj₁  : ∀ {µ} → Pat µ → Pat µ
    `inj₂  : ∀ {µ} → Pat µ → Pat µ

  data _⊢_ : List VarMode → TermMode → Set where
    `_     : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
    `λ_    : ∀ {µ} → (µ ▷ 𝕖) ⊢ 𝕖 → µ ⊢ 𝕖
    _·_    : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `tt    : ∀ {µ} → µ ⊢ 𝕖
    _`,_   : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `inj₁  : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `inj₂  : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖
    `match : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕔𝕤
    `[]    : ∀ {µ} → µ ⊢ 𝕔𝕤
    _`∷_   : ∀ {µ} → µ ⊢ 𝕔 → µ ⊢ 𝕔𝕤 → µ ⊢ 𝕔𝕤
    _`⇒_   : ∀ {µ µ'} → Pat µ' → (µ ▷▷ µ') ⊢ 𝕖 → µ ⊢ 𝕔

  unquoteDecl desc    = deriveDesc   (quote 𝕄) (quote _⊢_) desc
  unquoteDecl to      = deriveTo     (quote 𝕄) (quote _⊢_) (quote desc) to
  unquoteDecl from    = deriveFrom   (quote 𝕄) (quote _⊢_) (quote desc) from
  unquoteDecl from∘to = deriveFromTo (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) from∘to
  -- unquoteDecl to∘from = deriveToFrom (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) to∘from

  -- xx = {!desc!}
  -- unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  -- open FromIso 𝕄 Iso

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
    `λ_ : ∀ {Γ t₁ t₂} → (Γ ▷ t₁) ⊢ t₂ → Γ ⊢ (t₁ `⇒ t₂)
    _·_ : ∀ {Γ t₁ t₂} → Γ ⊢ (t₁ `⇒ t₂) → Γ ⊢ t₁ → Γ ⊢ t₂

  -- unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

  -- open FromIso 𝕄 Iso

