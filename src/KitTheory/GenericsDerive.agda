{-# OPTIONS -vreflection-debug:10 #-}

module KitTheory.GenericsDerive where

open import KitTheory.Derive.Desc   public
open import KitTheory.Derive.To     public
open import KitTheory.Derive.From   public
open import KitTheory.Derive.ToFrom public
open import KitTheory.Derive.FromTo public
open import KitTheory.Derive.Iso    public

-- Example ---------------------------------------------------------------------

open import KitTheory.Derive.Common

open import Data.List using (List; []; _∷_)
open import KitTheory.Prelude using (_∋_)
open import KitTheory.Modes
open import KitTheory.Generics
open import KitTheory.Iso

-- module PatternsTest where

--   data VarMode : Set where
--     𝕖 : VarMode

--   data TermMode : Set where
--     𝕖 : TermMode
--     𝕔 : TermMode
--     𝕔𝕤 : TermMode

--   m→M : VarMode → TermMode
--   m→M 𝕖 = 𝕖

--   𝕄 : Modes
--   𝕄 = record { VarMode = VarMode ; TermMode = TermMode ; m→M = m→M }

--   data Pat : List VarMode → Set where
--     `_     : (m : VarMode) → Pat (m ∷ [])
--     `tt    : Pat []
--     _`,_   : ∀ {µ₁ µ₂} → Pat µ₁ → Pat µ₂ → Pat (µ₂ ++ µ₁)
--     `inj₁  : ∀ {µ} → Pat µ → Pat µ
--     `inj₂  : ∀ {µ} → Pat µ → Pat µ

--   data _⊢_ : List VarMode → TermMode → Set where
--     `_     : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m
--     `λ_    : ∀ {µ} → (𝕖 ∷ µ) ⊢ 𝕖 → µ ⊢ 𝕖
--     _·_    : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
--     `tt    : ∀ {µ} → µ ⊢ 𝕖
--     _`,_   : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖 → µ ⊢ 𝕖
--     `inj₁  : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖
--     `inj₂  : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖
--     `match : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕔𝕤
--     `[]    : ∀ {µ} → µ ⊢ 𝕔𝕤
--     _`∷_   : ∀ {µ} → µ ⊢ 𝕔 → µ ⊢ 𝕔𝕤 → µ ⊢ 𝕔𝕤
--     _`⇒_   : ∀ {µ µ'} → Pat µ' → (µ' ++ µ) ⊢ 𝕖 → µ ⊢ 𝕔

--   -- unquoteDecl desc = deriveDesc (quote 𝕄) (quote _⊢_) desc
--   -- xx = {!desc!}

--   unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso

--   -- open FromIso 𝕄 Iso

private module STLC where

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

  xx = {!_⋯ₛ_!}


  -- unquoteDecl Iso = deriveIso (quote 𝕄) (quote _⊢_) Iso
  -- unquoteDecl Iso = deriveIso' 𝕄 _⊢_ Iso
  -- unquoteDecl STLC    = deriveDesc   (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) STLC
  -- unquoteDecl to      = deriveTo     (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) to
  -- unquoteDecl from    = deriveFrom   (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) from
  -- unquoteDecl from∘to = deriveFromTo (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) (quote to) (quote from) from∘to
  -- unquoteDecl to∘from = deriveToFrom (quote VarMode) (quote TermMode) (quote m→M) (quote _⊢_) (quote STLC) (quote to) (quote from) to∘from

  -- Iso' : ∀ {µ} {M} → (µ ⊢ M) ≃ Tm STLC µ M
  -- Iso' = iso to from from∘to to∘from

  -- xx = {!Iso!}

  -- unquoteDecl cong₃ = runFreshT (cong-n 3 cong₃)

  -- STLC' : Desc
  -- STLC' = `σ (Fin 2) λ where
  --   zero       → `X (𝕧 ∷ []m) 𝕥 (`■ 𝕥)
  --   (suc zero) → `X []m 𝕥 (`X []m 𝕥 (`■ 𝕥))
  --   (suc (suc ()))

  -- to' : ∀ {µ M} → (µ ⊢ M) → Tm STLC µ M
  -- to' (` x)     = `var x
  -- to' (`λ e)    = `con (zero , to' e , refl)
  -- to' (e₁ · e₂) = `con (suc zero , to' e₁ , to' e₂ , refl)

  -- from' : ∀ {µ M} → Tm STLC µ M → (µ ⊢ M)
  -- from' (`var x)                           = ` x
  -- from' (`con (zero , e , refl))           = `λ (from' e)
  -- from' (`con (suc zero , e₁ , e₂ , refl)) = from' e₁ · from' e₂

  -- from∘to' : ∀ {µ M} → (a : µ ⊢ M) → from (to a) ≡ a
  -- from∘to' (` x)     = refl
  -- from∘to' (`λ e)    = cong `λ_ (from∘to' e)
  -- from∘to' (e₁ · e₂) = cong₂ _·_ (from∘to' e₁) (from∘to' e₂)

  -- -- TODO: make deriving work for dependent constructors...
  -- to∘from' : ∀ {µ M} → (a : Tm STLC µ M) → to (from a) ≡ a
  -- to∘from' (`var x)                           = refl
  -- to∘from' (`con (zero , e , refl))           = cong `con (cong-Σ refl (cong-× (to∘from' e) refl))
  -- to∘from' (`con (suc zero , e₁ , e₂ , refl)) = cong `con (cong-Σ refl (cong-× (to∘from' e₁) (cong-× (to∘from' e₂) refl)))
  -- -- to∘from' (`con (zero , e , refl))           = cong `con (cong-Σ refl (
  -- --                                               cong-Σ (to∘from' e) uip))
  -- -- to∘from' (`con (suc zero , e₁ , e₂ , refl)) = cong `con (cong-Σ refl (
  -- --                                               cong-Σ (to∘from' e₁) (
  -- --                                               cong-Σ {!to∘from' e₂!} {!!})))

  -- -- -- STLC-correct : STLC ≡ STLC'
  -- -- -- STLC-correct = refl

  -- -- -- to-correct : ∀ {µ M} (t : µ ⊢ M) → to t ≡ to' t
  -- -- -- to-correct (` x) = refl
  -- -- -- to-correct (`λ t) rewrite to-correct t = refl
  -- -- -- to-correct (t₁ · t₂) rewrite to-correct t₁ |  to-correct t₂ = refl

  -- -- -- from-correct : ∀ {µ M} (t : Tm STLC µ M) → from t ≡ from' t
  -- -- -- from-correct (`var x) = refl
  -- -- -- from-correct (`con (zero , t , refl)) rewrite from-correct t = refl
  -- -- -- from-correct (`con (suc zero , t₁ , t₂ , refl)) rewrite from-correct t₁ | from-correct t₂ = refl

