module Paper.Examples where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)

--! FUnsortedSyntax {
data Kind : Set where
  ★ : Kind                                 -- Type Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n                -- Type Var
  ∀[α∶_]_  : Kind → Type (suc n) → Type n  -- Univ Quant
  _⇒_      : Type n → Type n → Type n      -- Functions

data Expr (n m : ℕ) : Set where
  `_   : Fin m → Expr n m                  -- Expr Var
  λx_  : Expr n (suc m) → Expr n m         -- Expr Abs
  Λα_  : Expr (suc n) m → Expr n m         -- Type Abs
  _·_  : Expr n m → Expr n m → Expr n m    -- Expr App
  _∙_  : Expr n m → Type n → Expr n m      -- Type App
--! }


