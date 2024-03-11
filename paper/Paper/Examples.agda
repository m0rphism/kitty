module Paper.Examples where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)

--! FUnsortedSyntax {
data Kind : Set where
  ★ : Kind                                 -- Type Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n                -- Type variable
  ∀[α∶_]_  : Kind → Type (suc n) → Type n  -- Universal quantification
  _⇒_      : Type n → Type n → Type n      -- Function type

data Expr (n m : ℕ) : Set where
  `_   : Fin m → Expr n m                  -- Expression variable
  λx_  : Expr n (suc m) → Expr n m         -- Expression abstraction
  Λα_  : Expr (suc n) m → Expr n m         -- Type abstraction
  _·_  : Expr n m → Expr n m → Expr n m    -- Expression application
  _∙_  : Expr n m → Type n → Expr n m      -- Type application
--! }


