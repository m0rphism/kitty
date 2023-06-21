module Paper.Examples where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)

--! FUnsortedSyntax {
data Kind : Set where
  ★ : Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n
  ∀[α∶_]_  : Kind → Type (suc n) → Type n 
  _⇒_      : Type n → Type n → Type n

data Expr (n m : ℕ) : Set where
  `_       : Fin m → Expr n m
  λ[x∶_]_  : Type n → Expr n (suc m) → Expr n m 
  Λ[α∶_]_  : Kind → Expr (suc n) m → Expr n m 
  _·_      : Expr n m → Expr n m → Expr n m
  _∙_      : Expr n m → Type n → Expr n m
--! }



