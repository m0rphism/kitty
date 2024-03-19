module ReflectionLib.Algorithms.Fin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)

open import ReflectionLib.Standard.Syntax

fin-pat : ℕ → Pattern
fin-pat zero = con (quote Fin.zero) []
fin-pat (suc x) = con (quote Fin.suc) (argᵥ (fin-pat x) ∷ [])

fin-con : ℕ → Term
fin-con zero = con (quote Fin.zero) []
fin-con (suc x) = con (quote Fin.suc) (argᵥ (fin-con x) ∷ [])

open import ReflectionLib.Named.Syntax

fin-pat' : ℕ → Pattern'
fin-pat' zero = con (quote Fin.zero) []
fin-pat' (suc x) = con (quote Fin.suc) (argᵥ (fin-pat' x) ∷ [])

fin-con' : ℕ → Term'
fin-con' zero = con (quote Fin.zero) []
fin-con' (suc x) = con (quote Fin.suc) (argᵥ (fin-con' x) ∷ [])
