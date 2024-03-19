module ReflectionLib.Algorithms.Nat where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

open import ReflectionLib.Standard.Syntax

nat-pat : ℕ → Pattern
nat-pat zero = con (quote Nat.zero) []
nat-pat (suc x) = con (quote Nat.suc) (argᵥ (nat-pat x) ∷ [])

nat-con : ℕ → Term
nat-con zero = con (quote Nat.zero) []
nat-con (suc x) = con (quote Nat.suc) (argᵥ (nat-con x) ∷ [])

open import ReflectionLib.Named.Syntax

nat-pat' : ℕ → Pattern'
nat-pat' zero = con (quote Nat.zero) []
nat-pat' (suc x) = con (quote Nat.suc) (argᵥ (nat-pat' x) ∷ [])

nat-con' : ℕ → Term'
nat-con' zero = con (quote Nat.zero) []
nat-con' (suc x) = con (quote Nat.suc) (argᵥ (nat-con' x) ∷ [])
