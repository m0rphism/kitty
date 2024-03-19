module ReflectionLib.Named.Pretty where

import Level as Level

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String

open import Reflection hiding (name; Type; returnTC)
open import Agda.Builtin.Reflection
open import Level using (Level)
open import Function using (_$_)

open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Standard.Pretty

open PrettyOpts

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

mutual
  instance

    ppDef' : Pretty Definition'
    ppDef' .pp o (function cs) = "(function " ++ pp o cs ++ ")"
    ppDef' .pp o (data-type pars cs) = "(data-type " ++ pp o pars ++ " " ++ pp o cs ++ ")"
    ppDef' .pp o (record-type c fs) = "(record-type " ++ pp o c ++ " " ++ pp o fs ++ ")"
    ppDef' .pp o (data-cons d) = "(data-cons " ++ pp o d ++ ")"
    ppDef' .pp o axiom = "axiom"
    ppDef' .pp o prim-fun = "prim-fun"

    ppSort' : Pretty Sort'
    ppSort' .pp o (set t) = "(set " ++ pp o t ++ ")"
    ppSort' .pp o (lit n) = "(lit " ++ pp o n ++ ")"
    ppSort' .pp o (prop t) = "(prop " ++ pp o t ++ ")"
    ppSort' .pp o (propLit n) = "(propLit " ++ pp o n ++ ")"
    ppSort' .pp o (inf n) = "(inf " ++ pp o n ++ ")"
    ppSort' .pp o unknown = "unknown"

    ppPattern' : Pretty Pattern'
    ppPattern' .pp o (con c ps) = "(con " ++ pp o ps ++ ")"
    ppPattern' .pp o (dot t) = "(dot " ++ pp o t ++ ")"
    ppPattern' .pp o (var x) = "(var " ++ pp o x ++ ")"
    ppPattern' .pp o (lit l) = "(lit " ++ pp o l ++ ")"
    ppPattern' .pp o (proj f) = "(proj " ++ pp o f ++ ")"
    ppPattern' .pp o (absurd x) = "(absurd " ++ pp o x ++ ")"

    ppClause' : Pretty Clause'
    ppClause' .pp o (clause tel ps t) =
      "(clause " ++ pp o tel ++ " " ++ pp o ps ++ " " ++ pp o t ++ ")"
    ppClause' .pp o (absurd-clause tel ps) =
      "(absurd-clause " ++ pp o tel ++ " " ++ pp o ps ++ ")"

    {-# TERMINATING #-}
    ppTerm' : Pretty Term'
    ppTerm' .pp o (var x args) = "(var " ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm' .pp o (con c args) = "(con " ++ pp o c ++ " " ++ pp o args ++ ")"
    ppTerm' .pp o (def f args) = "(def " ++ pp o f ++ " " ++ pp o args ++ ")"
    ppTerm' .pp o (lam v t) = "(lam " ++ pp o v ++ " " ++ pp o t ++ ")"
    ppTerm' .pp o (pat-lam cs args) = "(pat-lam " ++ pp o cs ++ " " ++ pp o args ++ ")"
    ppTerm' .pp o (pi a b) = "(pi " ++ pp o a ++ " " ++ pp o b ++ ")"
    ppTerm' .pp o (agda-sort s) = "(agda-sort " ++ pp o s ++ ")"
    ppTerm' .pp o (lit l) = "(lit " ++ pp o l ++ ")"
    ppTerm' .pp o (meta x args) = "(meta " ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm' .pp o unknown = "unknown"
