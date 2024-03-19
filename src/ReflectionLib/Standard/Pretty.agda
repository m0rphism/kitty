module ReflectionLib.Standard.Pretty where

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

open PrettyOpts

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

mutual
  instance

    ppDef : Pretty Definition
    ppDef .pp o (function cs) = "(function " ++ pp o cs ++ ")"
    ppDef .pp o (data-type pars cs) = "(data-type " ++ pp o pars ++ " " ++ pp o cs ++ ")"
    ppDef .pp o (record-type c fs) = "(record-type " ++ pp o c ++ " " ++ pp o fs ++ ")"
    ppDef .pp o (data-cons d) = "(data-cons " ++ pp o d ++ ")"
    ppDef .pp o axiom = "axiom"
    ppDef .pp o prim-fun = "prim-fun"

    ppVar : Pretty ℕ
    ppVar .pp o 0 = "0"
    ppVar .pp o 1 = "1"
    ppVar .pp o 2 = "2"
    ppVar .pp o 3 = "3"
    ppVar .pp o 4 = "4"
    ppVar .pp o 5 = "5"
    ppVar .pp o 6 = "6"
    ppVar .pp o 7 = "7"
    ppVar .pp o 8 = "8"
    ppVar .pp o 9 = "9"
    ppVar .pp o (suc x) = "(suc " ++ pp o x ++ ")"

    {-# TERMINATING #-}
    ppList : {{_ : Pretty A}} → Pretty (List A)
    ppList .pp o xs = "(" ++ f xs ++ ")" where
      f : {{_ : Pretty A}} → List A → String
      f [] = "[]"
      f (x ∷ xs) = pp o x ++ " ∷ " ++ f xs

    ppArg : {{_ : Pretty A}} → Pretty (Arg A)
    ppArg .pp o (arg (arg-info visible m) x) = "(argᵥ " ++ pp o x ++ ")"
    ppArg .pp o (arg (arg-info hidden m) x) = "(argₕ " ++ pp o x ++ ")"
    ppArg .pp o (arg (arg-info instance′ m) x) = "(argᵢ " ++ pp o x ++ ")"

    ppName : Pretty Name
    ppName .pp o n =
      let s = primShowQName n in
      if o .stripModules then strip-modules s else s

    ppVis : Pretty Visibility
    ppVis .pp o visible = "visible"
    ppVis .pp o hidden = "hidden"
    ppVis .pp o instance′ = "instance′"

    ppStr : Pretty String
    ppStr .pp o s = "\"" ++ s ++ "\"" -- TODO: escapes

    ppAbs : {{_ : Pretty A}} → Pretty (Abs A)
    ppAbs .pp o (abs s x) = "(abs " ++ pp o s ++ " " ++ pp o x ++ ")"

    ppSort : Pretty Sort
    ppSort .pp o (set t) = "(set " ++ pp o t ++ ")"
    ppSort .pp o (lit n) = "(lit " ++ pp o n ++ ")"
    ppSort .pp o (prop t) = "(prop " ++ pp o t ++ ")"
    ppSort .pp o (propLit n) = "(propLit " ++ pp o n ++ ")"
    ppSort .pp o (inf n) = "(inf " ++ pp o n ++ ")"
    ppSort .pp o unknown = "unknown"

    ppLit : Pretty Literal
    ppLit .pp o (nat n) = "(nat " ++ pp o n ++ ")"
    ppLit .pp o (word64 n) = "(word64 TODO)" -- TODO
    ppLit .pp o (float x) = "(float TODO)" -- TODO
    ppLit .pp o (char c) = "(char TODO)" -- TODO
    ppLit .pp o (string s) = "(string " ++ pp o s ++ ")"
    ppLit .pp o (name x) = "(name " ++ pp o x ++ ")"
    ppLit .pp o (meta x) = "(meta " ++ pp o x ++ ")"

    ppMeta : Pretty Meta
    ppMeta .pp o m = "META" -- TODO?

    ppPair : {{_ : Pretty A}} {{_ : Pretty B}} → Pretty (A × B)
    ppPair .pp o (a , b) = "(" ++ pp o a ++ " , " ++ pp o b ++ ")"

    ppPattern : Pretty Pattern
    ppPattern .pp o (con c ps) = "(con " ++ pp o c ++ " " ++ pp o ps ++ ")"
    ppPattern .pp o (dot t) = "(dot " ++ pp o t ++ ")"
    ppPattern .pp o (var x) = "(var " ++ pp o x ++ ")"
    ppPattern .pp o (lit l) = "(lit " ++ pp o l ++ ")"
    ppPattern .pp o (proj f) = "(proj " ++ pp o f ++ ")"
    ppPattern .pp o (absurd x) = "(absurd " ++ pp o x ++ ")"

    ppClause : Pretty Clause
    ppClause .pp o (clause tel ps t) =
      "(clause " ++ pp o tel ++ " " ++ pp o ps ++ " " ++ pp o t ++ ")"
    ppClause .pp o (absurd-clause tel ps) =
      "(absurd-clause " ++ pp o tel ++ " " ++ pp o ps ++ ")"

    ppTerm : Pretty Term
    ppTerm .pp o (var x args) = "(var " ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (con c args) = "(con " ++ pp o c ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (def f args) = "(def " ++ pp o f ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (lam v t) = "(lam " ++ pp o v ++ " " ++ pp o t ++ ")"
    ppTerm .pp o (pat-lam cs args) = "(pat-lam " ++ pp o cs ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (pi a b) = "(pi " ++ pp o a ++ " " ++ pp o b ++ ")"
    ppTerm .pp o (agda-sort s) = "(agda-sort " ++ pp o s ++ ")"
    ppTerm .pp o (lit l) = "(lit " ++ pp o l ++ ")"
    ppTerm .pp o (meta x args) = "(meta " ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm .pp o unknown = "unknown"
