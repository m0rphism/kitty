module ReflectionLib.Standard.VeryPretty where

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

open import Reflection hiding (name; Type)
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

    -- TODO
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

    -- TODO
    {-# TERMINATING #-}
    ppList : {{_ : Pretty A}} → Pretty (List A)
    ppList .pp o xs = f xs where
      f : {{_ : Pretty A}} → List A → String
      f [] = ""
      f (x ∷ []) = pp o x
      f (x ∷ xs) = pp o x ++ " " ++ f xs

    ppArg : {{_ : Pretty A}} → Pretty (Arg A)
    ppArg .pp o (arg (arg-info visible m) x) = pp o x
    ppArg .pp o (arg (arg-info hidden m) x) = "{" ++ pp o x ++ "}"
    ppArg .pp o (arg (arg-info instance′ m) x) = "{{" ++ pp o x ++ "}}"

    ppName : Pretty Name
    ppName .pp o n =
      let s = primShowQName n in
      if o .stripModules then strip-modules s else s

    -- TODO
    ppVis : Pretty Visibility
    ppVis .pp o visible = "visible"
    ppVis .pp o hidden = "hidden"
    ppVis .pp o instance′ = "instance′"

    ppStr : Pretty String
    ppStr .pp o s = "\"" ++ s ++ "\"" -- TODO: escapes

    ppAbs : {{_ : Pretty A}} → Pretty (Abs A)
    ppAbs .pp o (abs s x) = pp o s ++ " → " ++ pp o x

    -- TODO
    ppSort : Pretty Sort
    ppSort .pp o (set t) = "(Set " ++ pp o t ++ ")"
    ppSort .pp o (lit n) = pp o n
    ppSort .pp o (prop t) = "(Prop " ++ pp o t ++ ")"
    ppSort .pp o (propLit n) = "(Prop " ++ pp o n ++ ")"
    ppSort .pp o (inf n) = "(Inf " ++ pp o n ++ ")"
    ppSort .pp o unknown = "_"

    ppLit : Pretty Literal
    ppLit .pp o (nat n) = pp o n
    ppLit .pp o (word64 n) = "(word64 TODO)" -- TODO
    ppLit .pp o (float x) = "(float TODO)" -- TODO
    ppLit .pp o (char c) = "(char TODO)" -- TODO
    ppLit .pp o (string s) = pp o s
    ppLit .pp o (name x) = pp o x
    ppLit .pp o (meta x) = pp o x

    ppMeta : Pretty Meta
    ppMeta .pp o m = "META" -- TODO?

    -- Telescope Bind
    ppPair : {{_ : Pretty A}} {{_ : Pretty B}} → Pretty (A × B)
    ppPair .pp o (a , b) = "(" ++ pp o a ++ " : " ++ pp o b ++ ")"

    ppPattern : Pretty Pattern
    ppPattern .pp o (con c []) = pp o c
    ppPattern .pp o (con c ps) = "(" ++ pp o c ++ " " ++ pp o ps ++ ")"
    ppPattern .pp o (dot t) = "." ++ pp o t
    ppPattern .pp o (var x) = "#" ++ pp o x
    ppPattern .pp o (lit l) = pp o l
    ppPattern .pp o (proj f) = "." ++ pp o f
    ppPattern .pp o (absurd x) = "(absurd " ++ pp o x ++ ")"

    ppClause : Pretty Clause
    ppClause .pp o (clause tel ps t) =
      "(" ++ pp o tel ++ " ⊢ " ++ pp o ps ++ " → " ++ pp o t ++ ")"
    ppClause .pp o (absurd-clause tel ps) =
      "(" ++ pp o tel ++ " ⊢ " ++ pp o ps

    ppTerm : Pretty Term
    ppTerm .pp o (var x [])   = "#" ++ pp o x
    ppTerm .pp o (var x args) = "(#" ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (con c [])   = pp o c
    ppTerm .pp o (con c args) = "(" ++ pp o c ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (def f [])   = pp o f
    ppTerm .pp o (def f args) = "(" ++ pp o f ++ " " ++ pp o args ++ ")"
    ppTerm .pp o (lam v t) = "(λ " ++ pp o v ++ " " ++ pp o t ++ ")" -- TODO
    ppTerm .pp o (pat-lam cs args) = "λ{ " ++ pp o cs ++ " " ++ pp o args ++ "}"
    ppTerm .pp o (pi (arg (arg-info visible m) a) (abs x b)) =
      "((" ++ pp o x ++ " : " ++ pp o a ++ ") → " ++ pp o b ++ ")"
    ppTerm .pp o (pi (arg (arg-info hidden m) a) (abs x b)) =
      "({" ++ pp o x ++ " : " ++ pp o a ++ "} → " ++ pp o b ++ ")"
    ppTerm .pp o (pi (arg (arg-info instance′ m) a) (abs x b)) =
      "({{" ++ pp o x ++ " : " ++ pp o a ++ "}} → " ++ pp o b ++ ")"
    ppTerm .pp o (agda-sort s) = pp o s
    ppTerm .pp o (lit l) = pp o l
    ppTerm .pp o (meta x args) = "(" ++ pp o x ++ " " ++ pp o args ++ ")"
    ppTerm .pp o unknown = "_"
