module ReflectionLib.Standard.Syntax where

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

open import Level using (Level)
open import Function using (_$_)

open import Agda.Builtin.Reflection public using
  ( Associativity; Precedence; Fixity; Visibility; Relevance; Quantity; Modality
  ; ArgInfo; Arg; Abs; Literal; Term; Type; Sort; Pattern; Clause; Definition
  ; ErrorPart
  )

open Associativity public using (left-assoc; right-assoc; non-assoc)
open Precedence    public using (related; unrelated)
open Fixity        public using (fixity)
open Visibility    public using (visible; hidden; instance′)
open Relevance     public using (relevant; irrelevant)
open Quantity      public using (quantity-0; quantity-ω)
open Modality      public using (modality)
open ArgInfo       public using (arg-info)
open Arg           public using (arg)
open Abs           public using (abs)
open Literal       public using (nat; word64; float; char; string; name; meta)
open Term          public using (var; con; def; lam; pat-lam; pi; agda-sort; lit; meta; unknown)
open Sort          public using (set; lit; prop; propLit; inf; unknown)
open Pattern       public using (con; dot; var; lit; proj; absurd)
open Clause        public using (clause; absurd-clause)
open Definition    public using (function; data-type; record-type; data-cons; axiom; prim-fun)
open ErrorPart     public using (strErr; termErr; nameErr)

open import Agda.Builtin.Reflection public using
  ( Name; primQNameEquality; primQNameLess; primShowQName; primQNameFixity
  ; primQNameToWord64s )

open import Agda.Builtin.Reflection public using
  ( Meta; primMetaEquality; primMetaLess; primShowMeta; primMetaToNat )

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

open import Agda.Builtin.Reflection public using (Telescope)
-- Telescope : Set
-- Telescope = List (String × Arg Term)

pattern arg′ v a = arg (arg-info v (modality relevant quantity-ω)) a
pattern argᵥ a = arg (arg-info visible (modality relevant quantity-ω)) a
pattern argₕ a = arg (arg-info hidden (modality relevant quantity-ω)) a
pattern argᵢ a = arg (arg-info instance′ (modality relevant quantity-ω)) a

ctors : Definition → List Name
ctors (data-type pars cs) = cs
ctors _ = []

infixr 3 _⇒_
_⇒_ : Term → Term → Term
t₁ ⇒ t₂ = pi (argᵥ t₁) (abs "_" t₂)

arg-val : Arg A → A
arg-val (arg _ v) = v

arg-inf : Arg A → ArgInfo
arg-inf (arg i _) = i


