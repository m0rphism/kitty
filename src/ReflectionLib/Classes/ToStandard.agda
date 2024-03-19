module ReflectionLib.Classes.ToStandard where

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
open import Level using (Level)
open import Function using (_$_)

open import ReflectionLib.Named.Syntax
open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Categorical.Result
open import ReflectionLib.Classes.Pretty

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

-- Clause Generation -----------------------------------------------------------

-- Debuijn Vars are only used for local variables -> no context for clauses
--   (not true for pattern lambdas)
-- We can duplicate the AST with local names instead of indices and transform.

SResult : Set ℓ → Set ℓ
SResult A = Result A (List String)

with-trace : {{_ : Pretty A}} → A → SResult B → SResult B
with-trace a (ok x) = ok x
with-trace a (err ss) = 
  err $ _∷ ss $ "In context: " ++ pp strip-mod a ++ "\n"

record ToDebruijn (Src : Set) (Tgt : Set) : Set₁ where
  field
    to-debruijn : List String → Src → SResult Tgt

  to-debruijn-trace : {{_ : Pretty Src}} → List String → Src → SResult Tgt
  to-debruijn-trace env src = with-trace src (to-debruijn env src)
