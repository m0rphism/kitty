module ReflectionLib.Standard.Actions where

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

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Classes.Pretty

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ

open import Agda.Builtin.Reflection public using
  ( TC; returnTC; bindTC; unify; typeError; inferType; checkType; normalise
  ; reduce; catchTC; quoteTC; unquoteTC; quoteωTC; getContext; extendContext
  ; inContext; freshName; declareDef; declarePostulate; defineFun; getType
  ; getDefinition; blockOnMeta; commitTC; isMacro; withNormalisation
  ; withReconstructed; debugPrint; onlyReduceDefs; dontReduceDefs
  ; noConstraints; runSpeculative )

open import Agda.Builtin.Reflection renaming (returnTC to return; bindTC to _>>=_)

-- For splicing, e.g.:
--   t'' ← quoteTC ({m n : ℕ} → unquote (unifyM (Sub' m n)))
unifyM : TC Term → (Term → TC ⊤)
unifyM mt = λ hole → do
  t ← mt
  unify t hole

⟪_⟫ : TC Term → (Term → TC ⊤)
⟪_⟫ = unifyM

⟦_⟧ : Term → (Term → TC ⊤)
⟦ t ⟧ = unifyM (return t)

normaliseTC : A → TC A
normaliseTC {A = A} x = do
  x ← quoteTC x
  x ← normalise x
  x ← unquoteTC {A = A} x
  return x

quoteNormTC : A → TC Term
quoteNormTC x = withNormalisation true (quoteTC x)

term→name : Term → TC Name
term→name (def nm args) = return nm
term→name (con nm args) = return nm
term→name t = failStr "Term is not a Name."

quoteNameTC : A → TC Name
quoteNameTC a = do
  t ← quoteNormTC a
  term→name t

