module ReflectionLib.Standard.ActionsClass where

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

open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Categorical
open import ReflectionLib.Standard.Syntax
import ReflectionLib.Standard.Actions as A

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  F : Functor' ℓ

module _ {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} where

  defdecFun : Arg Name → Type → List Clause → F ⊤
  defdecFun a t cs = do
    declareDef a t
    defineFun (arg-val a) cs

  defdecFunMock : Arg Name → Type → List Clause → F ⊤
  defdecFunMock a t cs = do
    e ← quoteTC (a , t , cs)
    declareDef (argᵥ (arg-val a)) (quoteTerm (Arg Name × Type × List Clause))
    let c = clause [] [] e
    defineFun (arg-val a) (c ∷ [])

  -- For splicing, e.g.:
  --   t'' ← quoteTC ({m n : ℕ} → unquote (unifyM (Sub' m n)))
  unifyM : F Term → (Term → F ⊤)
  unifyM mt = λ hole → do
    t ← mt
    unify t hole

  ⟪_⟫ : F Term → (Term → F ⊤)
  ⟪_⟫ = unifyM

  ⟦_⟧ : Term → (Term → F ⊤)
  ⟦ t ⟧ = unifyM (return t)

  normaliseTC : A → F A
  normaliseTC x = liftTC (A.normaliseTC x)

  quoteNormTC : A → F Term
  quoteNormTC x = withNormalisation true (quoteTC x)

  term→name : Term → F Name
  term→name t = liftTC $ A.term→name t

  quoteNameTC : A → F Name
  quoteNameTC a = liftTC $ A.quoteNameTC a
