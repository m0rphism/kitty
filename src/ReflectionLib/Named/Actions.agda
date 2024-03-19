module ReflectionLib.Named.Actions where

open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Categorical
open import Agda.Primitive using (Level; Setω) renaming (lzero to 0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)

private variable
  ℓ : Level
  F : Functor' ℓ

quoteTC' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}}
           {a} {A : Set a} → A → F Term'
quoteTC' x = to-named =<< quoteTC x 

quoteωTC' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}}
            → {A : Setω} → A → F Term'
quoteωTC' x = to-named =<< quoteωTC x 

unquoteTC' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}}
             {a} {A : Set a} → Term' → F A
unquoteTC' x = unquoteTC =<< to-debruijn x

getType' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}}
           → Name → F Term'
getType' x = to-named =<< getType x

defdecFun' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}}
             → Arg Name → Type' → List Clause' → F ⊤
defdecFun' a t cs = liftTC do
  declareDef a =<< to-debruijn t
  defineFun (arg-val a) =<< to-debruijn cs

quoteNormTC' : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}}
                 {a} {A : Set a} → A → F Term'
quoteNormTC' x = withNormalisation true (quoteTC' x)

term→name : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}}
            → Term' → F Name
term→name (def nm args) = return nm
term→name (con nm args) = return nm
term→name t = liftTC (failStr "Term is not a Name.")

