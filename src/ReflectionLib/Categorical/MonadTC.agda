-- Disable deprecation warning from forwarding the deprecated interfaces:
-- - onlyReduceDefs (replaced by withReduceDefs)
-- - dontReduceDefs (replaced by withReduceDefs)
{-# OPTIONS -WnoUserWarning #-}

module ReflectionLib.Categorical.MonadTC where

open import Agda.Primitive using (Setω; Level; _⊔_) renaming (lzero to 0ℓ)
open import Reflection using () renaming (_>>=_ to _>>=TC_)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Reflection using (Term; Type; ErrorPart; Arg; Name; Clause; Definition; Meta)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
import Agda.Builtin.Reflection as R
open import Reflection using (TC) public

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

record MonadTC ℓ (F : Functor' ℓ) : Setω₁ where
  field
    liftTC           : TC A → F A
    unify            : Term → Term → F ⊤₀
    typeError        : List ErrorPart → F A
    inferType        : Term → F Type
    checkType        : Term → Type → F Term
    normalise        : Term → F Term
    reduce           : Term → F Term
    catchTC          : ∀ {a} {A : Set a} → F A → F A → F A
    quoteTC          : ∀ {a} {A : Set a} → A → F Term
    unquoteTC        : ∀ {a} {A : Set a} → Term → F A
    quoteωTC         : ∀ {A : Setω} → A → F Term
    getContext       : F (List (String × Arg Type))
    extendContext    : ∀ {a} {A : Set a} → String → Arg Type → F A → F A
    inContext        : ∀ {a} {A : Set a} → List (String × Arg Type) → F A → F A
    freshName        : String → F Name
    declareDef       : Arg Name → Type → F ⊤₀
    declarePostulate : Arg Name → Type → F ⊤₀
    defineFun        : Name → List Clause → F ⊤₀
    getType          : Name → F Type
    getDefinition    : Name → F Definition
    blockOnMeta      : ∀ {a} {A : Set a} → Meta → F A
    commitTC         : F ⊤₀
    isMacro          : Name → F Bool

    -- If the argument is 'true' makes the following primitives also normalise
    -- their results: inferType, checkType, quoteTC, getType, and getContext
    withNormalisation : ∀ {a} {A : Set a} → Bool → F A → F A

    -- Makes the following primitives to reconstruct hidden arguments
    -- getDefinition, normalise, reduce, inferType, checkType and getContext
    withReconstructed : ∀ {a} {A : Set a} → Bool → F A → F A

    -- Prints the third argument if the corresponding verbosity level is turned
    -- on (with the -v flag to Agda).
    debugPrint : String → ℕ → List ErrorPart → F ⊤₀

    -- Only allow reduction of specific definitions while executing the TC computation
    onlyReduceDefs : ∀ {a} {A : Set a} → List Name → F A → F A

    -- Don't allow reduction of specific definitions while executing the TC computation
    dontReduceDefs : ∀ {a} {A : Set a} → List Name → F A → F A

    -- Fail if the given computation gives rise to new, unsolved
    -- "blocking" constraints.
    noConstraints : ∀ {a} {A : Set a} → F A → F A

    -- Run the given TC action and return the first component. Resets to
    -- the old TC state if the second component is 'false', or keep the
    -- new TC state if it is 'true'.
    runSpeculative : ∀ {a} {A : Set a} → F (Σ A λ _ → Bool) → F A

open MonadTC {{...}} public

-- TC --------------------------------------------------------------------------

instance
  TC-Functor : Functor 0ℓ TC
  TC-Functor = record
    { map = λ f x → x >>=TC (λ y → R.returnTC (f y))
    }

  TC-Applicative : Applicative 0ℓ TC
  TC-Applicative = record
    { pure = R.returnTC
    ; _<*>_ = λ ff fx → ff >>=TC λ f →
                        fx >>=TC λ x →
                        R.returnTC (f x)
    }

  TC-Monad : Monad 0ℓ TC
  TC-Monad = record { _>>=_ = _>>=TC_ }

  TC-MonadTC : MonadTC 0ℓ TC
  TC-MonadTC = record
    { liftTC            = λ ma → ma
    ; unify             = R.unify
    ; typeError         = R.typeError
    ; inferType         = R.inferType
    ; checkType         = R.checkType
    ; normalise         = R.normalise
    ; reduce            = R.reduce
    ; catchTC           = R.catchTC
    ; quoteTC           = R.quoteTC
    ; unquoteTC         = R.unquoteTC
    ; quoteωTC          = R.quoteωTC
    ; getContext        = R.getContext
    ; extendContext     = R.extendContext
    ; inContext         = R.inContext
    ; freshName         = R.freshName
    ; declareDef        = R.declareDef
    ; declarePostulate  = R.declarePostulate
    ; defineFun         = R.defineFun
    ; getType           = R.getType
    ; getDefinition     = R.getDefinition
    ; blockOnMeta       = R.blockOnMeta
    ; commitTC          = R.commitTC
    ; isMacro           = R.isMacro
    ; withNormalisation = R.withNormalisation
    ; withReconstructed = R.withReconstructed
    ; debugPrint        = R.debugPrint
    ; onlyReduceDefs    = R.onlyReduceDefs
    ; dontReduceDefs    = R.dontReduceDefs
    ; noConstraints     = R.noConstraints
    ; runSpeculative    = R.runSpeculative
    }

  {-# WARNING_ON_USAGE MonadTC.onlyReduceDefs "DEPRECATED: Use `withReduceDefs` instead of `onlyReduceDefs`" #-}
  {-# WARNING_ON_USAGE MonadTC.dontReduceDefs "DEPRECATED: Use `withReduceDefs` instead of `dontReduceDefs`" #-}
