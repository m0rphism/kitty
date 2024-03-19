module ReflectionLib.Classes.Monad where

open import Reflection using (TC) renaming (_>>=_ to _>>=TC_; return to returnTC)
open import Level using (Level; _⊔_; lower) renaming (suc to lsuc; Lift to LLift; lift to llift)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Agda.Primitive using (Setω)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C S S' : Set ℓ
    F M : Set ℓ → Set ℓ

record Functor (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixl 5 _<$>_  _<$_

  field
    map : (A → B) → (F A → F B)

  _<$>_ : (A → B) → (F A → F B)
  _<$>_ = map

  _<$_ : B → (F A → F B)
  b <$ fa = map (λ _ → b) fa

open Functor {{...}} public

record Applicative (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixl 5 _<*>_  _<*_  _*>_

  field
    {{is-functor}} : Functor F
    pure : A → F A
    _<*>_ : F (A → B) → (F A → F B)

  _<*_ : F A → F B → F A
  fa <* fb = (λ a _ → a) <$> fa <*> fb

  _*>_ : F A → F B → F B
  fa *> fb = (λ _ b → b) <$> fa <*> fb

open Applicative {{...}} public

record Monad (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixl 5  _>>=_  _=<<_  _>>_  _<<_  _>=>_  _<=<_

  field
    {{is-applicative}} : Applicative F
    _>>=_ : F A → (A → F B) → F B

  return : A → F A
  return = pure

  _=<<_ : (A → F B) → F A → F B
  f =<< fa = fa >>= f

  _>>_ : F A → F B → F B
  _>>_ = _*>_

  _<<_ : F A → F B → F A
  _<<_ = _<*_

  _>=>_ : (A → F B) → (B → F C) → (A → F C)
  (f >=> g) x = f x >>= g

  _<=<_ : (B → F C) → (A → F B) → (A → F C)
  f <=< g = g >=> f

  join : F (F A) → F A
  join ffa = ffa >>= λ x → x

open Monad {{...}} public

record MonadTrans {ℓ} (T : (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)) : Set (lsuc ℓ) where
  field
    {{is-monad}} : {{_ : Monad M}} → Monad (T M)
    lift : {{_ : Monad F}} → F A → T F A

open MonadTrans {{...}} public

-- TC --------------------------------------------------------------------------

instance
  TC-Functor : Functor (TC {ℓ})
  TC-Functor = record
    { map = λ f x → x >>=TC (λ y → returnTC (f y))
    }

  TC-Applicative : Applicative (TC {ℓ})
  TC-Applicative = record
    { pure = returnTC
    ; _<*>_ = λ ff fx → ff >>=TC λ f →
                        fx >>=TC λ x →
                        returnTC (f x)
    }

  TC-Monad : Monad (TC {ℓ})
  TC-Monad = record { _>>=_ = _>>=TC_ }

open import Reflection using (Term; Type; ErrorPart; Arg; Name; Clause; Definition; Meta)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
record MonadTC (F : ∀ {ℓ} → Set ℓ → Set ℓ) : Setω₁ where
  field
    {{is-monad}}     : Monad (F {ℓ})
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
    getContext       : F (List (Arg Type))
    extendContext    : ∀ {a} {A : Set a} → Arg Type → F A → F A
    inContext        : ∀ {a} {A : Set a} → List (Arg Type) → F A → F A
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
    withReconstructed : ∀ {a} {A : Set a} → F A → F A

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

import Agda.Builtin.Reflection as R
instance
  TC-MonadTC : MonadTC TC
  TC-MonadTC = record
    { unify             = R.unify
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

-- StateT ----------------------------------------------------------------------

record StateT (S : Set ℓ) (F : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where 
  constructor stateT
  field
    runStateT : S → F (A × S)

open StateT public

instance
  StateT-Functor : ∀ {{_ : Functor F}} → Functor (StateT S F)
  StateT-Functor = record
    { map = λ f sx → stateT λ s → map (λ (x , s) → (f x , s)) (runStateT sx s)
    }

  StateT-Applicative : ∀ {{_ : Monad F}} → Applicative (StateT S F)
  StateT-Applicative = record
    { pure = λ x → stateT λ s → pure (x , s)
    ; _<*>_ = λ ff fx → stateT λ s →
        runStateT ff s >>= λ (f , s) →
        runStateT fx s >>= λ (x , s') →
        return (f x , s')
    }

  StateT-Monad : ∀ {{_ : Monad F}} → Monad (StateT S F)
  StateT-Monad = record
    { _>>=_ = λ sx f → stateT λ s →
        runStateT sx s >>= λ (x , s) →
        runStateT (f x) s
    }

  StateT-MonadTrans : MonadTrans (StateT S)
  StateT-MonadTrans = record
    { lift = λ fa → stateT λ s → map (_, s) fa
    }

record MonadState (S : Set ℓ) (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    {{is-monad}} : Monad F
    put : S → F ⊤
    get : F S

  modify : (S → S) → F ⊤
  modify f = do
    s ← get
    put (f s)

open MonadState {{...}} public

instance
  StateT-MonadState-here : {{_ : Monad F}} → MonadState S (StateT S F)
  StateT-MonadState-here = record
    { put = λ s → stateT (λ _ → pure (tt , s))
    ; get = stateT (λ s → pure (s , s))
    }

  -- StateT-MonadState-there : {{_ : MonadState S F}} {{_ : S ≢ S'}} →
  --                           MonadState S (StateT S' F)
  -- StateT-MonadState-there = record
  --   { put = λ s → lift (put s)
  --   ; get = lift get
  --   }

  Lift-MonadTC : {S : ∀ {ℓ} → Set ℓ} → MonadTC (StateT S TC)
  Lift-MonadTC =
    record
    { unify             = λ t₁ t₂ → lift (unify t₁ t₂)
    ; typeError         = λ e → lift (typeError e)
    ; inferType         = λ t → lift (inferType t)
    ; checkType         = λ t₁ t₂ → lift (checkType t₁ t₂)
    ; normalise         = λ t → lift (normalise t)
    ; reduce            = λ t → lift (reduce t)
    ; catchTC           = λ m₁ m₂ → do
        s ← get
        let m₁ = runStateT m₁ s
        let m₂ = runStateT m₂ s
        (a , s) ← lift (catchTC m₁ m₂)
        put s
        pure a
    ; quoteTC           = λ a → lift (quoteTC a)
    ; unquoteTC         = λ t → lift (unquoteTC t)
    ; quoteωTC          = λ t → lift (quoteωTC t)
    ; getContext        = lift (getContext )
    ; extendContext     = λ arg m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (extendContext arg m)
        put s
        pure a
    ; inContext         = λ arg m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (inContext arg m)
        put s
        pure a
    ; freshName         = λ s → lift (freshName s)
    ; declareDef        = λ arg t → lift (declareDef arg t)
    ; declarePostulate  = λ arg t → lift (declarePostulate arg t)
    ; defineFun         = λ n cs → lift (defineFun n cs)
    ; getType           = λ t → lift (getType t)
    ; getDefinition     = λ n → lift (getDefinition n)
    ; blockOnMeta       = λ m → lift (blockOnMeta m)
    ; commitTC          = lift (commitTC )
    ; isMacro           = λ n → lift (isMacro n)
    ; withNormalisation = λ b m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (withNormalisation b m)
        put s
        pure a
    ; withReconstructed = λ m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (withReconstructed m)
        put s
        pure a
    ; debugPrint        = λ s n es → lift (debugPrint s n es)
    ; onlyReduceDefs    = λ ns m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (onlyReduceDefs ns m)
        put s
        pure a
    ; dontReduceDefs    = λ ns m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (dontReduceDefs ns m)
        put s
        pure a
    ; noConstraints     = λ m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (noConstraints m)
        put s
        pure a
    ; runSpeculative    = λ m → do
        s ← get
        let m = (λ ((a , f) , s) → ((a , s) , f)) <$> runStateT m s
        (a , s) ← lift (runSpeculative m)
        put s
        pure a
    }

-- FreshT ----------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to ℕ→String)
open import Data.String using (String; _++_)
open import Function using (_∘_; _$_)

FreshT : ∀ {ℓ} → (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)
FreshT = StateT (LLift _ ℕ)

runFreshT : {{_ : Monad F}} → FreshT F A → F A
runFreshT fa = proj₁ <$> runStateT fa (llift 0)

fresh-ℕ : {{_ : Monad F}} → FreshT F ℕ
fresh-ℕ = do
  n ← get
  modify (llift ∘ suc ∘ lower)
  pure $ lower n

fresh-id : {{_ : Monad F}} → String → FreshT F String
fresh-id s = do
  n ← fresh-ℕ
  pure (s ++ ℕ→String n)

test : FreshT TC String
test = do
  x ← unquoteTC {A = Set} {!!}
  fresh-id ""
