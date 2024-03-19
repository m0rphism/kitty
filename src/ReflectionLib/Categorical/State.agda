-- Disable deprecation warning from forwarding the deprecated interfaces:
-- - onlyReduceDefs (replaced by withReduceDefs)
-- - dontReduceDefs (replaced by withReduceDefs)
{-# OPTIONS -WnoUserWarning #-}

module ReflectionLib.Categorical.State where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Agda.Primitive using (Setω; Level; _⊔_) renaming (lzero to 0ℓ)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.MonadTrans
open import ReflectionLib.Categorical.MonadTC

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C S S' : Set ℓ

record StateT (S : Set ℓ₁) {ℓ₂} (F : ∀ {ℓ} → Set ℓ → Set (ℓ ⊔ ℓ₂)) {ℓ} (A : Set ℓ)
         : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where 
  constructor stateT
  field
    runStateT : S → F (A × S)

open StateT public

instance
  StateT-Functor :
    ∀ {S : Set ℓ₁} {F : Functor' ℓ₂} {{_ : Functor ℓ₂ F}}
    → Functor (ℓ₁ ⊔ ℓ₂) (StateT S {ℓ₂ = ℓ₂} F)
  StateT-Functor = record
    { map = λ f sx → stateT λ s → map (λ (x , s) → (f x , s)) (runStateT sx s)
    }

  StateT-Applicative :
    ∀ {S : Set ℓ₁} {F : Functor' ℓ₂} {{_ : Monad ℓ₂ F}}
    → Applicative (ℓ₁ ⊔ ℓ₂) (StateT S {ℓ₂ = ℓ₂} F)
  StateT-Applicative = record
    { pure = λ x → stateT λ s → pure (x , s)
    ; _<*>_ = λ ff fx → stateT λ s →
        runStateT ff s >>= λ (f , s) →
        runStateT fx s >>= λ (x , s') →
        return (f x , s')
    }

  StateT-Monad :
    ∀ {S : Set ℓ₁} {F : Functor' ℓ₂} {{_ : Monad ℓ₂ F}}
    → Monad (ℓ₁ ⊔ ℓ₂) (StateT S {ℓ₂ = ℓ₂} F)
  StateT-Monad = record
    { _>>=_ = λ sx f → stateT λ s →
        runStateT sx s >>= λ (x , s) →
        runStateT (f x) s
    }

  StateT-MonadTrans :
    ∀ {S : Set ℓ₁}
    → MonadTrans ℓ₂ (ℓ₁ ⊔ ℓ₂) (StateT S)
  StateT-MonadTrans = record
    { lift = λ fa → stateT λ s → map (_, s) fa
    }

record MonadState {ℓ₁} (S : Set ℓ₁) ℓ₂ (F : Functor' ℓ₂) : Setω where
  field
    put : S → F {ℓ₂} ⊤
    get : F S

  modify : {{_ : Monad ℓ₂ F}} → (S → S) → F {ℓ₂} ⊤
  modify f = do
    s ← get
    put (f s)

open MonadState {{...}} public

instance
  StateT-MonadState-here :
    ∀ {S : Set ℓ₁}
      {F : Functor' ℓ₂}
      {{_ : Monad ℓ₂ F}}
    → MonadState S (ℓ₁ ⊔ ℓ₂) (StateT S {ℓ₂} F)
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

  Lift-MonadTC :
    ∀ {ℓ₁} {S : Set ℓ₁}
    → MonadTC ℓ₁ (λ {ℓ} → StateT S TC)
  Lift-MonadTC =
    record
    { liftTC            = λ ma → lift (liftTC ma)
    ; unify             = λ t₁ t₂ → lift (unify t₁ t₂)
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
    ; extendContext     = λ x arg m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (extendContext x arg m)
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
    ; withReconstructed = λ b m → do
        s ← get
        let m = runStateT m s
        (a , s) ← lift (withReconstructed b m)
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
