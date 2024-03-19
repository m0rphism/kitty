module ReflectionLib.Classes.Monad where

open import Reflection using (TC) renaming (_>>=_ to _>>=TC_; return to returnTC)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C S S' : Set ℓ
    F M : Set ℓ₁ → Set ℓ₂

record Functor (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  infixl 5 _<$>_  _<$_

  field
    map : (A → B) → (F A → F B)

  _<$>_ : (A → B) → (F A → F B)
  _<$>_ = map

  _<$_ : B → (F A → F B)
  b <$ fa = map (λ _ → b) fa

open Functor {{...}} public

record Applicative (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
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
open import Agda.Primitive using (Setω)

record MonadTrans {ℓ} (T : (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)) : Setω where
  field
    {{is-monads}} : {{_ : Monad M}} → Monad (T M)
    lift : {{_ : Monad F}} → F A → T F A

open MonadTrans {{...}} public

record MonadUnlift {ℓ} (T : (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)) : Setω where
  field
    {{is-monad-trans}} : MonadTrans T
    unlift : {{_ : Monad F}} → T F A → T F (F A)

open MonadUnlift {{...}} public

record MonadUnlift' {ℓ} (T : (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)) : Setω where
  field
    {{is-monad-trans}} : MonadTrans T
    unlift' : {{_ : Monad F}} → ((∀ {A} → T F A → F A) → T F B) → F B

open MonadUnlift' {{...}} public

record MonadUnlift'' {ℓ} (T : (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)) : Setω where
  field
    {{is-monad-trans}} : MonadTrans T
    unlift'' : {{_ : Monad F}} → T F A → T F (F (T F A))

open MonadUnlift'' {{...}} public

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
open import Agda.Primitive using (Setω)
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

  Lift-MonadTC : ∀ {T : ∀ {ℓ} → (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ)}
                   {F : ∀ {ℓ} → Set ℓ → Set ℓ}
                   {{MU : ∀ {ℓ} → MonadUnlift (T {ℓ})}}
                   {{MU' : ∀ {ℓ} → MonadUnlift' (T {ℓ})}}
                   {{MU'' : ∀ {ℓ} → MonadUnlift'' (T {ℓ})}}
                   {{MTC : MonadTC F}}
                 → MonadTC (T F)
  Lift-MonadTC {T = T} {{MU}} {{MU'}} {{MU''}} {{MTC}} =
    let MT {ℓ} = MonadUnlift.is-monad-trans (MU {ℓ}) in
    let MTF {ℓ} = MonadTrans.is-monads MT {{MonadTC.is-monad MTC {ℓ}}} in
    record
    { is-monad          = MTF
    ; unify             = let instance _ = MT in let instance _ = MTF in
                          λ t₁ t₂ → lift (MonadTC.unify MTC t₁ t₂)
    ; typeError         = let instance _ = MT in let instance _ = MTF in
                          λ e → lift (MonadTC.typeError MTC e)
    ; inferType         = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.inferType MTC t)
    ; checkType         = let instance _ = MT in let instance _ = MTF in
                          λ t₁ t₂ → lift (MonadTC.checkType MTC t₁ t₂)
    ; normalise         = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.normalise MTC t)
    ; reduce            = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.reduce MTC t)
    ; catchTC           = let instance _ = MT in let instance _ = MTF in
                          λ m₁ m₂ → do m₁ ← unlift m₁; m₂ ← unlift m₂; lift (MonadTC.catchTC MTC m₁ m₂)
    ; quoteTC           = let instance _ = MT in let instance _ = MTF in
                          λ a → lift (MonadTC.quoteTC MTC a)
    ; unquoteTC         = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.unquoteTC MTC t)
    ; quoteωTC          = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.quoteωTC MTC t)
    ; getContext        = let instance _ = MT in let instance _ = MTF in
                          lift (MonadTC.getContext MTC)
    ; extendContext     = let instance _ = MT in let instance _ = MTF in
                          λ arg m → do m ← unlift m; lift (MonadTC.extendContext MTC arg m)
    ; inContext         = let instance _ = MT in let instance _ = MTF in
                          λ arg m → do m ← unlift m; lift (MonadTC.inContext MTC arg m)
    ; freshName         = let instance _ = MT in let instance _ = MTF in
                          λ s → lift (MonadTC.freshName MTC s)
    ; declareDef        = let instance _ = MT in let instance _ = MTF in
                          λ arg t → lift (MonadTC.declareDef MTC arg t)
    ; declarePostulate  = let instance _ = MT in let instance _ = MTF in
                          λ arg t → lift (MonadTC.declarePostulate MTC arg t)
    ; defineFun         = let instance _ = MT in let instance _ = MTF in
                          λ n cs → lift (MonadTC.defineFun MTC n cs)
    ; getType           = let instance _ = MT in let instance _ = MTF in
                          λ t → lift (MonadTC.getType MTC t)
    ; getDefinition     = let instance _ = MT in let instance _ = MTF in
                          λ n → lift (MonadTC.getDefinition MTC n)
    ; blockOnMeta       = let instance _ = MT in let instance _ = MTF in
                          λ m → lift (MonadTC.blockOnMeta MTC m)
    ; commitTC          = let instance _ = MT in let instance _ = MTF in
                          lift (MonadTC.commitTC MTC)
    ; isMacro           = let instance _ = MT in let instance _ = MTF in
                          λ n → lift (MonadTC.isMacro MTC n)
    ; withNormalisation = let instance _ = MT in let instance _ = MTF in
                          λ b m → do m ← unlift m; lift (MonadTC.withNormalisation MTC b m)
    ; withReconstructed = let instance _ = MT in let instance _ = MTF in
                          λ m → do m ← unlift m; lift (MonadTC.withReconstructed MTC m)
    ; debugPrint        = let instance _ = MT in let instance _ = MTF in
                          λ s n es → lift (MonadTC.debugPrint MTC s n es)
    ; onlyReduceDefs    = let instance _ = MT in let instance _ = MTF in
                          λ ns m → do m ← unlift m; lift (MonadTC.onlyReduceDefs MTC ns m)
    ; dontReduceDefs    = let instance _ = MT in let instance _ = MTF in
                          λ ns m → do m ← unlift m; lift (MonadTC.dontReduceDefs MTC ns m)
    ; noConstraints     = let instance _ = MT in let instance _ = MTF in
                          λ m → do
                            m ← unlift'' m
                            join (lift (MonadTC.noConstraints MTC m))
    ; runSpeculative    = let instance _ = MT in let instance _ = MTF in
                          λ m → do
                            let m' = unlift' λ f → lift (f m)
                            lift (MonadTC.runSpeculative MTC m')
    }

-- StateT ----------------------------------------------------------------------

record StateT (S : Set ℓ) (F : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where 
  constructor stateT
  field
    runStateT : S → F (A × S)

open StateT

instance
  StateT-Functor : {{_ : Functor F}} → Functor (StateT S F)
  StateT-Functor = record
    { map = λ f sx → stateT λ s → map (λ (x , s) → (f x , s)) (runStateT sx s)
    }

  StateT-Applicative : {{_ : Monad F}} → Applicative (StateT S F)
  StateT-Applicative = record
    { pure = λ x → stateT λ s → pure (x , s)
    ; _<*>_ = λ ff fx → stateT λ s →
        runStateT ff s >>= λ (f , s) →
        runStateT fx s >>= λ (x , s') →
        return (f x , s')
    }

  StateT-Monad : {{_ : Monad F}} → Monad (StateT S F)
  StateT-Monad = record
    { _>>=_ = λ sx f → stateT λ s →
        runStateT sx s >>= λ (x , s) →
        runStateT (f x) s
    }

  StateT-MonadTrans : MonadTrans (StateT S)
  StateT-MonadTrans = record
    { lift = λ fa → stateT λ s → map (_, s) fa
    }

  StateT-MonadUnlift : MonadUnlift (StateT S)
  StateT-MonadUnlift = record
    { unlift = λ tfa → stateT λ s → {!runStateT tfa s!}
    }

  StateT-MonadUnlift' : MonadUnlift' (StateT S)
  StateT-MonadUnlift' = record
    { unlift' = λ f → {!f!}
    }

  StateT-MonadUnlift'' : MonadUnlift'' (StateT S)
  StateT-MonadUnlift'' = record
    { unlift'' = λ {{MF}} tfa → stateT λ s →
        pure (map (λ (a , s) → stateT λ _ → pure (a , s)) (runStateT tfa s) , s)
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

open MonadState {{...}}

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

-- -- FreshT ----------------------------------------------------------------------

-- open import Data.Nat using (ℕ; zero; suc)
-- open import Data.Nat.Show renaming (show to ℕ→String)
-- open import Data.String using (String; _++_)

-- FreshT = StateT ℕ

-- runFreshT : {{_ : Monad F}} → FreshT F A → F A
-- runFreshT fa = proj₁ <$> runStateT fa 0

-- fresh-ℕ : {{_ : Monad F}} → FreshT F ℕ
-- fresh-ℕ = do
--   n ← get
--   modify suc
--   pure n

-- fresh-id : {{_ : Monad F}} → String → FreshT F String
-- fresh-id s = do
--   n ← fresh-ℕ
--   pure (s ++ ℕ→String n)
