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

-- FreshT ----------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to ℕ→String)
open import Data.String using (String; _++_)

FreshT = StateT ℕ

runFreshT : {{_ : Monad F}} → FreshT F A → F A
runFreshT fa = proj₁ <$> runStateT fa 0

fresh-ℕ : {{_ : Monad F}} → FreshT F ℕ
fresh-ℕ = do
  n ← get
  modify suc
  pure n

fresh-id : {{_ : Monad F}} → String → FreshT F String
fresh-id s = do
  n ← fresh-ℕ
  pure (s ++ ℕ→String n)
