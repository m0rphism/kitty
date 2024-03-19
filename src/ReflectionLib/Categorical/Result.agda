module ReflectionLib.Categorical.Result where

open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.Monoid
open import ReflectionLib.Categorical.Foldable
open import ReflectionLib.Categorical.Traversable

open import Function using (_∘_; _$_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ' a b e : Level
  A B E E' : Set ℓ

data Result (A : Set a) (E : Set e) : Set (a ⊔ e) where
  ok  : A → Result A E
  err : E → Result A E

mapErr : (E → E') → Result A E → Result A E'
mapErr f (ok x) = ok x
mapErr f (err e) = err (f e)

map-Result : (A → B) → Result A E → Result B E
map-Result f (ok a) = ok (f a)
map-Result f (err e) = err e

case-Result : Result A E → (A → B) → (E → B) → B
case-Result (ok x)  f g = f x
case-Result (err x) f g = g x

_<*>-Result_ : Result (A → B) E → Result A E → Result B E
ok f  <*>-Result ok x  = ok (f x)
ok f  <*>-Result err e = err e
err e <*>-Result _     = err e

_>>=-Result_ : Result A E → (A → Result B E) → Result B E
ok a  >>=-Result f = f a
err e >>=-Result f = err e

_⊗-Result_ : {{_ : Monoid A}} → Result A E → Result A E → Result A E
ok x  ⊗-Result ok y  = ok (x ⊗ y)
ok x  ⊗-Result err e = err e
err e ⊗-Result _     = err e

foldr-Result : (A → B → B) → B → Result A E → B
foldr-Result f b0 (ok x) = f x b0
foldr-Result f b0 (err _) = b0

traverse-Result : {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
                → (A → F B) → Result A E → F (Result B E)
traverse-Result f (ok x) = map ok (f x)
traverse-Result f (err e) = pure (err e)

instance
  Result-Functor : ∀ {E : Set e} → Functor e (λ A → Result A E)
  Result-Functor = record { map = map-Result }

  Result-Applicative : ∀ {E : Set e} → Applicative e (λ A → Result A E)
  Result-Applicative = record { pure  = ok ; _<*>_ = _<*>-Result_}

  Result-Monad : ∀ {E : Set e} → Monad e (λ A → Result A E)
  Result-Monad = record { _>>=_ = _>>=-Result_ }

  Result-Monoid : {{_ : Monoid A}} → Monoid (Result A E)
  Result-Monoid = record { 1M = ok 1M ; _⊗_ = _⊗-Result_ }

  Result-Foldable : ∀ {E : Set e} → Foldable e (λ A → Result A E)
  Result-Foldable = record { foldr = foldr-Result }

  Result-Traversable : ∀ {E : Set e} → Traversable e (λ A → Result A E)
  Result-Traversable = record { traverse = traverse-Result }


record ResultT (E : Set e) (F : Functor' ℓ) (A : Set a) : Set (a ⊔ ℓ ⊔ e) where
  constructor mkResultT
  field
    runResultT : F (Result A E)

open ResultT public

map-ResultT :
  ∀ {E : Set e} {F : Functor' ℓ} {{_ : Functor ℓ F}}
  → (A → B)
  → ResultT {ℓ = ℓ} E F A
  → ResultT {ℓ = ℓ} E F B
map-ResultT f r = mkResultT (map (map f) (runResultT r))

_<*>-ResultT_ :
  ∀ {E : Set e} {F : Functor' ℓ} {{_ : Applicative ℓ F}}
  → ResultT {ℓ = ℓ} E F (A → B)
  → ResultT {ℓ = ℓ} E F A
  → ResultT {ℓ = ℓ} E F B
rf <*>-ResultT rx = mkResultT (_<*>_ <$> runResultT rf <*> runResultT rx)

_>>=-ResultT_ :
  ∀ {E : Set e} {F : Functor' ℓ} {{_ : Monad ℓ F}}
  → ResultT {ℓ = ℓ} E F A
  → (A → ResultT {ℓ = ℓ} E F B)
  → ResultT {ℓ = ℓ} E F B
rx >>=-ResultT f = mkResultT $ runResultT rx >>= λ where (ok x)  → runResultT (f x)
                                                         (err e) → return (err e)

instance
  ResultT-Functor :
    ∀ {E : Set e} {F : Functor' ℓ} {{_ : Functor ℓ F}}
    → Functor (e ⊔  ℓ) (ResultT E F)
  ResultT-Functor = record { map = map-ResultT }

  ResultT-Applicative :
    ∀ {E : Set e} {F : Functor' ℓ} {{_ : Applicative ℓ F}}
    → Applicative (e ⊔  ℓ) (ResultT E F)
  ResultT-Applicative = record { pure  = λ x → mkResultT (pure (ok x)) ; _<*>_ = _<*>-ResultT_}

  ResultT-Monad :
    ∀ {E : Set e} {F : Functor' ℓ} {{_ : Monad ℓ F}}
    → Monad (e ⊔  ℓ) (ResultT E F)
  ResultT-Monad = record { _>>=_ = _>>=-ResultT_ }
