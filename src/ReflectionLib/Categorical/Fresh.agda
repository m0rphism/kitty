module ReflectionLib.Categorical.Fresh where

open import Agda.Primitive using (Setω; Level; _⊔_) renaming (lzero to 0ℓ)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.MonadTrans
open import ReflectionLib.Categorical.MonadTC
open import ReflectionLib.Categorical.State
open import ReflectionLib.Categorical.List
open import ReflectionLib.Categorical.Traversable

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to ℕ→String)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C S S' : Set ℓ

FreshT = StateT ℕ

MonadFresh : (ℓ : Level) → Functor' ℓ → Setω
MonadFresh = MonadState ℕ

runFreshT :
  ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}}
  → FreshT {ℓ} F A → F A
runFreshT fa = proj₁ <$> runStateT fa 0

fresh-ℕ :
  ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadFresh ℓ F}}
  → F ℕ
fresh-ℕ = do
  n ← get
  modify suc
  pure n

fresh-id :
  ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadFresh ℓ F}}
  → String → F String
fresh-id s = do
  n ← fresh-ℕ
  pure (s ++ "∷" ++ ℕ→String n)

fresh-ids :
  ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadFresh ℓ F}}
  → ℕ → String → F (List String)
fresh-ids {ℓ = ℓ} {F = F} n s = forM (range₀ n) λ _ → fresh-id s

-- test : ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}} → F String
-- test = do
--   x ← unquoteTC {A = Set₃} {!!}
--   fresh-id ""
