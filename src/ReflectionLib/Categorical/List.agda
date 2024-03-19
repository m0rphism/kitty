module ReflectionLib.Categorical.List where

open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)

open import ReflectionLib.Categorical.Functor
open import ReflectionLib.Categorical.Applicative
open import ReflectionLib.Categorical.Monad
open import ReflectionLib.Categorical.Monoid
open import ReflectionLib.Categorical.Foldable
open import ReflectionLib.Categorical.Traversable

open import Data.List as List using (_++_)
open import Data.List using (List; []; _∷_) public
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; _$_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ' a b e : Level
  A B E : Set ℓ

_<*>-List_ : List (A → B) → List A → List B
fs <*>-List xs = List.cartesianProductWith (λ f x → f x) fs xs

_>>=-List_ : List A → (A → List B) → List B
xs >>=-List f = List.concat (List.map f xs)

traverse-List : {F : Functor' ℓ'} {{_ : Applicative ℓ' F}}
              → (A → F B) → List A → F (List B)
traverse-List f []       = pure []
traverse-List f (x ∷ xs) = _∷_ <$> f x <*> traverse-List f xs

instance
  List-Functor : Functor 0ℓ List
  List-Functor = record { map = List.map }

  List-Applicative : Applicative 0ℓ List
  List-Applicative = record { pure  = λ x → x ∷ [] ; _<*>_ = _<*>-List_}

  List-Monad : Monad 0ℓ List
  List-Monad = record { _>>=_ = _>>=-List_ }

  List-Monoid : Monoid (List A)
  List-Monoid = record { 1M = [] ; _⊗_ = _++_ }

  List-Foldable : Foldable 0ℓ List
  List-Foldable = record { foldr = List.foldr }

  List-Traversable : Traversable 0ℓ List
  List-Traversable = record { traverse = traverse-List }

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)

range₀ : ℕ → List ℕ
range₀ n = f n 0 where
  f : ℕ → ℕ → List ℕ
  f zero    m = []
  f (suc n) m = m ∷ f n (suc m)

range : ℕ → ℕ → List ℕ
range begin end = List.map (begin +_) (range₀ (end ∸ begin))

enumerate : List A → List (ℕ × A) 
enumerate xs = List.zip (range₀ (List.length xs)) xs

pattern [_] a = a ∷ []
pattern [_;_] a b = a ∷ b ∷ []
pattern [_;_;_] a b c = a ∷ b ∷ c ∷ []
pattern [_;_;_;_] a b c d = a ∷ b ∷ c ∷ d ∷ []
pattern [_;_;_;_;_] a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []
pattern [_;_;_;_;_;_] a b c d e f = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []
pattern [_;_;_;_;_;_;_] a b c d e f g = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []
pattern [_;_;_;_;_;_;_;_] a b c d e f g h = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []
pattern [_;_;_;_;_;_;_;_;_] a b c d e f g h i = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []
pattern [_;_;_;_;_;_;_;_;_;_] a b c d e f g h i j = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ []
pattern [_;_;_;_;_;_;_;_;_;_;_] a b c d e f g h i j k = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ []
pattern [_;_;_;_;_;_;_;_;_;_;_;_] a b c d e f g h i j k l = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ []
