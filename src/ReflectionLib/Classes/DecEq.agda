module ReflectionLib.Classes.DecEq where

open import Relation.Binary.Structures using (IsDecEquivalence) public
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence) public
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.TypeClasses using (_≟_; _≤?_) public
open import Relation.Nullary public using (Dec; yes; no)
open import Agda.Primitive using (Level)

private variable
  ℓ : Level
  A B C : Set ℓ

DecEq : ∀ {ℓ} → Set ℓ → Set ℓ
DecEq A = IsDecEquivalence  {A = A} _≡_

instance
  import Data.Nat as Nat
  DecEq-ℕ : DecEq Nat.ℕ
  DecEq-ℕ = isDecEquivalence Nat._≟_

  import Data.Fin as Fin
  DecEq-Fin : ∀ {n} → DecEq (Fin.Fin n)
  DecEq-Fin = isDecEquivalence Fin._≟_

  import Data.String as String
  DecEq-String : DecEq String.String
  DecEq-String = isDecEquivalence String._≟_

  import Data.Bool as Bool
  DecEq-Bool : DecEq Bool.Bool
  DecEq-Bool = isDecEquivalence Bool._≟_

  import Data.List as List
  import Data.List.Properties as ListP
  DecEq-List : ⦃ _ : DecEq A ⦄ → DecEq (List.List A)
  DecEq-List = isDecEquivalence (ListP.≡-dec _≟_)

  import Data.Product as Product
  import Data.Product.Properties as ProductP
  DecEq-Σ : ∀ {ℓ} {A : Set ℓ} {ℓ'} {B : A → Set ℓ'}
              ⦃ _ : DecEq A ⦄
              ⦃ _ : ∀ {a} → DecEq (B a) ⦄
            → DecEq (Product.Σ A B)
  DecEq-Σ = isDecEquivalence (ProductP.≡-dec _≟_ _≟_)
