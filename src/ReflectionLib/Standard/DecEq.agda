module ReflectionLib.Standard.DecEq where

open import ReflectionLib.Standard.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Primitive using (Level)

open import ReflectionLib.Classes.DecEq public
open import Reflection.Instances public using
 ( Lit-≡-isDecEquivalence
 ; Name-≡-isDecEquivalence
 ; Meta-≡-isDecEquivalence
 ; Visibility-≡-isDecEquivalence
 ; Relevance-≡-isDecEquivalence
 ; ArgInfo-≡-isDecEquivalence
 ; Pattern-≡-isDecEquivalence
 ; Clause-≡-isDecEquivalence
 ; Term-≡-isDecEquivalence
 ; Sort-≡-isDecEquivalence
 ; Abs-≡-isDecEquivalence
 ; Arg-≡-isDecEquivalence
 )

instance
  import Reflection.Definition as Definition
  Definition-≡-isDecEquivalence : DecEq Definition
  Definition-≡-isDecEquivalence = isDecEquivalence Definition._≟_
