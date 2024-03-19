module ReflectionLib.Named.DecEq where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.DecEq
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Classes.DecEq public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List using (List; _∷_ ; [])
import Data.List.Properties as ListP

open import ReflectionLib.Standard.DecEq public using
 ( Lit-≡-isDecEquivalence
 ; Name-≡-isDecEquivalence
 ; Meta-≡-isDecEquivalence
 ; Visibility-≡-isDecEquivalence
 ; Relevance-≡-isDecEquivalence
 ; ArgInfo-≡-isDecEquivalence
 ; Abs-≡-isDecEquivalence
 ; Arg-≡-isDecEquivalence
 )

instance
  mutual 

    _≟-Patterns'_ : ∀ (x y : List (Arg Pattern')) → Dec (x ≡ y)
    []       ≟-Patterns' []       = yes refl
    []       ≟-Patterns' (x ∷ ys) = no (λ ())
    (x ∷ xs) ≟-Patterns' []       = no (λ ())
    (x ∷ xs) ≟-Patterns' (y ∷ ys) with x ≟ y | xs ≟-Patterns' ys
    ... | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
    ... | no ¬x≡y | _         = no λ{ refl → ¬x≡y refl }
    ... | _       | no ¬xs≡ys = no λ{ refl → ¬xs≡ys refl }

    DecEq-Pattern' : DecEq Pattern'
    DecEq-Pattern' = isDecEquivalence _≟'_ where
      _≟'_ : ∀ (x y : Pattern') → Dec (x ≡ y)
      con c₁ ps₁ ≟' con c₂ ps₂ with c₁ ≟ c₂   | ps₁ ≟-Patterns' ps₂
      ...                         | yes c₁≡c₂ | yes ps₁≡ps₂ = {!!}
      ...                         | no ¬c₁≡c₂ | _           = {!!}
      ...                         | _         | no ¬ps₁≡ps₂ = {!!}
      dot t₁     ≟' dot t₂     = {!!}
      var x₁     ≟' var x₂     = {!!}
      lit l₁     ≟' lit l₂     = {!!}
      proj f₁    ≟' proj f₂    = {!!}
      absurd x₁  ≟' absurd x₂  = {!!}

      con c ps   ≟' dot t      = no λ()
      con c ps   ≟' var x      = no λ()
      con c ps   ≟' lit l      = no λ()
      con c ps   ≟' proj f     = no λ()
      con c ps   ≟' absurd x   = no λ()
      dot t      ≟' con c ps   = no λ()
      dot t      ≟' var x      = no λ()
      dot t      ≟' lit l      = no λ()
      dot t      ≟' proj f     = no λ()
      dot t      ≟' absurd x   = no λ()
      var x      ≟' con c ps   = no λ()
      var x      ≟' dot t      = no λ()
      var x      ≟' lit l      = no λ()
      var x      ≟' proj f     = no λ()
      var x      ≟' absurd x₁  = no λ()
      lit l      ≟' con c ps   = no λ()
      lit l      ≟' dot t      = no λ()
      lit l      ≟' var x      = no λ()
      lit l      ≟' proj f     = no λ()
      lit l      ≟' absurd x   = no λ()
      proj f     ≟' con c ps   = no λ()
      proj f     ≟' dot t      = no λ()
      proj f     ≟' var x      = no λ()
      proj f     ≟' lit l      = no λ()
      proj f     ≟' absurd x   = no λ()
      absurd x   ≟' con c ps   = no λ()
      absurd x   ≟' dot t      = no λ()
      absurd x   ≟' var x₁     = no λ()
      absurd x   ≟' lit l      = no λ()
      absurd x   ≟' proj f     = no λ()

    DecEq-Term' : DecEq Term'
    DecEq-Term' = isDecEquivalence _≟'_ where
      _≟'_ : ∀ (x y : Term') → Dec (x ≡ y)
      x ≟' y = {!!}

    DecEq-Sort' : DecEq Sort'
    DecEq-Sort' = isDecEquivalence _≟'_ where
      _≟'_ : ∀ (x y : Sort') → Dec (x ≡ y)
      x ≟' y = {!!}

    DecEq-Clause' : DecEq Clause'
    DecEq-Clause' = isDecEquivalence _≟'_ where
      _≟'_ : ∀ (x y : Clause') → Dec (x ≡ y)
      x ≟' y = {!!}

  DecEq-Definition' : DecEq Definition'
  DecEq-Definition' = isDecEquivalence _≟'_ where
    _≟'_ : ∀ (x y : Definition') → Dec (x ≡ y)
    x ≟' y = {!!}

-- data Pattern'' : Set where
--   con    : (c : Name) (ps : List (Arg Pattern'')) → Pattern''
--   dot    : (t : Term')   → Pattern''
--   var    : (x : String)  → (t : Type') → Pattern''
--   lit    : (l : Literal) → Pattern''
--   proj   : (f : Name)    → Pattern''
--   absurd : (x : String)  → (t : Type') → Pattern''  -- absurd patterns counts as variables

-- data Clause'' : Set where
--   clause        : (ps : List (Arg Pattern'')) (t : Term') → Clause''
--   absurd-clause : (ps : List (Arg Pattern'')) → Clause''
