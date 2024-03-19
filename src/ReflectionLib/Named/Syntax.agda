module ReflectionLib.Named.Syntax where

import Level as Level

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String
open import Data.String using (String) public

open import Reflection hiding (name; Type)
open import Agda.Builtin.Reflection
open import Level using (Level)
open import Function using (_$_)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

mutual 
  data Pattern' : Set where
    con    : (c : Name) (ps : List (Arg Pattern')) → Pattern'
    dot    : (t : Term')   → Pattern'
    var    : (x : String)  → Pattern'
    lit    : (l : Literal) → Pattern'
    proj   : (f : Name)    → Pattern'
    absurd : (x : String)  → Pattern'  -- absurd patterns counts as variables

  Type' = Term'
  data Term' : Set where
    var       : (x : String) (args : List (Arg Term')) → Term'
    con       : (c : Name) (args : List (Arg Term')) → Term'
    def       : (f : Name) (args : List (Arg Term')) → Term'
    lam       : (v : Visibility) (t : Abs Term') → Term'
    pat-lam   : (cs : List Clause') (args : List (Arg Term')) → Term'
    pi        : (a : Arg Type') (b : Abs Type') → Term'
    agda-sort : (s : Sort') → Term'
    lit       : (l : Literal) → Term'
    meta      : (x : Meta) → List (Arg Term') → Term'
    unknown   : Term'

  data Sort' : Set where
    set     : (t : Term') → Sort'
    lit     : (n : ℕ) → Sort'
    prop    : (t : Term') → Sort'
    propLit : (n : ℕ) → Sort'
    inf     : (n : ℕ) → Sort'
    unknown : Sort'

  data Clause' : Set where
    clause        : (tel : List (Σ String λ _ → Arg Type')) (ps : List (Arg Pattern')) (t : Term') → Clause'
    absurd-clause : (tel : List (Σ String λ _ → Arg Type')) (ps : List (Arg Pattern')) → Clause'

Telescope' : Set
Telescope' = List (String × Arg Term')

data Definition' : Set where
  function    : (cs : List Clause') → Definition'
  data-type   : (pars : ℕ) (cs : List Name) → Definition'
  record-type : (c : Name) (fs : List (Arg Name)) → Definition'
  data-cons   : (d : Name) → Definition'
  axiom       : Definition'
  prim-fun    : Definition'

data Pattern'' : Set where
  con    : (c : Name) (ps : List (Arg Pattern'')) → Pattern''
  dot    : (t : Term')   → Pattern''
  var    : (x : String)  → (t : Type') → Pattern''
  lit    : (l : Literal) → Pattern''
  proj   : (f : Name)    → Pattern''
  absurd : (x : String)  → (t : Type') → Pattern''  -- absurd patterns counts as variables

data Clause'' : Set where
  clause        : (ps : List (Arg Pattern'')) (t : Term') → Clause''
  absurd-clause : (ps : List (Arg Pattern'')) → Clause''

tel→pi : Telescope' → Type' → Type'
tel→pi []              t' = t'
tel→pi ((x , t) ∷ tel) t' = pi t (abs x (tel→pi tel t'))

list→pi : Telescope' → Type' → Type'
list→pi tel t' = tel→pi (reverse tel) t'

pi→tel : Type' → Telescope' × Type'
pi→tel (pi a (abs x t)) = let (tel , t') = pi→tel t in
                          ((x , a) ∷ tel) , t'
pi→tel t                = [] , t

pi→list : Type' → Telescope' × Type'
pi→list t = let (tel , t') = pi→tel t in
            reverse tel , t'

tel→patterns : Telescope' → List (Arg Pattern')
tel→patterns = List.map λ { (x , arg i _) → arg i (var x) }

tel→vars : Telescope' → List (Arg Term')
tel→vars = List.map λ { (x , arg i _) → arg i (var x []) }

tel→lam : Telescope' → Term' → Term'
tel→lam []                                  t = t
tel→lam ((x , arg (arg-info v _) t') ∷ tel) t = lam v (abs x (tel→lam tel t))
