{-# OPTIONS -vreflection-debug:10 #-}

module KitTheory.Derive.To where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.ActionsClass hiding (⟦_⟧)
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Actions
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Named.Substitution
open import ReflectionLib.Named.Rewrite
open import ReflectionLib.Categorical
open import ReflectionLib.Algorithms.Fin
open import ReflectionLib.Algorithms.Nat

open import Data.String as String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_; length; drop; zip; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Function using (_∘_; _$_; case_of_)

open import KitTheory.Prelude using (_∋_)
open import KitTheory.Modes
open import KitTheory.Generics
open import KitTheory.Iso
open import KitTheory.Derive.Common

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ
  F : Functor' ℓ
  VM TM : Set

-- Derving To ------------------------------------------------------------------

deriveTo : Name → Name → Name → Name → TC ⊤
deriveTo modes-nm Term-nm desc-nm to-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  var-c , term-cs ← split-term-ctors $ ctors ty
  modes  ← unquoteTC {A = Modes} (def modes-nm [])
  Term ← unquoteTC' {A = Scoped modes} (def Term-nm [])
  d ← unquoteTC' (def desc-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con var-c [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con (quote `var) [ argₕ unknown ; argₕ unknown ; argᵥ (var "x" []) ])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    c-ty ← getType' c
    let c-tel , c-ret = pi→tel c-ty
    let c-tel' = List.drop 1 c-tel
    `µ ← case List.head c-tel of λ where
      (just (x , _)) → pure x
      nothing        → liftTC $ failStr "No µ found."
    let ps = tel→patterns c-tel'
    let t = foldr
          (λ { (x , arg i tx) t → case unterm Term-nm tx of λ where
            (just (µ , M)) → con (quote _,_) [ argᵥ (def to-nm [ argᵥ (var x []) ]) ; argᵥ t ]
            nothing        → con (quote _,_) [ argᵥ (var x []) ; argᵥ t ]
          })
          (con (quote refl) [])
          c-tel'
    pure $ clause
      c-tel
      [ argᵥ (con c (argₕ (var `µ) ∷ ps)) ]
      (con (quote `con) [ (argᵥ (con (quote _,_) [ argᵥ (fin-con' i) ; argᵥ t ])) ])
  to-ty ← quoteTC' (∀ {µ} {M} → Term µ M → Tm modes d µ M)
  defdecFun'
    (argᵥ to-nm)
    to-ty
    (var-clause ∷ term-clauses)
