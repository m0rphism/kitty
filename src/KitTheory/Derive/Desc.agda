{-# OPTIONS -vreflection-debug:10 #-}

module KitTheory.Derive.Desc where

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

-- Deriving Desc ---------------------------------------------------------------

-- TODO: infer name and bind position of "µ"
µ→[]' : String → Term' → TC Term'
µ→[]' `µ t₂ = do
  let t₂ = rw (λ { ⦃ `Term ⦄ t → case un-++ t of λ where
                     (just (xs , var ys [])) → case `µ String.≟ ys of λ where
                                                 (yes _) → just xs
                                                 (no  _) → nothing
                     _                        → nothing
                 ; ⦃ T     ⦄ t → nothing
                 }) t₂
  pure $ t₂ [ `µ ↦ con (quote List.List.[]) [] ]

µ→[] : Term' → TC Term'
µ→[] (pi t₁ (abs `µ t₂)) = µ→[]' `µ t₂
µ→[] _                = failStr "Constructor doesn't start with quantification over µ."

deriveDesc : Name → Name → Name → TC ⊤
deriveDesc modes-nm Term-nm desc-nm = runFreshT do
  modes  ← unquoteTC {A = Modes} (def modes-nm [])
  Term-def ← getDefinition Term-nm
  _ , term-cons ← split-term-ctors (ctors Term-def)
  clauses ← forM (enumerate term-cons) λ (i , c) → do
    c-ty ← getType' c
    c-ty ← liftTC $ µ→[] c-ty
    liftTC $ printAST "Post-Subst:"
    liftTC $ printAST c-ty
    let (c-tel , c-ret) = pi→tel c-ty
    end-ty ← case c-ret of λ where
      (def f [ µ ; M ]) → pure (Term' by con (quote `■) [ M ])
      _                 → liftTC $ failStr "Unexpected constructor type"
    let desc = foldr' c-tel end-ty λ where
          (x , arg i arg-ty) desc → case unterm Term-nm arg-ty of λ where
            (just (µ , M)) →
              con (quote `X) [ argᵥ µ ; argᵥ M ; argᵥ desc ]
            nothing →
              con (quote `σ)
                [ argᵥ arg-ty
                ; argᵥ (lam visible (abs x desc))
                ]
    pure $ clause [] [ argᵥ (fin-pat' i) ] desc
  f ← unquoteTC' (pat-lam clauses [])
  desc ← quoteNormTC' (`σ {𝕄 = modes} (Fin (length term-cons)) f)
  defdecFun'
    (argᵥ desc-nm)
    (def (quote Desc) [ argᵥ (def modes-nm []) ])
    [ clause [] [] desc ]
