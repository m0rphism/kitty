{-# OPTIONS -vreflection-debug:10 #-}

module KitTheory.Derive.Iso where

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
open import KitTheory.Derive.Desc
open import KitTheory.Derive.To
open import KitTheory.Derive.From
open import KitTheory.Derive.ToFrom
open import KitTheory.Derive.FromTo

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ
  F : Functor' ℓ
  VM TM : Set

-- Deriving the Isomorphism ----------------------------------------------------

deriveIso : Name → Name → Name → TC ⊤
deriveIso modes-nm Term-nm Iso-nm = do
  printAST "–– deriveIso –––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––"
  desc-nm    ← freshName "d"
  to-nm      ← freshName "to"
  from-nm    ← freshName "from"
  from∘to-nm ← freshName "from∘to"
  to∘from-nm ← freshName "to∘from"
  printAST "–– deriveDesc"
  deriveDesc   modes-nm Term-nm desc-nm
  printAST "–– deriveTo"
  deriveTo     modes-nm Term-nm desc-nm to-nm
  printAST "–– deriveFrom"
  deriveFrom   modes-nm Term-nm desc-nm from-nm
  printAST "–– deriveFromTo"
  deriveFromTo modes-nm Term-nm desc-nm to-nm from-nm from∘to-nm
  printAST "–– deriveToFrom"
  deriveToFrom modes-nm Term-nm desc-nm to-nm from-nm to∘from-nm
  modes    ← unquoteTC {A = Modes} (def modes-nm [])
  Term     ← unquoteTC {A = Scoped modes} (def Term-nm [])
  d        ← unquoteTC {A = Desc modes} (def desc-nm [])
  iso-ty   ← quoteTC (∀ {µ} {M} → (Term µ M) ≃ Tm modes d µ M)
  defdecFun
    (argᵥ Iso-nm)
    iso-ty
    [ clause [] [] (con (quote iso)
      [ argᵥ (def to-nm [])
      ; argᵥ (def from-nm [])
      ; argᵥ (def from∘to-nm [])
      ; argᵥ (def to∘from-nm [])
      ])
    ]

deriveIso' : (𝕄 : Modes)
           → Scoped 𝕄
           → Name
           → TC ⊤
deriveIso' modes Term Iso-nm = do
  modes-nm    ← type→name =<< runFreshT (quoteTC' modes)
  Term-nm     ← type→name =<< runFreshT (quoteTC' Term)
  deriveIso modes-nm Term-nm Iso-nm
