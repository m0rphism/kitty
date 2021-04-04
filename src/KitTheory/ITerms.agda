open import KitTheory.Modes
open import KitTheory.Kit using (KitTraversal)
open import KitTheory.Compose using (KitAssoc)
open import KitTheory.Types using (KitType)
open KitAssoc using (KitAssocLemmas)

module KitTheory.ITerms {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) (A : KitAssoc 𝕋 T) (AL : KitAssocLemmas A) (KT : KitType 𝕋 T A AL) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import KitTheory.Prelude

open Modes 𝕄
open Terms 𝕋
open KitTheory.Types.KitType KT

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m

infix   4  _∋_∶_

_∋_∶_ : Ctx µ → µ ∋ m → µ ∶⊢ m→M m → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

record ITerms : Set₁ where
  infix   4  _⊢_∶_
  field
    _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set
    ⊢` : ∀ {Γ : Ctx µ} {x : µ ∋ m} {t} →
         Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t
