open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)

module Kitty.Typing.ITerms {𝕄 : Modes} (𝕋 : Terms 𝕄) {ℓ} (𝕊 : SubWithLaws 𝕋 ℓ) (T : Traversal 𝕋 𝕊) (H : KitHomotopy 𝕋 𝕊 T)
                           (𝕊C : SubCompose 𝕋 𝕊 T H) (C : ComposeTraversal 𝕋 𝕊 T H 𝕊C) (KT : KitType 𝕋) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude

open import Kitty.Term.Kit 𝕋
open Modes 𝕄
open Terms 𝕋
open Kitty.Typing.Types.KitType KT
open import Kitty.Typing.OPE C KT

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ₁ ℓ₂ : Level
    Γ Γ₁ Γ₂ : Ctx µ
    x y z : µ ∋ m

record ITerms : Set₁ where
  infix   4  _⊢_∶_
  field
    _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set
    ⊢` : ∀ {Γ : Ctx µ} {x : µ ∋ m} {t} →
         Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t
