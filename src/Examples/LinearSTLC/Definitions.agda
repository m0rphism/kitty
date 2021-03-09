module Examples.LinearSTLC.Definitions where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

open import Substructural.Usage using (Usage; [0]; [1]; [∞]; Semiring; Lattice; Semiring-Usage; Lattice-Usage)
open Semiring {{...}}
open Lattice {{...}}

postulate fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
open Substructural.Usage.Instances-∀ fun-ext using (Semiring-∀; Lattice-∀)

private
  instance
    _ = Semiring-Usage
    _ = Semiring-∀
    _ = Lattice-Usage
    _ = Lattice-∀
