open import Kitty.Term.Modes
open import Kitty.Term.Sub
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)

module Kitty.Term.Strengthen {𝕄 : Modes} {𝕋 : Terms 𝕄} {ℓ} {𝕊 : SubWithLaws 𝕋 ℓ} {T : Traversal 𝕋 𝕊} {H : KitHomotopy 𝕋 𝕊 T}
                        {𝕊C : SubCompose 𝕋 𝕊 T H} (C : ComposeTraversal 𝕋 𝕊 T H 𝕊C) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_; drop; take)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

open Modes 𝕄
open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open Kitty.Term.Traversal.Traversal T
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open Kitty.Term.ComposeTraversal.ComposeTraversal C

open Kit ⦃ … ⦄
open KitT ⦃ … ⦄
open ComposeKit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open SubCompose ⦃ … ⦄

open import Data.Product using (Σ-syntax; ∃-syntax; _,_) 
open import Data.List.Properties using (++-identityʳ; take++drop)
open import Data.List.Membership.Propositional using (_∈_)

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kittᵣ
private instance _ = kittₛ
private instance _ = ckitᵣ
private instance _ = ckitₛᵣ
private instance _ = ckitₛₛ
private instance _ = 𝕊
private instance _ = 𝕊C

-- ∈-split : ∀ {ℓ} {A : Set ℓ} {x : A} {xs} → (x ∈ xs) → ∃[ xs₁ ] ∃[ xs₂ ] xs ≡ xs₁ ++ x ∷ xs₂  
-- ∈-split {ℓ} {A} {x} {.x ∷ xs} (here refl) = [] , xs , refl
-- ∈-split {ℓ} {A} {x} {x' ∷ xs} (there x∈xs) with ∈-split x∈xs
-- ... | xs₁ , xs₂ , refl = x' ∷ xs₁ , xs₂ , refl

open import Kitty.Term.Prelude

depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

-- We need to drop one extra using `suc`, because otherwise the types in a
-- context are allowed to use themselves.
drop-∈ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
drop-∈ x = drop (suc (depth x))

take-∈ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
take-∈ x = take (suc (depth x))

take-∈' : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
take-∈' x = take (depth x)

wk-drop-∈ : ∀ {µ} {m : VarMode} {M : TermMode} (x : µ ∋ m) → drop-∈ x µ ⊢ M → µ ⊢ M
wk-drop-∈ (here _)  t = wk _ t
wk-drop-∈ (there x) t = wk _ (wk-drop-∈ x t)

∈-split : ∀ {ℓ} {A : Set ℓ} {x : A} {xs} → (x∈xs : x ∈ xs) → take-∈' x∈xs xs ++ x ∷ drop-∈ x∈xs xs ≡ xs
∈-split {ℓ} {A} {x} {.x ∷ xs} x∈xs@(here refl) = refl
∈-split {ℓ} {A} {x} {x' ∷ xs} x∈xs@(there x∈xs') =
  take-∈' x∈xs (x' ∷ xs) ++ (x ∷ drop-∈ x∈xs (x' ∷ xs)) ≡⟨⟩
  x' ∷ take-∈' x∈xs' xs ++ (x ∷ drop-∈ x∈xs' xs)        ≡⟨ cong (x' ∷_) (∈-split x∈xs') ⟩
  x' ∷ xs                                               ∎

_free-in_ : ∀ {m} {µ} {M} (x : µ ∋ m) (t : µ ⊢ M) → Set
_free-in_ {m} {µ} {M} x t =
  let sub = subst₂ (_→ₛ_) (∈-split x) (∈-split x) in 
  ∀ (t' : drop-∈ x µ ⊢ m→M m) → t ⋯ sub (wkₖ m ⦅ t' ⦆ ↑* (take-∈' x µ)) ≡ t
