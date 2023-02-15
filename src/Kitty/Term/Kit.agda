open import Kitty.Term.Modes

module Kitty.Term.Kit {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Required for proving that `kitᵣ ≢ kitₛ`
data KitTag : Set where
  instance K-Ren K-Sub : KitTag

record Kit : Set₁ where
  infix   4  _∋/⊢_

  field
    VarMode/TermMode : Set
    _∋/⊢_            : List VarMode → VarMode/TermMode → Set 

    id/m→M           : VarMode → VarMode/TermMode
    m→M/id           : VarMode/TermMode → TermMode
    id/m→M/id        : ∀ m → m→M/id (id/m→M m) ≡ m→M m

    id/`             : ∀ m → µ ∋ m → µ ∋/⊢ id/m→M m
    `/id             : ∀ m → µ ∋/⊢ id/m→M m → µ ⊢ m→M m
    `/id'            : ∀ m → µ ∋/⊢ m → µ ⊢ m→M/id m -- For IKit Experiment
    id/`/id          : ∀ x → `/id {µ = µ} m (id/` _ x) ≡ ` x
    id/`/id'         : ∀ x → let sub = subst (µ ⊢_) (sym (id/m→M/id m)) in
                             `/id' {µ = µ} (id/m→M m) (id/` _ x) ≡ sub (` x) -- For Compose Experiment
    `/id≡`/id'       : ∀ {m} (x/t : µ ∋/⊢ id/m→M m)
                       → let sub = subst (µ ⊢_) (id/m→M/id m) in
                         `/id _ x/t ≡ sub (`/id' _ x/t)

    wk               : ∀ m/M → µ ∋/⊢ m/M → (µ ▷ m') ∋/⊢ m/M
    wk-id/`          : ∀ m' (x : µ ∋ m) → wk {m' = m'} _ (id/` _ x) ≡ id/` _ (there x)
    kit-tag          : KitTag

  -- Weakening

  wk* : ∀ SM → µ ∋/⊢ SM → (µ ▷▷ µ') ∋/⊢ SM
  wk* {µ' = []}     m/M x = x
  wk* {µ' = µ' ▷ m} m/M x = wk m/M (wk* m/M x)

  -- wk' : µ –→ (µ ▷ m)
  -- wk' _ x = wk _ (id/` _ x)

  -- wk'* : µ –→ (µ ▷▷ µ')
  -- wk'* _ x = wk* _ (id/` _ x)

_∋/⊢[_]_ : List VarMode → (𝕂 : Kit) → Kit.VarMode/TermMode 𝕂 → Set
µ ∋/⊢[ 𝕂 ] sm = Kit._∋/⊢_ 𝕂 µ sm

kitᵣ : Kit
Kit.VarMode/TermMode kitᵣ = VarMode
Kit._∋/⊢_            kitᵣ = _∋_
Kit.id/m→M           kitᵣ = λ m → m
Kit.m→M/id           kitᵣ = m→M
Kit.id/m→M/id        kitᵣ = λ m → refl
Kit.id/`             kitᵣ = λ m x → x
Kit.`/id             kitᵣ = λ m x → ` x
Kit.`/id'            kitᵣ = λ m x → ` x
Kit.id/`/id          kitᵣ = λ x → refl
Kit.id/`/id'         kitᵣ = λ x → refl
Kit.`/id≡`/id'       kitᵣ = λ x → refl
Kit.wk               kitᵣ = λ m x → there x
Kit.wk-id/`          kitᵣ = λ m x → refl
Kit.kit-tag          kitᵣ = K-Ren

