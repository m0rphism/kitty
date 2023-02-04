{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive.Common where

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

open import Kitty.Prelude using (_∋_; _▷▷_)
open import Kitty.Modes
open import Kitty.Iso

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ
  F : Functor' ℓ
  VM TM : Set

-- Helpers ---------------------------------------------------------------------

_by_ : (A : Set ℓ) → A → A
A by a = a

FreshTC = FreshT {0ℓ} TC

subst-pi : Type' → Term' → Type'
subst-pi (pi a (abs x b)) t' = (b [ x ↦ t' ])
subst-pi t                t' = t

split-term-ctors : List Name → FreshTC (Name × List Name)
split-term-ctors []       = liftTC $ failStr "No variable constructor found"
split-term-ctors (c ∷ cs) = return (c , cs)

_isTCon_ : Type' → Name → Bool
def nm args isTCon nm' = primQNameEquality nm nm' 
_           isTCon _   = false 

splitRec : Telescope' → Name → Telescope' × Telescope'
splitRec []                      nm = [] , []
splitRec (b@(x , arg i t) ∷ tel) nm =
  let tel-rec , tel = splitRec tel nm in
  if t isTCon nm then (b ∷ tel-rec , tel)
                else (tel-rec , b ∷ tel)

foldr' : {T : Functor' ℓ} {{_ : Foldable ℓ T}}
        → T A → B → (A → B → B) → B
foldr' ta b0 f = foldr f b0 ta

foldrM' : {T : Functor' ℓ} {{_ : Traversable ℓ T}}
          {F : Functor' ℓ'} {{_ : Monad ℓ' F}}
        → T A → F B → (A → B → F B) → F B
foldrM' ta b0 f = foldrM f b0 ta

unterm : Name → Term' → Maybe (Term' × Term')
unterm Term-nm (def f [ argᵥ µ ; argᵥ M ]) =
  if primQNameEquality f Term-nm
    then just (µ , M)
    else nothing
unterm Term-nm _ = nothing

cong-Σ : {A : Set ℓ₁} {B : A → Set ℓ₂} {x y : A} {u : B x} {v : B y} →
      (p : x ≡ y) → subst B p u ≡ v → (x , u) ≡ (y , v)
cong-Σ refl refl = refl

cong-× : {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} {u v : B} →
      x ≡ y → u ≡ v → (x , u) ≡ (y , v)
cong-× refl refl = refl

uip : ∀ {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl

un-++ : Term' → Maybe (Term' × Term')
un-++ (def (quote _++_) args) = case drop (length args ∸ 2) args of λ where
                                  [ argᵥ xs ; argᵥ ys ] → just (xs , ys)
                                  _                     → nothing
un-++ (def (quote _▷▷_) args) = case drop (length args ∸ 2) args of λ where
                                  [ argᵥ xs ; argᵥ ys ] → just (ys , xs)
                                  _                     → nothing
un-++ _ = nothing
