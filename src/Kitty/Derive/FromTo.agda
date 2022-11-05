{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive.FromTo where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.ActionsClass hiding (⟦_⟧; term→name)
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

open import Kitty.Prelude using (_∋_)
open import Kitty.Modes
open import Kitty.Generics
open import Kitty.Iso
open import Kitty.Derive.Common

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ
  F : Functor' ℓ
  VM TM : Set

-- Deriving n-ary cong ---------------------------------------------------------

-- cong₂ : ∀ {a : Level} {A : Set a}
--           {b : Level} {B : Set b}
--           {c : Level} {C : Set c}
--           (f : A → B → C)
--           {x y : A}
--           {u v : B}
--         → x ≡ y
--         → u ≡ v
--         → f x u ≡ f y v
-- cong₂ f refl refl = refl

cong-n : ℕ → Name → FreshT TC ⊤
cong-n n nm = do
  levels    ← fresh-ids n "ℓ"
  sets      ← fresh-ids n "A"
  out-level ← fresh-id "ℓ"
  out-set   ← fresh-id "A"
  let all-levels = levels ++ [ out-level ]
  let all-sets   = sets ++ [ out-set ]
  let level-tel  = map (λ ℓ → (ℓ , argₕ (def (quote Level) []))) all-levels
  let set-tel    = map (λ (ℓ , A) → (A , argₕ (agda-sort (set (var ℓ []))))) (zip all-levels all-sets)
  f ← fresh-id "f"
  let f-ty  = tel→pi (map (λ A → ("_" , argᵥ (var A []))) sets) (var out-set [])
  let f-tel = [ f , argᵥ f-ty ]
  args-x ← fresh-ids (length sets) "x"
  args-y ← fresh-ids (length sets) "y"
  let args-x-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-x sets)
  let args-y-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-y sets)
  let eq-tel = map
        (λ (x , y) → ("_", argᵥ (def (quote _≡_) [ argᵥ (var x []) ; argᵥ (var y []) ])))
        (zip args-x args-y)
  let eq-res = def (quote _≡_) [ argᵥ (var f (map (λ x → argᵥ (var x [])) args-x))
                               ; argᵥ (var f (map (λ y → argᵥ (var y [])) args-y)) ]
  let tel = level-tel ++ set-tel ++ f-tel ++ args-x-tel ++ args-y-tel ++ eq-tel
  let cong-ty = tel→pi tel eq-res
  let cong-clause = clause
        (level-tel ++ set-tel ++ f-tel)
        (List.map (λ x → argₕ (var x)) all-levels ++
        List.map (λ x → argₕ (var x)) all-sets ++
        argᵥ (var f) ∷ List.map (λ _ → argᵥ (con (quote refl) [])) eq-tel)
        (con (quote refl) [])
  defdecFun' (argᵥ nm) cong-ty [ cong-clause ]

-- Deriving from∘to ------------------------------------------------------------

deriveFromToClause : Name → Name → FreshT TC Clause'
deriveFromToClause from∘to-nm con-nm = do
  con-ty ← getType' con-nm
  let tel , ret-ty = pi→tel con-ty
  ret-nm ← liftTC $ term→name ret-ty
  let tel-rec , tel-non-rec = splitRec tel ret-nm
  let rec-ids = map proj₁ tel-rec
  let non-rec-ids = map proj₁ tel-non-rec
  cong-name ← freshName "cong-n"
  cong-n (length rec-ids) cong-name
  let cong-fun = tel→lam tel-rec $ con con-nm $
                  List.map (λ{ (x , arg i t) → arg i (var x [])}) tel
  return $ clause
    tel
    [ argᵥ (con con-nm (tel→patterns tel)) ]
    (def cong-name (argᵥ cong-fun ∷ List.map (λ x → argᵥ (def from∘to-nm [ argᵥ (var x []) ])) rec-ids))

deriveFromTo : Name → Name → Name → Name → Name → Name → TC ⊤
deriveFromTo modes-nm Term-nm desc-nm to-nm from-nm from∘to-nm = runFreshT $ do
  ty ← getDefinition Term-nm
  let cs = ctors ty
  var-c , term-cs ← split-term-ctors cs
  modes ← unquoteTC {A = Modes} (def modes-nm [])
  Term  ← unquoteTC {A = Modes.Scoped modes} (def Term-nm [])
  d     ← unquoteTC {A = Desc modes} (def desc-nm [])
  from  ← unquoteTC {A = ∀ {µ M} → Tm modes d µ M → Term µ M} (def from-nm [])
  to    ← unquoteTC {A = ∀ {µ M} → Term µ M → Tm modes d µ M} (def to-nm [])
  let var-clause = clause
        [ ("µ" , argₕ unknown)
        ; ("m" , argₕ unknown)
        ; ("x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ" []) ; argᵥ (var "m" []) ]))
        ]
        [ argᵥ (con var-c [ argₕ (var "µ") ; argₕ (var "m") ; argᵥ (var "x") ]) ]
        (con (quote refl) [])
  term-clauses ← forM (enumerate term-cs) λ (i , c) → do
    deriveFromToClause from∘to-nm c
  from∘to-ty ← quoteTC' (∀ {µ} {M} → (x : Term µ M) → from (to x) ≡ x)
  defdecFun' (argᵥ from∘to-nm) from∘to-ty (var-clause ∷ term-clauses)
