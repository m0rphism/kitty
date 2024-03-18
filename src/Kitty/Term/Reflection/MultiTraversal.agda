{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Term.Reflection.MultiTraversal where

open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_; length; drop; zip; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _$_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)
open ≡-Reasoning
import Agda.Builtin.List

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Standard.ActionsClass hiding (term→name; ⟦_⟧)
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Actions
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Named.FromStandard
open import ReflectionLib.Named.ToStandard
open import ReflectionLib.Named.Substitution
open import ReflectionLib.Named.Rewrite
open import ReflectionLib.Algorithms.Fin
open import ReflectionLib.Algorithms.Nat
open import ReflectionLib.Categorical

open import Kitty.Term.Prelude using (_∋_)
open import Kitty.Term.Terms
import Kitty.Term.Kit
import Kitty.Term.MultiTraversal
open import Kitty.Util.Star using (Star; []; _∷_)
open import Kitty.Term.Reflection.Common
import Kitty.Term.Sub
import Kitty.Term.MultiSub

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ

Scoped' : (Sort : SortTy → Set) → Set₁
Scoped' Sort = List (Sort Var) → Sort Var → Set

record VarCon (Sort : SortTy → Set) (_⊢_ : Scoped' Sort) : Set where
  field
    nm    : Name
    ctor` : Term' → Term'
    pat`  : Pattern' → Pattern'
    ctor  : ∀ {S s} → S ∋ s → S ⊢ s

  ctor-lam` : Term'
  ctor-lam` = lam visible (abs "x" (ctor` (var "x" [])))

open VarCon

get-var-con : (Sort : SortTy → Set) (_⊢_ : Scoped' Sort) → Name → TC (VarCon Sort _⊢_)
get-var-con 𝕄 _⊢_ `-nm = do
  catchTC
    (do
      `_ ← unquoteTC' {A = ∀ {S s} → S ∋ s → S ⊢ s} (con `-nm [])
      pure record
        { nm = `-nm
        ; ctor` = λ x → con `-nm [ argᵥ x ]
        ; pat` = λ x → con `-nm [ argᵥ x ]
        ; ctor = λ {S} → `_ {S}
        }
    )
    (do
      `_ ← (unquoteTC' {A = ∀ {S s} → S ∋ s → S ⊢ s}
                        (lam hidden (abs "S"
                        (lam hidden (abs "s"
                        (con `-nm [ argₕ (var "S" [])
                                  ; argₕ (var "s" [])
                                  ; argᵥ (con (quote refl) [])
                                  ]))))))
      pure record
        { nm = `-nm
        ; ctor` = λ x → con `-nm [ argᵥ (con (quote refl) []) ; argᵥ x ]
        ; pat` = λ x → con `-nm [ argᵥ (con (quote refl) []) ; argᵥ x ]
        ; ctor = λ {S} → `_ {S}
        }
    )

derive-Terms : (Sort : SortTy → Set) → (_⊢_ : Scoped' Sort) → Name → TC ⊤
derive-Terms Sort _⊢_ terms-nm = runFreshT do
  Sort-nm ← quoteNameTC Sort
  ⊢-nm ← quoteNameTC _⊢_
  ⊢-def ← getDefinition ⊢-nm
  `-nm , _ ← split-term-ctors (ctors ⊢-def)
  var-con ← liftTC $ get-var-con Sort _⊢_ `-nm
  terms-ty ← quoteTC' Terms
  -- terms-body ← quoteTC' (mkTerms _⊢_ (ctor var-con) `-injective)
  let `-injective = pat-lam [ clause [] [ argᵥ (con (quote refl) []) ] (con (quote refl) []) ] []
  let terms-body = def (quote mkTerms) [ argᵥ (def Sort-nm []) ; argᵥ (def ⊢-nm []) ; argᵥ (ctor-lam` var-con) ; argᵥ `-injective ]
  -- let terms-ty = def (quote Terms) [ argᵥ (def 𝕄-nm []) ]
  -- let terms-body = def (quote mkTerms) [ argᵥ (def ⊢-nm []) ; argᵥ (con `-nm []) ] 
  defdecFun'
    (argᵥ terms-nm)
    terms-ty
    [ clause [] [] terms-body ]

-- record DeriveContext : Set₁ where
--   field
--     𝕄 : Modes
--     𝕋 : Terms 𝕄

--     `𝕄 : Name
--     `𝕋 : Name
--     `⊢ : Name
--     `VarMode : Name
--     `TermMode : Name
--     `Kit : Name
--     `⋯ : Name

--     `var : Name
--     `cons : List Name
--     con-tys : List Type'
--     con-tels : List Telescope'

--   open Modes 𝕄 public
--   open Terms 𝕋 public
--   open Kitty.Kit 𝕋 public

derive-⋯ : Terms → Name → TC ⊤
derive-⋯ 𝕋 ⋯-nm = runFreshT do
  let open Terms 𝕋 renaming (Sort to 𝕋Sort)
  let open Kitty.Term.Kit 𝕋
  let open Kitty.Term.Sub 𝕋
  let open Sub ⦃ … ⦄
  ⊢-nm ← quoteNameTC (_⊢_ {Var})
  ⊢-def ← getDefinition ⊢-nm
  `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
  var-con ← liftTC $ get-var-con 𝕋Sort _⊢_ `-nm
  𝕋-nm ← term→name =<< quoteTC' 𝕋
  -- TermMode` ← quoteNormTC' TermMode
  VarSort` ← quoteNormTC' (𝕋Sort Var)
  SortTy` ← quoteNormTC' SortTy
  let Sort` : Term' → Term'
      Sort` st = def (quote Kitty.Term.Terms.Terms.Sort) [ argᵥ (def 𝕋-nm []) ; argᵥ st ]
  SortCtx` ← quoteNormTC' (List (𝕋Sort Var))
  let VarScoped` : Term'
      VarScoped` = def (quote Kitty.Term.Terms.Terms.VarScoped) [ argᵥ (def 𝕋-nm []) ]
  Set` ← quoteTC' Set
  let Kit` : Term' → Term'
      Kit` _∋/⊢_ = def (quote Kitty.Term.Kit.Kit) [ argᵥ (def 𝕋-nm []) ; argᵥ _∋/⊢_ ]
  Level` ← quoteTC' Level
  let Sub` : Term' → Term'
      Sub` ℓ = def (quote Kitty.Term.Sub.Sub) [ argᵥ (def 𝕋-nm []) ; argᵥ ℓ ]

  let mk-tel c-tel =
        [ "ℓ" , argₕ Level`
        ; "𝕊" , argᵢ (Sub` (var "ℓ" []))
        ; "_∋/⊢_" , argₕ VarScoped`
        ; "𝕂" , argᵢ (Kit` (var "_∋/⊢_" []))
        ; "S₁" , argₕ SortCtx`
        ; "S₂" , argₕ SortCtx`
        ] ++ c-tel ++
        [ "f" , argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
            [ argᵥ (var "𝕊" [])
            ; argᵥ (var "S₁" [])
            ; argᵥ (var "𝕂" [])
            ; argᵥ (var "S₂" [])
            ])
        ]
  let mk-pats c-pat = 
        [ argₕ (var "ℓ")
        ; argᵢ (var "𝕊")
        ; argₕ (var "_∋/⊢_")
        ; argᵢ (var "𝕂")
        ; argₕ (var "S₁")
        ; argₕ (var "S₂")
        ] ++ c-pat ∷
        [ argᵥ (var "f" ) ]

  clauses ← forM (enumerate con-nms) λ (i , c) → do
    -- Get constructor telescope
    c-ty ← getType' c
    let (c-tel , c-ret) = pi→tel c-ty

    -- Retrieve variable name used for `S`
    c-S ← case unterm ⊢-nm c-ret of λ where
      (just (var S [] , M)) → pure S
      (just (S , M)) → liftTC $ failStr "constructed type has to return variable as S."
      nothing → liftTC $ failStr "impossible"

    -- Rename `S` binding and occurences to `S₁`
    let c-tel' = List.map (λ { (x , b) → case x String.≟ c-S of λ where
                                            (no _)  → (x , b [ c-S ↦ var "S₁" [] ])
                                            (yes _) → ("S₁" , b)
                              }) c-tel

    -- Remove `S₁` binding, since it's already bound on the outside
    let c-tel'x = List.filterᵇ
          (λ { (x , _) → case x String.≟ "S₁" of λ { (yes _) → false; (no _) → true } })
          c-tel'

    let c-tel'' = List.map (λ { (x , b) → case x String.≟ c-S of λ where
                                            (no _)  → (x , b [ c-S ↦ var "S₂" [] ])
                                            (yes _) → ("S₂" , b)
                              }) c-tel
    let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-S of λ where
                                                  (no _)  → arg i (var x)
                                                  (yes _) → arg i (dot (var "S₁" []))
                              }) c-tel'
    let c-pat = argᵥ (con c c-pats)
    let body = con c $ foldr' c-tel'' [] λ where
          (s , arg i t) c-args → _∷ c-args $ case unterm ⊢-nm t of λ where
            (just _) → arg i (def ⋯-nm [ argᵥ (var s [])
                                       ; argᵥ (def (quote Kitty.Term.MultiSub._↑*'_)
                                           [ argᵥ (def 𝕋-nm [])
                                           ; argᵥ (var "f" [])
                                           ; argᵥ unknown
                                           ])
                                        ]) 
            nothing  → case s String.≟ c-S of λ where
                          (no _)  → arg i (var s [])
                          (yes _) → arg i (var "S₂" [])
    pure $ clause (mk-tel c-tel'x) (mk-pats c-pat) body

  let var-tel = [ "x" , argᵥ (def (quote _∋_) [ argᵥ (var "S₁" [])
                                              ; argᵥ unknown
                                              ])
                ]
  let var-pat = argᵥ (pat` var-con (var "x"))
  let var-clause = clause (mk-tel var-tel)
                          (mk-pats var-pat)
                          (def (quote Kitty.Term.Kit.Kit.`/id)
                            [ argᵥ (var "𝕂" [])
                            ; argᵥ (def (quote Kitty.Term.Sub.Sub._&_) [ argᵥ (var "𝕊" [])
                                                                       ; argᵥ (var "x" [])
                                                                       ; argᵥ (var "f" [])
                                                                       ])
                            ])

  -- ⋯-ty ← quoteTC' (∀ {ℓ} ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ℓ ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {S₁ S₂} {M} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M)
  let ⋯-ty = pi (argₕ (def (quote Level) [])) (abs "ℓ" (
             pi (argᵢ (def (quote Kitty.Term.Sub.Sub) [ argᵥ (def 𝕋-nm []) ; argᵥ (var "ℓ" []) ])) (abs "𝕊" (
             pi (argₕ VarScoped` ) (abs "_∋/⊢_" (
             pi (argᵢ (Kit` (var "_∋/⊢_" []))) (abs "𝕂" (
             pi (argₕ SortCtx`) (abs "S₁" (
             pi (argₕ SortCtx`) (abs "S₂" (
             pi (argₕ SortTy`) (abs "st" (
             pi (argₕ (Sort` (var "st" []))) (abs "s" (
             pi (argᵥ (def ⊢-nm [ argᵥ (var "S₁" []) ; argᵥ (var "s" []) ])) (abs "_" (
             pi (argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
                       [ argᵥ (var "𝕊" []) ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂" []) ; argᵥ (var "S₂" []) ])) (abs "_" (
             def ⊢-nm [ argᵥ (var "S₂" []) ; argᵥ (var "s" []) ]))))))))))))))))))))

  defdecFun'
    (argᵥ ⋯-nm)
    ⋯-ty
    (var-clause ∷ clauses)

-- _⋯_ : ∀ {S₁} {S₂} {M} {{𝕂 : Kit}} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M
-- (` x)     ⋯ f = `/id _ (f _ x)
-- (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
-- (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
-- (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

derive-⋯-var : Terms → Name → Name → TC ⊤
derive-⋯-var 𝕋 ⋯-nm ⋯-var-nm = runFreshT do
  let open Terms 𝕋 renaming (Sort to 𝕋Sort)
  let open Kitty.Term.Kit 𝕋
  let open Kitty.Term.Sub 𝕋
  let open Sub ⦃ … ⦄
  let open SubWithLaws ⦃ … ⦄

  ⊢-nm ← quoteNameTC (_⊢_ {Var})
  ⊢-def ← getDefinition ⊢-nm
  `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
  var-con ← liftTC $ get-var-con 𝕋Sort _⊢_ `-nm
  𝕋-nm ← term→name =<< quoteTC' 𝕋
  VarSort` ← quoteNormTC' (𝕋Sort Var)
  SortTy` ← quoteNormTC' SortTy
  let Sort` : Term' → Term'
      Sort` st = def (quote Kitty.Term.Terms.Terms.Sort) [ argᵥ (def 𝕋-nm []) ; argᵥ st ]
  SortCtx` ← quoteNormTC' (List (𝕋Sort Var))
  let VarScoped` : Term'
      VarScoped` = def (quote Kitty.Term.Terms.Terms.VarScoped) [ argᵥ (def 𝕋-nm []) ]
  Set` ← quoteTC' Set
  let Kit` : Term' → Term'
      Kit` _∋/⊢_ = def (quote Kitty.Term.Kit.Kit) [ argᵥ (def 𝕋-nm []) ; argᵥ _∋/⊢_ ]

  -- _⋯_ ← unquoteTC' {A = ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {S₁ S₂} {M} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M} (def ⋯-nm [])

  let body = lam visible (abs "x" (
             lam visible (abs "f" (
             con (quote refl) []))))

  -- ⋯-var-ty ← quoteTC' (∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ ⦃ 𝕂 : Kit ⦄ {S₁} {S₂} {m} (x : S₁ ∋ m) (f : S₁ –[ 𝕂 ]→ S₂)
  --                      → (ctor var-con x) ⋯ f ≡ Kit.`/id 𝕂 (x & f))
  let 𝕤` = def (quote Kitty.Term.Sub.SubWithLaws.SubWithLaws-Sub) [ argᵥ (var "𝕊" []) ]
  let ⋯-var-ty =
        pi (argₕ (def (quote Level) [])) (abs "ℓ" (
        pi (argᵢ (def (quote Kitty.Term.Sub.SubWithLaws) [ argᵥ (def 𝕋-nm []) ; argᵥ (var "ℓ" []) ])) (abs "𝕊" (
        pi (argₕ VarScoped`) (abs "_∋/⊢_" (
        pi (argᵢ (Kit` (var "_∋/⊢_" []))) (abs "𝕂" (
        pi (argₕ SortCtx`) (abs "S₁" (
        pi (argₕ SortCtx`) (abs "S₂" (
        pi (argₕ VarSort`) (abs "m" (
        pi (argᵥ (def (quote _∋_) [ argᵥ (var "S₁" []) ; argᵥ (var "m" []) ])) (abs "x" (
        pi (argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
                    [ argᵥ 𝕤` ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂" []) ; argᵥ (var "S₂" []) ])) (abs "f" (
        def (quote _≡_) [ argᵥ (def ⋯-nm [ argᵥ (ctor` var-con (var "x" []))
                                          ; argᵥ (var "f" []) ])
                        ; argᵥ (def (quote Kitty.Term.Kit.Kit.`/id)
                            [ argᵥ (var "𝕂" [])
                            ; argᵥ (def (quote Kitty.Term.Sub.Sub._&_) [ argᵥ 𝕤`
                                                                      ; argᵥ (var "x" [])
                                                                      ; argᵥ (var "f" []) ]) ]) ]
        ))))))))))))))))))

  defdecFun'
    (argᵥ ⋯-var-nm)
    ⋯-var-ty
    [ clause [] [] body ]

-- ⋯-var : ∀ {{𝕂 : Kit}} {S₁} {S₂} {m} (x : S₁ ∋ m) (f : S₁ –→ S₂) →
--         (` x) ⋯ f ≡ `/id _ (f _ x)
-- ⋯-var x f = refl

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

tel→args : Telescope' → List (Arg Term')
tel→args [] = []
tel→args ((x , arg i t) ∷ tel) = arg i (var x []) ∷ tel→args tel

S→[]' : String → Term' → Term'
S→[]' `S t₂ =
  let t₂ = rw (λ { ⦃ `Term ⦄ t → case un-++ t of λ where
                      (just (xs , var ys [])) → case `S String.≟ ys of λ where
                                                  (yes _) → just xs
                                                  (no  _) → nothing
                      _                        → nothing
                  ; ⦃ T     ⦄ t → nothing
                  }) t₂
  in t₂ [ `S ↦ con (quote List.List.[]) [] ]

derive-⋯-↑-con : Terms → Name → Name → Name → TC ⊤
derive-⋯-↑-con 𝕋 ⋯-nm con-nm ⋯-↑-con-nm = runFreshT do
  let open Terms 𝕋 renaming (Sort to 𝕋Sort)
  let open Kitty.Term.Kit 𝕋
  let open Kitty.Term.Prelude using (_▷▷_)
  let open Kitty.Term.MultiTraversal 𝕋
  let open Kitty.Term.Sub 𝕋
  let open Sub ⦃ … ⦄
  let open SubWithLaws ⦃ … ⦄

  ⊢-nm ← quoteNameTC (_⊢_ {Var})
  ⊢-def ← getDefinition ⊢-nm
  `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
  𝕋-nm ← term→name =<< quoteTC' 𝕋

  VarSort` ← quoteNormTC' (𝕋Sort Var)
  SortTy` ← quoteNormTC' SortTy
  let Sort` : Term' → Term'
      Sort` st = def (quote Kitty.Term.Terms.Terms.Sort) [ argᵥ (def 𝕋-nm []) ; argᵥ st ]
  SortCtx` ← quoteNormTC' (List (𝕋Sort Var))
  let VarScoped` : Term'
      VarScoped` = def (quote Kitty.Term.Terms.Terms.VarScoped) [ argᵥ (def 𝕋-nm []) ]

  -- _⋯⊤_ ← unquoteTC' {A = ∀ (_ : ⊤) {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {S₁ S₂} {M} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M}
  --                   (lam visible (abs "_" (def ⋯-nm [])))
  -- let open Kitty.Term.MultiSub.TraversalOps' 𝕋 _⋯⊤_
  let ⋯⊤' : Term'
      ⋯⊤' = lam visible (abs "_" (lam instance′ (abs "𝕤" (def ⋯-nm [ argᵢ (var "𝕤" []) ]))))
  let open Kitty.Term.MultiSub.TraversalOps' 𝕋

  -- Get constructor telescope
  c-ty ← getType' con-nm
  let (c-tel , c-ret) = pi→tel c-ty

  -- Retrieve variable name used for `S`
  c-S ← case unterm ⊢-nm c-ret of λ where
    (just (var S [] , M)) → pure S
    (just (S , M)) → liftTC $ failStr "constructed type has to return variable as S."
    nothing → liftTC $ failStr "impossible"

  -- Rename `S` to `S₁` and replace `S` occurences with `S₁ ▷▷ S₁'`
  let c-tel' = List.map (λ { (x , b) → case x String.≟ c-S of λ where
                                          (no _)  → (x , b [ c-S ↦ def (quote _▷▷_) [ argᵥ (var "S₁" []) ; argᵥ (var "S₁'" []) ] ])
                                          (yes _) → ("S₁" , b)
                            }) c-tel

  -- Remove `S₁` binding, since it's already bound on the outside
  let c-tel'x = List.filterᵇ
        (λ { (x , _) → case x String.≟ "S₁" of λ { (yes _) → false; (no _) → true } })
        c-tel'

  KitPkg` ← quoteTC' (Kitty.Term.MultiSub.KitPkg 𝕋)
  let unpack-kit` : Term' → Term'
      unpack-kit` KP = def (quote Kitty.Term.MultiSub.unpack-kit) [ argᵥ (def 𝕋-nm []) ; argᵥ KP ]
  Kits` ← quoteTC' (List (Kitty.Term.MultiSub.KitPkg 𝕋))
  let SubWithLaws` : Term' → Term'
      SubWithLaws` ℓ = def (quote Kitty.Term.Sub.SubWithLaws) [ argᵥ (def 𝕋-nm []) ; argᵥ ℓ ]

  let 𝕤 = def (quote Kitty.Term.Sub.SubWithLaws.SubWithLaws-Sub)
            [ argᵥ (var "𝕊" [])
            ]

  -- Convert tel bindings (x , t) to var arguments, but replace `S₁` with `S₁ ▷▷ S₁'`
  let con-term = con con-nm $ List.map
                    (λ where (x , arg i _) → case x String.≟ "S₁" of λ where
                              (yes _) → arg i (def (quote _▷▷_)
                                                    [ argᵥ (var "S₁" [])
                                                    ; argᵥ (var "S₁'" []) ])
                              (no _) → arg i (var x [])
                    )
                    c-tel'
  -- ((λx t) ⋯* (f ↑** S₁')) ≡ λx (t ⋯* (f ↑** S₁' ↑** [ 𝕖 ]))
  let _⋯*`_ = (Term' → Term' → Term') by
                λ t fs → def (quote Kitty.Term.MultiSub.TraversalOps'._⋯*_)
                        [ argᵥ (def 𝕋-nm [])
                        ; argᵥ ⋯⊤'
                        ; argᵢ 𝕤
                        ; argᵥ t
                        ; argᵥ fs
                        ]
  let _↑**`_ = (Term' → Term' → Term') by
                λ fs S → def (quote Kitty.Term.MultiSub._↑**_)
                              [ argᵥ (def 𝕋-nm []) ; argᵢ 𝕤 ; argᵥ fs ; argᵥ S ]
  let lhs = con-term ⋯*` (var "fs" [] ↑**` var "S₁'" [])
  let rhs = con con-nm $ List.map
                    (λ where (x , arg i t) → case x String.≟ c-S of λ where
                              (yes _) → arg i (def (quote _▷▷_)
                                                    [ argᵥ (var "S₂" [])
                                                    ; argᵥ (var "S₁'" []) ])
                              (no _) → case unterm ⊢-nm t of λ where
                                          (just (S , _)) → let S' = S→[]' c-S S in
                                                          arg i (var x [] ⋯*` ((var "fs" [] ↑**` var "S₁'" []) ↑**` S'))
                                          nothing        → arg i (var x [])
                    )
                    c-tel

  let ⋯-↑-con-ty = tel→pi
        ( [ ("ℓ"   , argₕ (def (quote Level) []))
          ; ("𝕊"   , argᵢ (SubWithLaws` (var "ℓ" [])))
          ; ("𝕂s"  , argₕ Kits`)
          ; ("S₁"  , argₕ SortCtx`) 
          ; ("S₂"  , argₕ SortCtx`) 
          ; ("S₁'" , argₕ SortCtx`)
          ; ("fs"  , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                          [ argᵥ (def 𝕋-nm []) ; argᵢ 𝕤 ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂s" []) ; argᵥ (var "S₂" []) ]))
          ] ++ c-tel'x)
        (def (quote _≡_) [ argᵥ lhs ; argᵥ rhs ])

  let mk-tel 𝕂s-binds fs-binds = Telescope' by
        ([ ("ℓ"   , argₕ (def (quote Level) []))
          ; ("𝕊"   , argᵢ (SubWithLaws` (var "ℓ" [])))
          ] ++
          𝕂s-binds ++
          [ ("S₁" , argₕ SortCtx`)
          ; ("S₂" , argₕ SortCtx`)
          ; ("S₁'" , argₕ SortCtx`)
          ] ++
          fs-binds ++
          c-tel'x)
  let c-pats = List (Arg Pattern') by
                List.map (λ { (x , arg i _) → arg i (var x) }) c-tel'x
  let mk-pats 𝕂s-pats fs-pats = List (Arg Pattern') by
        [ argₕ (var "ℓ")
        ; argᵢ (var "𝕊") ] ++
        𝕂s-pats ++
        [ argₕ (var "S₁")
        ; argₕ (var "S₂")
        ; argₕ (var "S₁'")
        ] ++ fs-pats ++ c-pats

  -- ⋯-↑-λ : ∀ {𝕂s : List Kit} {S₁ S₂ S₁'} (f : S₁ –[ 𝕂s ]→* S₂)
  --         → (t : (S₁ ▷▷ S₁' ▷ 𝕖) ⊢ 𝕖)
  --         → ((λx t) ⋯* (f ↑** S₁')) ≡ λx (t ⋯* (f ↑** S₁' ↑** [ 𝕖 ]))

  -- ⋯-↑-λ           []       t = refl
  let clause₁ = clause
        (mk-tel [] [])
        (mk-pats [ argₕ (con (quote Agda.Builtin.List.List.[]) []) ]
                  [ argᵥ (con (quote Kitty.Util.Star.Star.[]) []) ])
        (con (quote refl) [])

  -- ⋯-↑-λ {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-λ fs t) refl
  let con-args = List.map
                    (λ where (x , arg i _) → arg i (var x []))
                    c-tel'x
  let rec = def ⋯-↑-con-nm ([ argᵢ (var "𝕊" []) ; argᵥ (var "fs" []) ] ++ con-args)
  let clause₂ = clause
        (mk-tel [ ("𝕂" , argₕ KitPkg`) ; ("𝕂s" , argₕ Kits`) ]
                [ ("Sₓ" , argₕ SortCtx`)
                ; ("f" , argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
                      [ argᵥ 𝕤
                      ; argᵥ (var "Sₓ" []) ; argᵥ (unpack-kit` (var "𝕂" [])) ; argᵥ (var "S₂" []) ]))
                ; ("fs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                      [ argᵥ (def 𝕋-nm [])
                      ; argᵢ 𝕤
                      ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂s" []) ; argᵥ (var "Sₓ" []) ]))
                ])
        (mk-pats [ argₕ (con (quote Agda.Builtin.List.List._∷_) [ argᵥ (var "𝕂") ; argᵥ (var "𝕂s") ]) ]
                 [ argᵥ (con (quote Kitty.Util.Star._∷_) [ argₕ (dot (var "S₂" []))
                                                         ; argₕ (var "Sₓ")
                                                         ; argₕ (dot (var "S₁" []))
                                                         ; argᵥ (var "f") ; argᵥ (var "fs") ])
                 ])
        (def (quote cong₂)
          [ argᵥ (def ⋯-nm [ argᵢ 𝕤 ; argᵢ (unpack-kit` (var "𝕂" [])) ])
          ; argᵥ rec
          ; argᵥ (con (quote refl) [])
          ])

  defdecFun'
    (argᵥ ⋯-↑-con-nm)
    ⋯-↑-con-ty
    [ clause₁ ; clause₂ ]

derive-⋯-↑ : Terms → Name → Name → TC ⊤
derive-⋯-↑ 𝕋 ⋯-nm ⋯-↑-nm = runFreshT do
  let open Terms 𝕋 renaming (Sort to 𝕋Sort)
  let open Kitty.Term.Kit 𝕋
  let open Kitty.Term.Prelude using (_▷▷_)
  let open Kitty.Term.MultiTraversal 𝕋
  let open Kitty.Term.Sub 𝕋
  let open Kitty.Term.MultiSub 𝕋
  let open Sub ⦃ … ⦄
  let open SubWithLaws ⦃ … ⦄

  ⊢-nm ← quoteNameTC (_⊢_ {Var})
  ⊢-def ← getDefinition ⊢-nm
  `-nm , con-nms ← split-term-ctors (ctors ⊢-def)

  var-con ← liftTC $ get-var-con 𝕋Sort _⊢_ `-nm
  𝕋-nm ← term→name =<< quoteTC' 𝕋
  VarSort` ← quoteNormTC' (𝕋Sort Var)
  SortTy` ← quoteNormTC' SortTy
  let Sort` : Term' → Term'
      Sort` st = def (quote Kitty.Term.Terms.Terms.Sort) [ argᵥ (def 𝕋-nm []) ; argᵥ st ]
  SortCtx` ← quoteNormTC' (List (𝕋Sort Var))
  let VarScoped` : Term'
      VarScoped` = def (quote Kitty.Term.Terms.Terms.VarScoped) [ argᵥ (def 𝕋-nm []) ]

  Kits` ← quoteTC' (List (Kitty.Term.MultiSub.KitPkg 𝕋))
  let SubWithLaws` : Term' → Term'
      SubWithLaws` ℓ = def (quote Kitty.Term.Sub.SubWithLaws) [ argᵥ (def 𝕋-nm []) ; argᵥ ℓ ]

  -- _⋯_ ← unquoteTC' {A = ∀ {ℓ} ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ℓ ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {S₁ S₂} {M} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M} (def ⋯-nm [])
  -- _⋯⊤_ ← unquoteTC' {A = ∀ (_ : ⊤) {ℓ} ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ℓ ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {S₁ S₂} {M} → S₁ ⊢ M → S₁ –[ 𝕂 ]→ S₂ → S₂ ⊢ M} (lam visible (abs "_" (def ⋯-nm [])))
  -- let open Kitty.Term.MultiSub.TraversalOps' 𝕋 _⋯⊤_
  let ⋯⊤` : Term'
      ⋯⊤` = lam visible (abs "_" (lam instance′ (abs "𝕤" (def ⋯-nm [ argᵢ (var "𝕤" []) ]))))
  let open Kitty.Term.MultiSub.TraversalOps' 𝕋

  let mk-tel c-tel =
        [ "ℓ", argₕ (def (quote Level) [])
        ; "𝕊" , argᵢ (SubWithLaws` (var "ℓ" []))
        ; "𝕂s₁" , argₕ Kits`
        ; "𝕂s₂" , argₕ Kits`
        ; "S₁" , argₕ SortCtx`
        ; "S₂" , argₕ SortCtx`
        ; "fs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
            [ argᵥ (def 𝕋-nm [])
            ; argᵥ (var "S₁" [])
            ; argᵥ (var "𝕂s₁" [])
            ; argᵥ (var "S₂" [])
            ])
        ; "gs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
            [ argᵥ (def 𝕋-nm [])
            ; argᵥ (var "S₁" [])
            ; argᵥ (var "𝕂s₂" [])
            ; argᵥ (var "S₂" [])
            ])
        ; "fs≈gs" , argᵥ (def (quote Kitty.Term.MultiSub.TraversalOps'._≈ₓ_)
            [ argᵥ (def 𝕋-nm [])
            ; argᵥ ⋯⊤`
            ; argᵥ (var "fs" [])
            ; argᵥ (var "gs" [])
            ])
        ; "S₁'" , argₕ SortCtx`
        ] ++ c-tel
  let mk-pats c-pat = 
        [ argₕ (var "ℓ")
        ; argᵢ (var "𝕊")
        ; argₕ (var "𝕂s₁")
        ; argₕ (var "𝕂s₂")
        ; argₕ (var "S₁")
        ; argₕ (var "S₂")
        ; argᵥ (var "fs" )
        ; argᵥ (var "gs" )
        ; argᵥ (var "fs≈gs" )
        ; argₕ (var "S₁'")
        ] ++ c-pat ∷ []

  non-var-clauses ← forM (enumerate con-nms) λ (i , c) → do
    ⋯-↑-con-nm ← freshName "⋯-↑-con"
    liftTC (derive-⋯-↑-con 𝕋 ⋯-nm c ⋯-↑-con-nm)

    -- Get constructor telescope
    c-ty ← getType' c
    let (c-tel , c-ret) = pi→tel c-ty

    -- Retrieve variable name used for `S`
    c-S ← case unterm ⊢-nm c-ret of λ where
      (just (var S [] , M)) → pure S
      (just (S , M)) → liftTC $ failStr "constructed type has to return variable as S."
      nothing → liftTC $ failStr "impossible"

    -- Rename `S` to `S₁` and replace `S` occurences with `S₁ ▷▷ S₁'`
    let c-tel' = List.map (λ { (x , b) → case x String.≟ c-S of λ where
                                            (no _)  → (x , b [ c-S ↦ def (quote _▷▷_) [ argᵥ (var "S₁" []) ; argᵥ (var "S₁'" []) ] ])
                                            (yes _) → ("S₁" , b)
                              }) c-tel

    -- Remove `S₁` binding, since it's already bound on the outside
    let c-tel'x = List.filterᵇ
          (λ { (x , _) → case x String.≟ "S₁" of λ { (yes _) → false; (no _) → true } })
          c-tel'

    -- Convert tel bindings (x , t) to var patterns, but replace `S₁` with `S₁ ▷▷ S₁'`
    let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-S of λ where
                                                  (no _)  → arg i (var x)
                                                  (yes _) → arg i (dot (def (quote _▷▷_)
                                                    [ argᵥ (var "S₁" [])
                                                    ; argᵥ (var "S₁'" []) ]))
                              }) c-tel
    let c-pat = argᵥ (con c c-pats)


    let ⋯-↑-con` = (Term' → Term' → Term') by λ 𝕂s fs →
          def ⋯-↑-con-nm
            ([ argₕ unknown
              ; argₕ 𝕂s
              ; argₕ (var "S₁" [])
              ; argₕ (var "S₂" [])
              ; argₕ (var "S₁'" [])
              ; argᵥ fs
              ] ++ List.map (λ { (x , arg i t) → arg i (var x []) }) c-tel'x)
    let sym` = (Term' → Term') by λ eq → def (quote sym) [ argᵥ eq ]
    let trans` = (Term' → Term' → Term') by λ eq₁ eq₂ → def (quote trans) [ argᵥ eq₁ ; argᵥ eq₂ ]
    let 𝕂s₁` = Term' by (var "𝕂s₁" [])
    let 𝕂s₂` = Term' by (var "𝕂s₂" [])
    let fs` = Term' by (var "fs" [])
    let gs` = Term' by (var "gs" [])
    let S₁'` = Term' by (var "S₁'" [])
    let fs≈gs` = Term' by (var "fs≈gs" [])
    let cong` = (Term' → Term' → Term') by λ f eq → def (quote cong) [ argᵥ f ; argᵥ eq ]
    let _⋯*`_ = (Term' → Term' → Term') by
                  λ t fs → def (quote Kitty.Term.MultiSub.TraversalOps'._⋯*_)
                          [ argᵥ (def 𝕋-nm [])
                          ; argᵥ ⋯⊤`
                          ; argᵥ t
                          ; argᵥ fs
                          ]
    let _↑**`_ = (Term' → Term' → Term') by
                  λ fs S → def (quote Kitty.Term.MultiSub._↑**_)
                              [ argᵥ (def 𝕋-nm []) ; argᵥ fs ; argᵥ S ]
    let ⋯-↑` = (Term' → Term' → Term' → Term' → Term') by λ fs gs fs≈gs t →
                def ⋯-↑-nm [ argᵥ fs ; argᵥ gs ; argᵥ fs≈gs ; argᵥ t ]
    let ≈↑**` = (Term' → Term' → Term' → Term') by λ fs gs fs≈gs →
                def (quote Kitty.Term.MultiSub.TraversalOps'.≈↑**)
                    [ argᵥ (def 𝕋-nm [])
                    ; argᵥ ⋯⊤`
                    ; argᵥ fs ; argᵥ gs ; argᵥ fs≈gs
                    ]

    let rec = (Term' → Term') by λ t →
          ⋯-↑` (fs` ↑**` S₁'`) (gs` ↑**` S₁'`) (≈↑**` fs` gs` fs≈gs`) t

    let tel-rec , tel-non-rec = splitRec c-tel ⊢-nm
    let rec-ids = map proj₁ tel-rec
    let non-rec-ids = map proj₁ tel-non-rec
    cong-name ← freshName "cong-n"
    cong-n (length rec-ids) cong-name
    let cong-fun = tel→lam tel-rec $ con c $
                    List.map (λ{ (x , arg i t) → case x String.≟ c-S of λ where
                                    (no _)  → arg i (var x [])
                                    (yes _) → arg i (def (quote _▷▷_)
                                                      [ argᵥ (var "S₂" [])
                                                      ; argᵥ (var "S₁'" []) ])
                                }) c-tel

    let eqq = def cong-name (argᵥ cong-fun ∷ List.map (λ x → argᵥ (rec (var x []))) rec-ids)

    let body = trans` (⋯-↑-con` 𝕂s₁` fs`) (
                trans` eqq
                      (sym` (⋯-↑-con` 𝕂s₂` gs`)))

    pure $ clause
      (mk-tel c-tel'x)
      (mk-pats c-pat)
      body

  -- ⋯-↑-ty ← quoteTC' (
  --     ∀ {ℓ} ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {S₁} {S₂} (f : S₁ –[ 𝕂s₁ ]→* S₂) (g : S₁ –[ 𝕂s₂ ]→* S₂) →
  --       f ≈ₓ g → f ≈ₜ g
  --   )
  let ⋯-↑-ty =
        pi (argₕ (def (quote Level) [])) (abs "ℓ" (
        pi (argᵢ (def (quote Kitty.Term.Sub.SubWithLaws) [ argᵥ (def 𝕋-nm []) ; argᵥ (var "ℓ" []) ])) (abs "𝕊" (
        pi (argₕ Kits`) (abs "𝕂s₁" (
        pi (argₕ Kits`) (abs "𝕂s₂" (
        pi (argₕ SortCtx`) (abs "S₁" (
        pi (argₕ SortCtx`) (abs "S₂" (
        pi (argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                    [ argᵥ (def 𝕋-nm []) ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂s₁" []) ; argᵥ (var "S₂" []) ])) (abs "f" (
        pi (argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                    [ argᵥ (def 𝕋-nm []) ; argᵥ (var "S₁" []) ; argᵥ (var "𝕂s₂" []) ; argᵥ (var "S₂" []) ])) (abs "g" (
        pi (argᵥ (def (quote Kitty.Term.MultiSub.TraversalOps'._≈ₓ_)
                    [ argᵥ (def 𝕋-nm [])
                    ; argᵥ ⋯⊤`
                    ; argᵥ (var "f" [])
                    ; argᵥ (var "g" []) ])) (abs "_" (
        (def (quote Kitty.Term.MultiSub.TraversalOps'._≈ₜ_)
                    [ argᵥ (def 𝕋-nm [])
                    ; argᵥ ⋯⊤`
                    ; argᵥ (var "f" [])
                    ; argᵥ (var "g" []) ])
        ))))))))))))))))))

  let var-clause = clause
        (mk-tel [ "x" , argᵥ (def (quote _∋_) [ argᵥ (def (quote List._++_)
                                                        [ argᵥ (var "S₁'" [])
                                                        ; argᵥ (var "S₁" [])
                                                        ])
                                              ; argᵥ unknown
                                              ])
                ])
        (mk-pats (argᵥ (pat` var-con (var "x"))))
        (var "fs≈gs" [ argᵥ (var "x" []) ])

  defdecFun'
    (argᵥ ⋯-↑-nm)
    ⋯-↑-ty
    (var-clause ∷ non-var-clauses)

derive-MultiTraversal-record : Terms → Name → Name → Name → Name → TC ⊤
derive-MultiTraversal-record 𝕋 ⋯-nm ⋯-var-nm ⋯-↑-nm kit-traversal-nm = runFreshT do
  𝕋-nm ← term→name =<< quoteTC' 𝕋
  let body =
        con (quote Kitty.Term.MultiTraversal.mkMultiTraversal)
          [ argᵥ (def ⋯-nm [])
          ; argᵥ (def ⋯-var-nm [])
          ; argᵥ (def ⋯-↑-nm [])
          ]
  defdecFun'
    (argᵥ kit-traversal-nm)
    (def (quote Kitty.Term.MultiTraversal.MultiTraversal) [ argᵥ (def 𝕋-nm []) ])
    [ clause [] [] body ]

derive-MultiTraversal : (Sort : SortTy → Set) → (_⊢_ : ∀ {st} → List (Sort Var) → Sort st → Set) → Name → TC ⊤
derive-MultiTraversal Sort _⊢_ traversal-nm = do
  liftTC $ printStr "Deriving Terms"
  terms-nm ← freshName "terms"
  derive-Terms Sort _⊢_ terms-nm
  terms ← unquoteTC {A = Terms} (def terms-nm [])

  liftTC $ printStr "Deriving ⋯"
  ⋯-nm ← freshName "⋯"
  derive-⋯ terms ⋯-nm

  liftTC $ printStr "Deriving ⋯-var"
  ⋯-var-nm ← freshName "⋯-var"
  derive-⋯-var terms ⋯-nm ⋯-var-nm

  liftTC $ printStr "Deriving ⋯-↑"
  ⋯-↑-nm ← freshName "⋯-↑"
  derive-⋯-↑ terms ⋯-nm ⋯-↑-nm

  derive-MultiTraversal-record terms ⋯-nm ⋯-var-nm ⋯-↑-nm traversal-nm
