{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive.Traversal where

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
open import Kitty.Experimental.KitAltSimple
open import Kitty.Derive.Common
import Kitty.Kit

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ

open Modes using (Scoped)

deriveTerms : (𝕄 : Modes) → (_⊢_ : Scoped 𝕄) → Name → TC ⊤
deriveTerms 𝕄 _⊢_ terms-nm = runFreshT do
  let open Modes 𝕄
  𝕄-nm ← quoteNameTC 𝕄
  ⊢-nm ← quoteNameTC _⊢_
  ⊢-def ← getDefinition ⊢-nm
  `-nm , _ ← split-term-ctors (ctors ⊢-def)
  `_ ← unquoteTC' {A = ∀ {µ m} → µ ∋ m → µ ⊢ m→M m} (con `-nm [])
  terms-ty ← quoteTC' (Terms 𝕄)
  terms-body ← quoteTC' (mkTerms _⊢_ (λ {µ} → `_ {µ}))
  -- let terms-ty = def (quote Terms) [ argᵥ (def 𝕄-nm []) ]
  -- let terms-body = def (quote mkTerms) [ argᵥ (def ⊢-nm []) ; argᵥ (con `-nm []) ] 
  defdecFun'
    (argᵥ terms-nm)
    terms-ty
    [ clause [] [] terms-body ]

record DeriveContext : Set₁ where
  field
    𝕄 : Modes
    𝕋 : Terms 𝕄

    `𝕄 : Name
    `𝕋 : Name
    `⊢ : Name
    `VarMode : Name
    `TermMode : Name
    `Kit : Name
    `⋯ : Name

    `var : Name
    `cons : List Name
    con-tys : List Type'
    con-tels : List Telescope'

  open Modes 𝕄 public
  open Terms 𝕋 public
  open Kitty.Kit 𝕋 public

postulate TODO : ∀ {ℓ} {A : Set ℓ} → A

deriveTraversal : {𝕄 : Modes} → Terms 𝕄 → Name → TC ⊤
deriveTraversal {𝕄} 𝕋 ⋯-nm = runFreshT do
  liftTC $ printAST "FUCK YOU FUCK YOU FUCK YOU"
  let open Modes 𝕄
  let open Terms 𝕋
  let open Kitty.Kit 𝕋
  𝕄-nm ← quoteNameTC 𝕄
  ⊢-nm ← quoteNameTC _⊢_
  ⊢-def ← getDefinition ⊢-nm
  `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
  𝕋-nm ← term→name =<< quoteTC' 𝕋
  VarMode` ← quoteNormTC' VarMode
  VarModes` ← quoteNormTC' (List VarMode)
  Kit` ← quoteTC' Kit

  let mk-tel c-tel =
        [ "𝕂" , argᵢ Kit`
        ; "µ₁" , argₕ VarModes`
        ; "µ₂" , argₕ VarModes`
        ] ++ c-tel ++
        [ "f" , argᵥ (def (quote Kitty.Kit._–[_]→_)
            [ argᵥ (def 𝕋-nm [])
            ; argᵥ (var "µ₁" [])
            ; argᵥ (var "𝕂" [])
            ; argᵥ (var "µ₂" [])
            ])
        ]
  let mk-pats c-pat = 
        [ argᵢ (var "𝕂")
        ; argₕ (var "µ₁")
        ; argₕ (var "µ₂")
        ] ++ c-pat ∷
        [ argᵥ (var "f" ) ]

  clauses ← forM (enumerate con-nms) λ (i , c) → do
    liftTC $ printAST c
    c-ty ← getType' c
    let (c-tel , c-ret) = pi→tel c-ty
    liftTC $ printAST c-tel
    c-µ ← case unterm ⊢-nm c-ret of λ where
      (just (var µ [] , M)) → pure µ
      (just (µ , M)) → liftTC $ failStr "constructed type has to return variable as µ."
      nothing → liftTC $ failStr "impossible"
    let c-tel' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                           (no _)  → (x , b [ c-µ ↦ var "µ₁" [] ])
                                           (yes _) → ("µ₁" , b)
                             }) c-tel
    let c-tel'x = List.boolFilter
          (λ { (x , _) → case x String.≟ "µ₁" of λ { (yes _) → false; (no _) → true } })
          c-tel'
    let c-tel'' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                            (no _)  → (x , b [ c-µ ↦ var "µ₂" [] ])
                                            (yes _) → ("µ₂" , b)
                              }) c-tel
    liftTC $ printAST c-tel'
    let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-µ of λ where
                                                 (no _)  → arg i (var x)
                                                 (yes _) → arg i (dot (var "µ₁" []))
                             }) c-tel'
    let c-pat = argᵥ (con c c-pats)
    let body = con c $ foldr' c-tel'' [] λ where
          (s , arg i t) c-args → _∷ c-args $ case unterm ⊢-nm t of λ where
            (just _) → arg i (def ⋯-nm [ argᵥ (var s [])
                                       ; argᵥ (def (quote Kitty.Kit.Kit._↑*_)
                                           [ argᵥ (var "𝕂" [])
                                           ; argᵥ (var "f" [])
                                           ; argᵥ unknown
                                           ])
                                       ]) 
            nothing  → case s String.≟ c-µ of λ where
                          (no _)  → arg i (var s [])
                          (yes _) → arg i (var "µ₂" [])
    pure $ clause (mk-tel c-tel'x) (mk-pats c-pat) body

  let var-tel = [ "x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ₁" [])
                                              ; argᵥ unknown
                                              ])
                ]
  let var-pat = argᵥ (con `-nm [ argᵥ (var "x") ])
  let var-clause = clause (mk-tel var-tel)
                          (mk-pats var-pat)
                          (def (quote Kit.`/id)
                            [ argᵥ (var "𝕂" [])
                            ; argᵥ unknown
                            ; argᵥ (var "f" [ argᵥ unknown
                                            ; argᵥ (var "x" [])
                                            ])
                            ])

  ⋯-ty ← quoteTC' (∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M)

  defdecFun'
    (argᵥ ⋯-nm)
    ⋯-ty
    (var-clause ∷ clauses)

-- _⋯_ : ∀ {µ₁} {µ₂} {M} {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
-- (` x)     ⋯ f = `/id _ (f _ x)
-- (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
-- (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
-- (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

module Example where
  open Kitty.Prelude

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `_    : ∀ {µ m}  →  µ ∋ m  →  µ ⊢ m→M m
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  unquoteDecl terms = deriveTerms 𝕄 _⊢_ terms

  open Kitty.Kit terms
  open Kit ⦃ ... ⦄

  -- module Custom where
  --   _⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  --   -- _⋯_ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (`_ {.(µ₁)} {m} x) f = `/id m (f m x)
  --   (` x)     ⋯ f = `/id _ (f _ x)
  --   (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
  --   (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
  --   (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

  open Terms terms
  unquoteDecl _⋯_ = deriveTraversal terms _⋯_


  -- xx = {!_⋯_!}
