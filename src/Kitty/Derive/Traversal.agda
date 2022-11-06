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
  -- let VarMode` = def (quote Kitty.Modes.Modes.VarMode) [ argᵥ (def 𝕄-nm []) ]
  -- let VarModes` = def (quote List) [ argᵥ VarMode` ]
  -- let Kit` = def (quote Kitty.Kit.Kit) [ argᵥ (def 𝕋-nm []) ]
  VarMode` ← quoteNormTC' VarMode
  VarModes` ← quoteNormTC' (List VarMode)
  Kit` ← quoteTC' Kit
  -- let VarMode` = def (quote VarMode) []
  -- let VarModes` = def (quote List) [ argᵥ (def (quote VarMode) []) ]
  -- let Kit` = def (quote Kitty.Kit.Kit) [ argᵥ 𝕋` ]
  -- clauses ← forM (enumerate con-nms) λ (i , c) → do
  --   c-ty ← getType' c
  --   -- c-ty ← liftTC $ µ→[] c-ty
  --   -- let (c-tel , c-ret) = pi→tel c-ty
  --   -- end-ty ← case c-ret of λ where
  --   --   (def f [ µ ; M ]) → pure (Term' by con (quote `■) [ M ])
  --   --   _                 → liftTC $ failStr "Unexpected constructor type"
  --   -- let desc = foldr' c-tel end-ty λ where
  --   --       (x , arg i arg-ty) desc → case unterm Term-nm arg-ty of λ where
  --   --         (just (µ , M)) →
  --   --           con (quote `X) [ argᵥ µ ; argᵥ M ; argᵥ desc ]
  --   --         nothing →
  --   --           con (quote `σ)
  --   --             [ argᵥ arg-ty
  --   --             ; argᵥ (lam visible (abs x desc))
  --   --             ]
  --   -- pure $ clause [] [ argᵥ (fin-pat' i) ] desc
  --   pure {!!}
  let clauses = []
  let var-clause = clause [ "𝕂" , argᵢ Kit`
                          ; "µ₁" , argₕ VarModes`
                          ; "µ₂" , argₕ VarModes`
                          ; "x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ₁" [])
                                                        ; argᵥ unknown
                                                        ])
                          ; "f" , argᵥ (def (quote Kitty.Kit._–[_]→_) [ argᵥ (def 𝕋-nm [])
                                                                      ; argᵥ (var "µ₁" [])
                                                                      ; argᵥ (var "𝕂" [])
                                                                      ; argᵥ (var "µ₂" [])
                                                                      ])
                          ]
                          [ argᵢ (var "𝕂")
                          ; argₕ (var "µ₁")
                          ; argₕ (var "µ₂")
                          ; argᵥ (con `-nm [ argᵥ (var "x") ])
                          ; argᵥ (var "f" )
                          ]
                          (def (quote Kit.`/id)
                            [ argᵥ (var "𝕂" [])
                            ; argᵥ unknown
                            ; argᵥ (var "f" [ argᵥ unknown
                                            ; argᵥ (var "x" [])
                                            ])
                            ])
  let clauses = var-clause ∷ clauses
  liftTC $ printAST var-clause
  ⋯-ty ← quoteTC' (∀ ⦃ 𝕂 : Kit ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M)
  liftTC $ printAST ⋯-ty
  defdecFun'
    (argᵥ ⋯-nm)
    ⋯-ty
    clauses

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

  module Custom where
    _⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    -- _⋯_ ⦃ 𝕂 ⦄ {µ₁} {µ₂} (`_ {.(µ₁)} {m} x) f = `/id m (f m x)
    (` x)     ⋯ f = `/id _ (f _ x)
    (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
    (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
    (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

  unquoteDecl _⋯_ = deriveTraversal terms _⋯_

  -- xx = {!terms!}
