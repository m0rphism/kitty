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
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Function using (_∘_; _$_; case_of_)
open ≡-Reasoning

open import Kitty.Prelude using (_∋_)
open import Kitty.Modes
-- open import Kitty.Experimental.KitAltSimple
import Kitty.Experimental.KitAltSimple
open import Kitty.Experimental.Star
open import Kitty.Derive.Common
import Kitty.Kit

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
  A B C : Set ℓ

open Modes using (Scoped)

-- derive-Terms : (𝕄 : Modes) → (_⊢_ : Scoped 𝕄) → Name → TC ⊤
-- derive-Terms 𝕄 _⊢_ terms-nm = runFreshT do
--   let open Modes 𝕄
--   𝕄-nm ← quoteNameTC 𝕄
--   ⊢-nm ← quoteNameTC _⊢_
--   ⊢-def ← getDefinition ⊢-nm
--   `-nm , _ ← split-term-ctors (ctors ⊢-def)
--   `_ ← unquoteTC' {A = ∀ {µ m} → µ ∋ m → µ ⊢ m→M m} (con `-nm [])
--   terms-ty ← quoteTC' (Terms 𝕄)
--   terms-body ← quoteTC' (mkTerms _⊢_ (λ {µ} → `_ {µ}))
--   -- let terms-ty = def (quote Terms) [ argᵥ (def 𝕄-nm []) ]
--   -- let terms-body = def (quote mkTerms) [ argᵥ (def ⊢-nm []) ; argᵥ (con `-nm []) ] 
--   defdecFun'
--     (argᵥ terms-nm)
--     terms-ty
--     [ clause [] [] terms-body ]

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

-- postulate TODO : ∀ {ℓ} {A : Set ℓ} → A

-- derive-⋯ : {𝕄 : Modes} → Terms 𝕄 → Name → TC ⊤
-- derive-⋯ {𝕄} 𝕋 ⋯-nm = runFreshT do
--   let open Modes 𝕄
--   let open Terms 𝕋
--   let open Kitty.Kit 𝕋
--   𝕄-nm ← quoteNameTC 𝕄
--   ⊢-nm ← quoteNameTC _⊢_
--   ⊢-def ← getDefinition ⊢-nm
--   `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
--   𝕋-nm ← term→name =<< quoteTC' 𝕋
--   VarMode` ← quoteNormTC' VarMode
--   VarModes` ← quoteNormTC' (List VarMode)
--   Kit` ← quoteTC' Kit

--   let mk-tel c-tel =
--         [ "𝕂" , argᵢ Kit`
--         ; "µ₁" , argₕ VarModes`
--         ; "µ₂" , argₕ VarModes`
--         ] ++ c-tel ++
--         [ "f" , argᵥ (def (quote Kitty.Kit._–[_]→_)
--             [ argᵥ (def 𝕋-nm [])
--             ; argᵥ (var "µ₁" [])
--             ; argᵥ (var "𝕂" [])
--             ; argᵥ (var "µ₂" [])
--             ])
--         ]
--   let mk-pats c-pat = 
--         [ argᵢ (var "𝕂")
--         ; argₕ (var "µ₁")
--         ; argₕ (var "µ₂")
--         ] ++ c-pat ∷
--         [ argᵥ (var "f" ) ]

--   clauses ← forM (enumerate con-nms) λ (i , c) → do
--     c-ty ← getType' c
--     let (c-tel , c-ret) = pi→tel c-ty
--     c-µ ← case unterm ⊢-nm c-ret of λ where
--       (just (var µ [] , M)) → pure µ
--       (just (µ , M)) → liftTC $ failStr "constructed type has to return variable as µ."
--       nothing → liftTC $ failStr "impossible"
--     let c-tel' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
--                                            (no _)  → (x , b [ c-µ ↦ var "µ₁" [] ])
--                                            (yes _) → ("µ₁" , b)
--                              }) c-tel
--     let c-tel'x = List.boolFilter
--           (λ { (x , _) → case x String.≟ "µ₁" of λ { (yes _) → false; (no _) → true } })
--           c-tel'
--     let c-tel'' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
--                                             (no _)  → (x , b [ c-µ ↦ var "µ₂" [] ])
--                                             (yes _) → ("µ₂" , b)
--                               }) c-tel
--     let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-µ of λ where
--                                                  (no _)  → arg i (var x)
--                                                  (yes _) → arg i (dot (var "µ₁" []))
--                              }) c-tel'
--     let c-pat = argᵥ (con c c-pats)
--     let body = con c $ foldr' c-tel'' [] λ where
--           (s , arg i t) c-args → _∷ c-args $ case unterm ⊢-nm t of λ where
--             (just _) → arg i (def ⋯-nm [ argᵥ (var s [])
--                                        ; argᵥ (def (quote Kitty.Kit.Kit._↑*_)
--                                            [ argᵥ (var "𝕂" [])
--                                            ; argᵥ (var "f" [])
--                                            ; argᵥ unknown
--                                            ])
--                                        ]) 
--             nothing  → case s String.≟ c-µ of λ where
--                           (no _)  → arg i (var s [])
--                           (yes _) → arg i (var "µ₂" [])
--     pure $ clause (mk-tel c-tel'x) (mk-pats c-pat) body

--   let var-tel = [ "x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ₁" [])
--                                               ; argᵥ unknown
--                                               ])
--                 ]
--   let var-pat = argᵥ (con `-nm [ argᵥ (var "x") ])
--   let var-clause = clause (mk-tel var-tel)
--                           (mk-pats var-pat)
--                           (def (quote Kitty.Kit.Kit.`/id)
--                             [ argᵥ (var "𝕂" [])
--                             ; argᵥ unknown
--                             ; argᵥ (var "f" [ argᵥ unknown
--                                             ; argᵥ (var "x" [])
--                                             ])
--                             ])

--   ⋯-ty ← quoteTC' (∀ ⦃ 𝕂 : Kitty.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M)

--   defdecFun'
--     (argᵥ ⋯-nm)
--     ⋯-ty
--     (var-clause ∷ clauses)

-- -- _⋯_ : ∀ {µ₁} {µ₂} {M} {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
-- -- (` x)     ⋯ f = `/id _ (f _ x)
-- -- (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
-- -- (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
-- -- (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

-- derive-⋯-var : {𝕄 : Modes} → Terms 𝕄 → Name → Name → TC ⊤
-- derive-⋯-var {𝕄} 𝕋 ⋯-nm ⋯-var-nm = runFreshT do
--   let open Modes 𝕄
--   let open Terms 𝕋
--   let open Kitty.Kit 𝕋
--   𝕄-nm ← quoteNameTC 𝕄
--   ⊢-nm ← quoteNameTC _⊢_
--   ⊢-def ← getDefinition ⊢-nm
--   `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
--   𝕋-nm ← term→name =<< quoteTC' 𝕋

--   _⋯_ ← unquoteTC' {A = ∀ ⦃ 𝕂 : Kitty.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M} (def ⋯-nm [])

--   let body = lam visible (abs "x" (
--              lam visible (abs "f" (
--              con (quote refl) []))))
--   ⋯-var-ty ← quoteTC' (∀ {{𝕂 : Kit}} {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –[ 𝕂 ]→ µ₂)
--                        → (` x) ⋯ f ≡ Kit.`/id 𝕂 _ (f _ x))
--   defdecFun'
--     (argᵥ ⋯-var-nm)
--     ⋯-var-ty
--     [ clause [] [] body ]

-- -- ⋯-var : ∀ {{𝕂 : Kit}} {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
-- --         (` x) ⋯ f ≡ `/id _ (f _ x)
-- -- ⋯-var x f = refl

-- derive-⋯-↑ : {𝕄 : Modes} → Terms 𝕄 → Name → Name → TC ⊤
-- derive-⋯-↑ {𝕄} 𝕋 ⋯-nm ⋯-↑-nm = runFreshT do
--   let open Modes 𝕄
--   let open Terms 𝕋
--   let open Kitty.Kit 𝕋
--   let open Kitty.Experimental.KitAltSimple 𝕋
--   𝕄-nm ← quoteNameTC 𝕄
--   ⊢-nm ← quoteNameTC _⊢_
--   ⊢-def ← getDefinition ⊢-nm
--   `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
--   𝕋-nm ← term→name =<< quoteTC' 𝕋

--   _⋯_ ← unquoteTC' {A = ∀ ⦃ 𝕂 : Kitty.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M} (def ⋯-nm [])
--   let _⋯*_ =
--         (∀ {𝕂s : List Kit} {µ₁ µ₂ M} →
--           µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M)
--         by
--         (λ t fs → fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs)

--   let todo = def (quote TODO) []
--   let body = todo
--   ⋯-↑-ty ← quoteTC' (
--       ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂ M} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
--       → (∀ m (x : µ₁ ∋ m) → ((` x) ⋯* f) ≡ ((` x) ⋯* g))
--       → (t : µ₁ ⊢ M) → t ⋯* f ≡ t ⋯* g
--     )
--   defdecFun'
--     (argᵥ ⋯-↑-nm)
--     ⋯-↑-ty
--     [ clause [] [] body ]

-- derive-KitTraversalAlt : {𝕄 : Modes} → Terms 𝕄 → Name → Name → Name → Name → TC ⊤
-- derive-KitTraversalAlt {𝕄} 𝕋 ⋯-nm ⋯-var-nm ⋯-↑-nm kit-traversal-nm = runFreshT do
--   𝕋-nm ← term→name =<< quoteTC' 𝕋
--   let body =
--         con (quote Kitty.Experimental.KitAltSimple.mkKitTraversalAlt)
--           [ argᵥ (def ⋯-nm [])
--           ; argᵥ (def ⋯-var-nm [])
--           ; argᵥ (def ⋯-↑-nm [])
--           ]
--   defdecFun'
--     (argᵥ kit-traversal-nm)
--     (def (quote Kitty.Experimental.KitAltSimple.KitTraversalAlt) [ argᵥ (def 𝕋-nm []) ])
--     [ clause [] [] body ]

-- derive-traversal : (𝕄 : Modes) → (_⊢_ : Scoped 𝕄) → Name  → TC ⊤
-- derive-traversal 𝕄 _⊢_ traversal-nm = do
--   terms-nm ← freshName "terms"
--   derive-Terms 𝕄 _⊢_ terms-nm
--   terms ← unquoteTC {A = Terms 𝕄} (def terms-nm [])

--   ⋯-nm ← freshName "⋯"
--   derive-⋯ terms ⋯-nm

--   ⋯-var-nm ← freshName "⋯-var"
--   derive-⋯-var terms ⋯-nm ⋯-var-nm

--   ⋯-↑-nm ← freshName "⋯-↑"
--   derive-⋯-↑ terms ⋯-nm ⋯-↑-nm

--   derive-KitTraversalAlt terms ⋯-nm ⋯-var-nm ⋯-↑-nm traversal-nm

module Example where
  open Kitty.Prelude

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  infix  30 `_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `_    : ∀ {µ m}  →  µ ∋ m  →  µ ⊢ m→M m
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  module Custom where
    terms : Terms 𝕄
    terms = record { _⊢_ = _⊢_ ; `_ = `_ }

    open import Kitty.Experimental.KitAltSimple terms
    open Kitty.Kit terms
    open Kit ⦃ ... ⦄

    _⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    (` x)     ⋯ f = `/id _ (f _ x)
    (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
    (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
    (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

    ⋯-var : ∀ {{𝕂 : Kit}} {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id _ (f _ x)
    ⋯-var x f = refl

    _⋯*_ : ∀ {𝕂s : List Kit} {µ₁ µ₂ M} →
          µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
    t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

    ⋯-↑-λ : ∀ {𝕂s : List Kit} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t : (µ₁ ▷▷ µ₁' ▷ 𝕖) ⊢ 𝕖)
            → ((λx t) ⋯* (f ↑** µ₁')) ≡ λx (t ⋯* (f ↑** (µ₁' ▷▷ _)))
    ⋯-↑-λ []       t = refl
    ⋯-↑-λ {𝕂 ∷ 𝕂s} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-λ fs t) refl

    ⋯-↑-· : ∀ {𝕂s : List Kit} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t₁ t₂ : (µ₁ ▷▷ µ₁') ⊢ 𝕖)
            → ((t₁ · t₂) ⋯* (f ↑** µ₁')) ≡ ((t₁ ⋯* (f ↑** (µ₁' ▷▷ _))) · (t₂ ⋯* (f ↑** (µ₁' ▷▷ _))))
    ⋯-↑-· {.[]}     []       t₁ t₂ = refl
    ⋯-↑-· {𝕂 ∷ 𝕂s} (f ∷ fs) t₁ t₂ = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-· fs t₁ t₂) refl

    ⋯-↑-foo' : ∀ {𝕂s : List Kit} {µ₁ µ₂ µ₁' µ} (f : µ₁ –[ 𝕂s ]→* µ₂)
              → (t : (µ₁ ▷▷ µ₁' ▷▷ µ) ⊢ 𝕖)
              → (foo {µ' = µ} t) ⋯* (f ↑** µ₁')
              ≡ foo {µ' = µ} (t ⋯* ((f ↑** µ₁') ↑** µ))
    ⋯-↑-foo' {.[]}     []       t = refl
    ⋯-↑-foo' {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-foo' fs t) refl

    -- TODO: does it still work if we pull out the µ₁'?
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂ µ₁' M} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → (∀ {µ₁'} m (x : (µ₁ ▷▷ µ₁') ∋ m) → ((` x) ⋯* (f ↑** µ₁')) ≡ ((` x) ⋯* (g ↑** µ₁')))
          → (t : (µ₁ ▷▷ µ₁') ⊢ M) → t ⋯* (f ↑** µ₁') ≡ t ⋯* (g ↑** µ₁')
    ⋯-↑ f g f≈g (` x)     = f≈g _ x
    ⋯-↑ f g f≈g (λx t)    = trans (⋯-↑-λ f t) (
                            trans (cong λx_ (⋯-↑ f g f≈g t)) (
                            sym (⋯-↑-λ g t)))
    ⋯-↑ f g f≈g (t₁ · t₂) = trans (⋯-↑-· f t₁ t₂) (
                            trans (cong₂ _·_ (⋯-↑ f g f≈g t₁) (⋯-↑ f g f≈g t₂)) (
                            sym (⋯-↑-· g t₁ t₂)))
    ⋯-↑ {µ₁ = µ₁} {µ₂ = µ₂} {µ₁' = µ₁'} f g f≈g (foo {µ' = µ} t)
                          = trans (⋯-↑-foo' f t) (
                            trans (cong foo (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (helper _⋯*_ f g f≈g) t)) (
                            sym (⋯-↑-foo' g t)))

  -- module Derived where
  --   -- unquoteDecl terms = derive-Terms 𝕄 _⊢_ terms
  --   -- unquoteDecl _⋯_ = derive-⋯ terms _⋯_

  --   unquoteDecl traversal = derive-traversal 𝕄 _⊢_ traversal
  --   open import Kitty.Experimental.KitAltSimple

  --   open Kitty.Experimental.KitAltSimple.Derive _ traversal

  --   `id : [] ⊢ 𝕖
  --   `id = λx ` here refl

  --   `f : [ 𝕖 ] ⊢ 𝕖
  --   `f = λx (` here refl) · (` there (here refl))

  --   `f' : [] ⊢ 𝕖
  --   `f' = `f ⋯ ⦅ `id ⦆ₛ

  --   test-`f' : `f' ≡ λx (` here refl) · (λx ` here refl)
  --   test-`f' = refl



