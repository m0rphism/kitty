module ReflectionLib.Named.ToStandard where

import Level as Level

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product using (_×_; _,_)
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String

open import Level using (Level)
open import Function using (_$_)

open import ReflectionLib.Classes.ToStandard
open import ReflectionLib.Categorical
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.VeryPretty

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ
    F : Functor' ℓ 

-- Clause Generation -----------------------------------------------------------

-- Debuijn Vars are only used for local variables -> no context for clauses
--   (not true for pattern lambdas)
-- We can duplicate the AST with local names instead of indices and transform.

open ToDebruijn {{...}} renaming (to-debruijn to ⟪_∥_⟫'; to-debruijn-trace to ⟪_∥_⟫)

to-debruijn : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}}
                {{_ : ToDebruijn A B}} {{_ : Pretty A}} → A → F B
to-debruijn a with ⟪ [] ∥ a ⟫
... | ok a = return a 
... | err ss = liftTC $ failStr (String.concat ss)


get-index' : String → List String → SResult ℕ
get-index' x [] = err $ _∷ [] $ "ERROR: to-debruin reached undefined variable '" ++ x ++ "'.\n"
get-index' x (y ∷ ys) with x String.≟ y
get-index' x (y ∷ ys) | yes _ = return zero
get-index' x (y ∷ ys) | no  _ = do i ← get-index' x ys; return (suc i)

env-to-str : List String → String
env-to-str env = "[" ++ f env ++ "]" where
  f : List String → String
  f []        = ""
  f (x ∷ [])  = x
  f (x ∷ env) = x ++ ", " ++ f env

get-index : String → List String → SResult ℕ
get-index x env with get-index' x env
... | ok x = ok x
... | err msgs = err $ _∷ msgs $ "With environment: " ++ env-to-str env ++ "\n"

mutual

  trans-tel : List String → Telescope' → SResult (List String × Telescope)
  trans-tel γ [] = return $ γ , []
  trans-tel γ ((x , t) ∷ tel) = do
    t' ← ⟪ γ ∥ t ⟫
    (γ' , tel') ← trans-tel (x ∷ γ) tel
    return (γ' , (x , t') ∷ tel')

  instance

    DB-Term : ToDebruijn Term' Term
    DB-Term .⟪_∥_⟫' γ (var x args)      = var <$> get-index x γ <*> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (con c args)      = con c <$> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (def f args)      = def f <$> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (lam v t)         = lam v <$> ⟪ γ ∥ t ⟫'
    DB-Term .⟪_∥_⟫' γ (pat-lam cs args) = pat-lam <$> ⟪ γ ∥ cs ⟫ <*> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (pi a b)          = pi <$> ⟪ γ ∥ a ⟫ <*> ⟪ γ ∥ b ⟫'
    DB-Term .⟪_∥_⟫' γ (agda-sort s)     = agda-sort <$> ⟪ γ ∥ s ⟫
    DB-Term .⟪_∥_⟫' γ (lit l)           = pure $ lit l
    DB-Term .⟪_∥_⟫' γ (meta x t)        = meta x <$> ⟪ γ ∥ t ⟫
    DB-Term .⟪_∥_⟫' γ unknown           = pure unknown

    DB-Abs : {{_ : ToDebruijn A B}} {{_ : Pretty A}} → ToDebruijn (Abs A) (Abs B)
    DB-Abs .⟪_∥_⟫' γ (abs x a) = abs x <$> ⟪ x ∷ γ ∥ a ⟫

    DB-Pattern : ToDebruijn Pattern' Pattern
    DB-Pattern .⟪_∥_⟫' γ (con c ps) = con c <$> ⟪ γ ∥ ps ⟫
    DB-Pattern .⟪_∥_⟫' γ (dot t)    = dot <$> ⟪ γ ∥ t ⟫
    DB-Pattern .⟪_∥_⟫' γ (var x)    = var <$> get-index x γ
    DB-Pattern .⟪_∥_⟫' γ (lit l)    = pure $ lit l
    DB-Pattern .⟪_∥_⟫' γ (proj f)   = pure $ proj f
    DB-Pattern .⟪_∥_⟫' γ (absurd x) = absurd <$> get-index x γ

    DB-Clause : ToDebruijn Clause' Clause
    DB-Clause .⟪_∥_⟫' γ (clause tel ps t) = do
      (γ' , tel') ← trans-tel γ tel
      clause tel' <$> ⟪ γ' ∥ ps ⟫ <*> ⟪ γ' ∥ t ⟫
    DB-Clause .⟪_∥_⟫' γ (absurd-clause tel ps) = do
      (γ' , tel') ← trans-tel γ tel
      absurd-clause tel' <$> ⟪ γ' ∥ ps ⟫

    DB-Sort : ToDebruijn Sort' Sort
    DB-Sort .⟪_∥_⟫' γ (set t)     = set <$> ⟪ γ ∥ t ⟫
    DB-Sort .⟪_∥_⟫' γ (lit n)     = pure $ lit n
    DB-Sort .⟪_∥_⟫' γ (prop t)    = prop <$> ⟪ γ ∥ t ⟫
    DB-Sort .⟪_∥_⟫' γ (propLit n) = pure $ propLit n
    DB-Sort .⟪_∥_⟫' γ (inf n)     = pure $ inf n
    DB-Sort .⟪_∥_⟫' γ unknown     = pure $ unknown

    DB-Arg : {{_ : ToDebruijn A B}} {{_ : Pretty A}} → ToDebruijn (Arg A) (Arg B)
    DB-Arg .⟪_∥_⟫' γ (arg i x) = arg i <$> ⟪ γ ∥ x ⟫'

    {-# TERMINATING #-}
    DB-List : {{_ : ToDebruijn A B}} {{_ : Pretty A}} → ToDebruijn (List A) (List B)
    DB-List .⟪_∥_⟫' γ []       = pure []
    DB-List .⟪_∥_⟫' γ (x ∷ xs) = _∷_ <$> ⟪ γ ∥ x ⟫ <*> ⟪ γ ∥ xs ⟫'

-- module Test₁ where

--   test : Clause'
--   test = clause
--     ( ("A" , argₕ (agda-sort (lit 0)))
--     ∷ ("B" , argₕ (agda-sort (lit 0)))
--     ∷ ("f" , argᵥ (pi (argᵥ (var "A" [])) (abs "a" (var "B" []))))
--     ∷ ("a" , argᵥ (var "A" []))
--     ∷ ("b" , argᵥ (var "B" []))
--     ∷ [])
--     ( argₕ (var "A")
--     ∷ argₕ (var "B") 
--     ∷ argᵥ (var "f") 
--     ∷ argᵥ (var "a") 
--     ∷ argᵥ (var "b") 
--     ∷ [])
--     ( var "f" (argᵥ (var "a" []) ∷ []) ) 

--   test' : Clause
--   test' = to-debruijn test

--   derive-test : Name → SResult ⊤
--   derive-test f-id = do
--     declareDef (argᵥ f-id) (quoteTerm ({A B : Set} (f : A → B) (a : A) (b : B) → B))
--     defineFun f-id (test' ∷ [])

--   unquoteDecl test'' = derive-test test''

--   -- xxxx = {!test''!}

-- Clause Generation with inlined Telescope ------------------------------------

mutual
  pattern''→' : ArgInfo → Telescope' → Pattern'' → Telescope' × Pattern'
  pattern''→' i tel (con c ps) = let (tel , ps) = patterns''→' tel ps in tel , con c ps
  pattern''→' i tel (dot t) = tel , dot t
  pattern''→' i tel (var x t) = (x , arg i t) ∷ tel , var x 
  pattern''→' i tel (lit l) = tel , lit l
  pattern''→' i tel (proj f) = tel , proj f
  pattern''→' i tel (absurd x t) = (x , arg i t) ∷ tel , absurd x

  patterns''→' : Telescope' → List (Arg Pattern'') → Telescope' × List (Arg Pattern')
  patterns''→' tel [] = tel , []
  patterns''→' tel (arg i p ∷ ps) =
    let (tel , p) = pattern''→' i tel p in
    let (tel , ps) = patterns''→' tel ps in
    tel , (arg i p ∷ ps)

clause''→' : Clause'' → Clause'
clause''→' (clause ps'' t') =
  let (tel' , ps') = patterns''→' [] (List.reverse ps'') in
  clause tel' (List.reverse ps') t'
clause''→' (absurd-clause ps'') =
  let (tel' , ps') = patterns''→' [] (List.reverse ps'') in
  absurd-clause tel' (List.reverse ps')

instance
  DB-Clause'' : ToDebruijn Clause'' Clause
  DB-Clause'' .⟪_∥_⟫' γ c'' = ⟪ γ ∥ clause''→' c'' ⟫'

module Test₂ where

  -- testx : Clause''
  -- testx = clause
  --   ( argₕ (var "A" (agda-sort (lit 0)))
  --   ∷ argₕ (var "B" (agda-sort (lit 0))) 
  --   ∷ argᵥ (var "f" (pi (argᵥ (var "A" [])) (abs "a" (var "B" [])))) 
  --   ∷ argᵥ (var "a" (var "A" [])) 
  --   ∷ argᵥ (var "b" (var "B" [])) 
  --   ∷ [])
  --   ( var "f" (argᵥ (var "a" []) ∷ []) ) 

  -- testx' : Clause
  -- testx' = to-debruijn testx

  -- derive-testx : Name → SResult ⊤
  -- derive-testx f-id = do
  --   declareDef (argᵥ f-id) (quoteTerm ({A B : Set} (f : A → B) (a : A) (b : B) → B))
  --   defineFun f-id (testx' ∷ [])

  -- unquoteDecl testx'' = derive-testx testx''

  -- -- xxxx = {!testx''!}
