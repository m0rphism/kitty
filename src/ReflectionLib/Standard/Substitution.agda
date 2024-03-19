module ReflectionLib.Standard.Substitution where

import Level as Level

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit using (⊤; tt)
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String using (String)

open import Reflection hiding (name; Type; returnTC)
open import Agda.Builtin.Reflection
open import Level using (Level)
open import Function using (_$_)

open import ReflectionLib.Standard.Syntax

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

-- Weakening -------------------------------------------------------------------

record Weaken (A : Set) : Set₁ where
  field
    wk-from : ℕ → A → A

open Weaken {{...}} public

wk : {{_ : Weaken A}} → A → A
wk = wk-from 0

wk*-from : {{_ : Weaken A}} → ℕ → ℕ → A → A
wk*-from 0 m a = a
wk*-from (suc n) m a = wk-from m (wk*-from n m a)

wk* : {{_ : Weaken A}} → ℕ → A → A
wk* n a = wk*-from n 0 a

mutual
  wkTel-from : ℕ → Telescope → Telescope
  wkTel-from n []              = []
  wkTel-from n ((x , t) ∷ tel) = (x , wk-from n t) ∷ wkTel-from (suc n) tel

  instance

    wkDef : Weaken Definition
    wkDef = record { wk-from = wk-from' } where
      wk-from' : ℕ → Definition → Definition
      wk-from' n (function cs)       = function (wk-from n cs)
      wk-from' n (data-type pars cs) = data-type pars cs
      wk-from' n (record-type c fs)  = record-type c fs
      wk-from' n (data-cons d)       = data-cons d
      wk-from' n axiom               = axiom
      wk-from' n prim-fun            = prim-fun

    wkList : {{_ : Weaken A}} → Weaken (List A)
    wkList = record { wk-from = wk-from' } where
      wk-from' : {{_ : Weaken A}} → ℕ → List A → List A
      wk-from' n xs = map (wk-from n) xs

    wkArg : {{_ : Weaken A}} → Weaken (Arg A)
    wkArg = record { wk-from = wk-from' } where
      wk-from' : {{_ : Weaken A}} → ℕ → Arg A → Arg A
      wk-from' n (arg i a) = arg i (wk-from n a)

    wkAbs : {{_ : Weaken A}} → Weaken (Abs A)
    wkAbs = record { wk-from = wk-from' } where
      wk-from' : {{_ : Weaken A}} → ℕ → Abs A → Abs A
      wk-from' n (abs x a) = abs x (wk-from (suc n) a)

    wkSort : Weaken Sort
    wkSort = record { wk-from = wk-from' } where
      wk-from' : ℕ → Sort → Sort
      wk-from' n (set t)     = set (wk-from n t)
      wk-from' n (lit m)     = lit m
      wk-from' n (prop t)    = prop (wk-from n t)
      wk-from' n (propLit m) = propLit m
      wk-from' n (inf m)     = inf m
      wk-from' n unknown     = unknown

    wkPattern : Weaken Pattern
    wkPattern = record { wk-from = wk-from' } where
      wk-from' : ℕ → Pattern → Pattern
      wk-from' n (con c ps) = con c (wk-from n ps)
      wk-from' n (dot t)    = dot (wk-from n t)
      wk-from' n (var x)    = var x
      wk-from' n (lit l)    = lit l
      wk-from' n (proj f)   = proj f
      wk-from' n (absurd x) = absurd x

    wkClause : Weaken Clause
    wkClause = record { wk-from = wk-from' } where
      wk-from' : ℕ → Clause → Clause
      wk-from' n (clause tel ps t)      =
        clause (wkTel-from n tel) (wk-from n ps) (wk-from (length tel + n) t)
      wk-from' n (absurd-clause tel ps) =
        absurd-clause (wkTel-from n tel) (wk-from n ps)

    {-# TERMINATING #-}
    wkTerm : Weaken Term
    wkTerm = record { wk-from = wk-from' } where
      wk-from' : ℕ → Term → Term
      wk-from' n (var x args)      with x Nat.<? n
      ...                             | yes _ = var x       (wk-from n args)
      ...                             | no _  = var (suc x) (wk-from n args)
      wk-from' n (con c args)      = con c (wk-from n args)
      wk-from' n (def f args)      = def f (wk-from n args)
      wk-from' n (lam v t)         = lam v (wk-from n t)
      wk-from' n (pat-lam cs args) = pat-lam (wk-from n cs) (wk-from n args)
      wk-from' n (pi a b)          = pi (wk-from n a) (wk-from n b)
      wk-from' n (agda-sort s)     = agda-sort (wk-from n s)
      wk-from' n (lit l)           = lit l
      wk-from' n (meta a b)        = meta a b
      wk-from' n unknown           = unknown

-- Substitution ----------------------------------------------------------------

record Substitution (A : Set) : Set₁ where
  field
    _[_↦_] : A → ℕ → Term → A

open Substitution {{...}} public

_[_↦_↑_] : {{_ : Substitution A}} → A → ℕ → Term → ℕ → A
a [ x ↦ t ↑ n ] = a [ (n + x) ↦ (wk* n t) ]

mutual
  subTel : Telescope → ℕ → Term → Telescope
  subTel []              x t' = []
  subTel ((y , t) ∷ tel) x t' = (y , t [ x ↦ t' ]) ∷ subTel tel (suc x) (wk t')

  instance

    subDef : Substitution Definition
    subDef = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Definition → ℕ → Term → Definition
      function cs       [ x ↦ t' ]' = function (cs [ x ↦ t' ])
      data-type pars cs [ x ↦ t' ]' = data-type pars cs
      record-type c fs  [ x ↦ t' ]' = record-type c fs
      data-cons d       [ x ↦ t' ]' = data-cons d
      axiom             [ x ↦ t' ]' = axiom
      prim-fun          [ x ↦ t' ]' = prim-fun

    subList : {{_ : Substitution A}} → Substitution (List A)
    subList = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → List A → ℕ → Term → List A
      as [ x ↦ t' ]' = map _[ x ↦ t' ] as

    subArg : {{_ : Substitution A}} → Substitution (Arg A)
    subArg = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → Arg A → ℕ → Term → Arg A
      (arg i a) [ x ↦ t' ]' = arg i (a [ x ↦ t' ])

    subAbs : {{_ : Substitution A}} → Substitution (Abs A)
    subAbs = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → Abs A → ℕ → Term → Abs A
      (abs y a) [ x ↦ t' ]' = abs y (a [ x ↦ t' ↑ 1 ])

    {-# TERMINATING #-}
    subSort : Substitution Sort
    subSort = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Sort → ℕ → Term → Sort
      set t     [ x ↦ t' ]' = set (t [ x ↦ t' ])
      lit n     [ x ↦ t' ]' = lit n
      prop t    [ x ↦ t' ]' = prop (t [ x ↦ t' ])
      propLit n [ x ↦ t' ]' = propLit n
      inf n     [ x ↦ t' ]' = inf n
      unknown   [ x ↦ t' ]' = unknown

    subPattern : Substitution Pattern
    subPattern = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Pattern → ℕ → Term → Pattern
      con c ps [ x ↦ t' ]' = con c (ps [ x ↦ t' ])
      dot t    [ x ↦ t' ]' = dot (t [ x ↦ t' ])
      var y    [ x ↦ t' ]' = var y
      lit l    [ x ↦ t' ]' = lit l
      proj f   [ x ↦ t' ]' = proj f
      absurd y [ x ↦ t' ]' = absurd y

    subClause : Substitution Clause
    subClause = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Clause → ℕ → Term → Clause
      clause tel ps t      [ x ↦ t' ]' =
        clause (subTel tel x t') (ps [ x ↦ t' ↑ length tel ]) (t [ x ↦ t' ↑ length tel ])
      absurd-clause tel ps [ x ↦ t' ]' =
        absurd-clause (subTel tel x t') (ps [ x ↦ t' ↑ length tel ])

    -- FIXME: when replacing a var, the var-arguments need to be reapplied.
    subTerm : Substitution Term
    subTerm = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Term → ℕ → Term → Term
      var y args      [ x ↦ t' ]' with x Nat.≟ y | x Nat.<? y
      ...                            | yes x≡y | _       = t'
      ...                            | no _    | yes x<y = var y (args [ x ↦ t' ])
      ...                            | no _    | no  x>y = var (y ∸ 1) (args [ x ↦ t' ])
      con c args      [ x ↦ t' ]' = con c (args [ x ↦ t' ])
      def f args      [ x ↦ t' ]' = def f (args [ x ↦ t' ])
      lam v t         [ x ↦ t' ]' = lam v (t [ x ↦ t' ])
      pat-lam cs args [ x ↦ t' ]' = pat-lam (cs [ x ↦ t' ]) (args [ x ↦ t' ])
      pi a b          [ x ↦ t' ]' = pi (a [ x ↦ t' ]) (b [ x ↦ t' ])
      agda-sort s     [ x ↦ t' ]' = agda-sort (s [ x ↦ t' ])
      lit l           [ x ↦ t' ]' = lit l
      meta a b        [ x ↦ t' ]' = meta a b
      unknown         [ x ↦ t' ]' = unknown

-- How Pattern Variables are Represented ---------------------------------------

private
  _by_ : (A : Set ℓ) → A → A
  A by a = a

  -- Term showing the DeBruijn-Indices used in `var` pattern: they
  -- refer to the clause's telescope.
  test : Term
  test = quoteTerm ((ℕ → ℕ → ℕ → ℕ) by λ a → ((ℕ → ℕ → ℕ → ℕ) by (λ { x y z → x })) a)

  test' : Term
  test' = 
    def (quote _by_)
      ( argₕ (def (quote Level.zero) [])
      ∷ argᵥ ℕ→ℕ→ℕ→ℕ
      ∷ argᵥ (lam visible (abs "a"
        (def (quote _by_)
          ( argₕ (def (quote Level.zero) [])
          ∷ argᵥ ℕ→ℕ→ℕ→ℕ
          ∷ argᵥ (pat-lam
            ( clause
              ( ("x" , argᵥ (def (quote ℕ) []))
              ∷ ("y" , argᵥ (def (quote ℕ) []))
              ∷ ("z" , argᵥ (def (quote ℕ) []))
              ∷ [])
              ( argᵥ (var 2)
              ∷ argᵥ (var 1)
              ∷ argᵥ (var 0)
              ∷ [])
              (var 2 [])
            ∷ [])
            [])
          ∷ argᵥ (var 0 [])
          ∷ []))))
      ∷ [])
    where 
      ℕ→ℕ→ℕ→ℕ : Term
      ℕ→ℕ→ℕ→ℕ = quoteTerm (ℕ → ℕ → ℕ → ℕ) 

  test-eq : test ≡ test'
  test-eq = refl
