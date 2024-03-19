module ReflectionLib.Named.Substitution where

import Level as Level

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit using (⊤; tt)
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List as List
open import Data.Char as Char
open import Data.String as String using (String)
open import Data.Maybe using (Maybe; nothing; just)

open import Agda.Builtin.Reflection
open import Agda.Primitive using (Level; Setω)
open import Function using (_$_)

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Named.Syntax

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ

-- Free Variables --------------------------------------------------------------

private
  remove : String → List String → List String
  remove s' [] = []
  remove s' (s ∷ ss) with s String.≟ s'
  ... | yes _ = remove s' ss
  ... | no  _ = s ∷ remove s' ss

  remove* : List String → List String → List String
  remove* []         ss = ss
  remove* (s' ∷ ss') ss = remove s' (remove* ss' ss)

  contains : String → List String → Bool
  contains s' [] = false
  contains s' (s ∷ ss) with s String.≟ s'
  ... | yes _ = true
  ... | no _  = contains s' ss

  lookup' : String → List (String × A) → Maybe A
  lookup' s [] = nothing
  lookup' s ((s' , a) ∷ xs) with s String.≟ s'
  ... | yes _ = just a
  ... | no  _ = lookup' s xs

record FreeVars (A : Set) : Set₁ where
  field
    fvs : A → List String

open FreeVars {{...}} public

mutual
  fvsTel : Telescope' → List String
  fvsTel []              = []
  fvsTel ((x , t) ∷ tel) = fvs t ++ remove x (fvsTel tel)

  instance

    fvsDef : FreeVars Definition'
    fvsDef = record { fvs = fvs' } where
      fvs' : Definition' → List String
      fvs' (function cs)       = fvs cs
      fvs' (data-type pars cs) = []
      fvs' (record-type c fs)  = []
      fvs' (data-cons d)       = []
      fvs' axiom               = []
      fvs' prim-fun            = []

    fvsList : {{_ : FreeVars A}} → FreeVars (List A)
    fvsList = record { fvs = fvs' } where
      fvs' : {{_ : FreeVars A}} → List A → List String
      fvs' xs = List.concat (List.map fvs xs)

    fvsArg : {{_ : FreeVars A}} → FreeVars (Arg A)
    fvsArg = record { fvs = fvs' } where
      fvs' : {{_ : FreeVars A}} → Arg A → List String
      fvs' (arg i a) = fvs a

    fvsAbs : {{_ : FreeVars A}} → FreeVars (Abs A)
    fvsAbs = record { fvs = fvs' } where
      fvs' : {{_ : FreeVars A}} → Abs A → List String
      fvs' (abs x a) = remove x (fvs a)

    fvsSort : FreeVars Sort'
    fvsSort = record { fvs = fvs' } where
      fvs' : Sort' → List String
      fvs' (set t)     = fvs t
      fvs' (lit m)     = []
      fvs' (prop t)    = fvs t
      fvs' (propLit m) = []
      fvs' (inf m)     = []
      fvs' unknown     = []

    fvsPattern : FreeVars Pattern'
    fvsPattern = record { fvs = fvs' } where
      fvs' : Pattern' → List String
      fvs' (con c ps) = fvs ps
      fvs' (dot t)    = fvs t
      fvs' (var x)    = x ∷ []
      fvs' (lit l)    = []
      fvs' (proj f)   = []
      fvs' (absurd x) = x ∷ []

    fvsClause : FreeVars Clause'
    fvsClause = record { fvs = fvs' } where
      fvs' : Clause' → List String
      fvs' (clause tel ps t)      =
        fvsTel tel ++ remove* (List.map proj₁ tel) (fvs t)
      fvs' (absurd-clause tel ps) =
        fvsTel tel

    {-# TERMINATING #-}
    fvsTerm : FreeVars Term'
    fvsTerm = record { fvs = fvs' } where
      fvs' : Term' → List String
      fvs' (var x args)      = x ∷ fvs args
      fvs' (con c args)      = fvs args
      fvs' (def f args)      = fvs args
      fvs' (lam v t)         = fvs t
      fvs' (pat-lam cs args) = fvs cs ++ fvs args
      fvs' (pi a b)          = fvs a ++ fvs b
      fvs' (agda-sort s)     = fvs s
      fvs' (lit l)           = []
      fvs' (meta a b)        = []
      fvs' unknown           = []

-- Substitution ----------------------------------------------------------------

-- Important: does NOT perform renaming to be capture avoiding!

record Substitution (A : Set) : Set₁ where
  field
    _[_↦_] : A → String → Term' → A

open Substitution {{...}} public

mutual
  subTel : Telescope' → String → Term' → Telescope'
  subTel []              x t' = []
  subTel ((y , t) ∷ tel) x t' = (y , t [ x ↦ t' ]) ∷ subTel tel x t'

  instance

    subDef : Substitution Definition'
    subDef = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Definition' → String → Term' → Definition'
      function cs       [ x ↦ t' ]' = function (cs [ x ↦ t' ])
      data-type pars cs [ x ↦ t' ]' = data-type pars cs
      record-type c fs  [ x ↦ t' ]' = record-type c fs
      data-cons d       [ x ↦ t' ]' = data-cons d
      axiom             [ x ↦ t' ]' = axiom
      prim-fun          [ x ↦ t' ]' = prim-fun

    subList : {{_ : Substitution A}} → Substitution (List A)
    subList = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → List A → String → Term' → List A
      as [ x ↦ t' ]' = map _[ x ↦ t' ] as

    subArg : {{_ : Substitution A}} → Substitution (Arg A)
    subArg = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → Arg A → String → Term' → Arg A
      (arg i a) [ x ↦ t' ]' = arg i (a [ x ↦ t' ])

    subAbs : {{_ : Substitution A}} → Substitution (Abs A)
    subAbs = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : {{_ : Substitution A}} → Abs A → String → Term' → Abs A
      (abs y a) [ x ↦ t' ]' = abs y (a [ x ↦ t' ])

    {-# TERMINATING #-}
    subSort : Substitution Sort'
    subSort = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Sort' → String → Term' → Sort'
      set t     [ x ↦ t' ]' = set (t [ x ↦ t' ])
      lit n     [ x ↦ t' ]' = lit n
      prop t    [ x ↦ t' ]' = prop (t [ x ↦ t' ])
      propLit n [ x ↦ t' ]' = propLit n
      inf n     [ x ↦ t' ]' = inf n
      unknown   [ x ↦ t' ]' = unknown

    subPattern : Substitution Pattern'
    subPattern = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Pattern' → String → Term' → Pattern'
      con c ps [ x ↦ t' ]' = con c (ps [ x ↦ t' ])
      dot t    [ x ↦ t' ]' = dot (t [ x ↦ t' ])
      var y    [ x ↦ t' ]' = var y
      lit l    [ x ↦ t' ]' = lit l
      proj f   [ x ↦ t' ]' = proj f
      absurd y [ x ↦ t' ]' = absurd y

    subClause : Substitution Clause'
    subClause = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Clause' → String → Term' → Clause'
      clause tel ps t      [ x ↦ t' ]' =
        clause (subTel tel x t') (ps [ x ↦ t' ]) (t [ x ↦ t' ])
      absurd-clause tel ps [ x ↦ t' ]' =
        absurd-clause (subTel tel x t') (ps [ x ↦ t' ])

    -- FIXME: when replacing a var, the var-arguments need to be reapplied.
    subTerm : Substitution Term'
    subTerm = record { _[_↦_] = _[_↦_]' } where
      _[_↦_]' : Term' → String → Term' → Term'
      var y args      [ x ↦ t' ]' with x String.≟ y 
      ...                            | yes x≡y = t'
      ...                            | no _    = var y (args [ x ↦ t' ])
      con c args      [ x ↦ t' ]' = con c (args [ x ↦ t' ])
      def f args      [ x ↦ t' ]' = def f (args [ x ↦ t' ])
      lam v t         [ x ↦ t' ]' = lam v (t [ x ↦ t' ])
      pat-lam cs args [ x ↦ t' ]' = pat-lam (cs [ x ↦ t' ]) (args [ x ↦ t' ])
      pi a b          [ x ↦ t' ]' = pi (a [ x ↦ t' ]) (b [ x ↦ t' ])
      agda-sort s     [ x ↦ t' ]' = agda-sort (s [ x ↦ t' ])
      lit l           [ x ↦ t' ]' = lit l
      meta a b        [ x ↦ t' ]' = meta a b
      unknown         [ x ↦ t' ]' = unknown

-- Renaming of Bound Variables -------------------------------------------------

open import ReflectionLib.Categorical

private variable
  F : Functor' ℓ

record RnBound (A : Set) : Setω where
  field
    rn-bound : ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}}
               → List (String × String) → (String → F String) → A → F A

open RnBound {{...}} public

-- `make-fresh-for a b` renames all free variables of `a` in `b` with
-- fresh variables.
make-fresh-for : ∀ {{_ : FreeVars A}} {{_ : RnBound B}} {F : Functor' ℓ} {{_ : Monad ℓ F}} {{_ : MonadFresh ℓ F}}
                 → A → B → F B
make-fresh-for a = rn-bound [] λ x →
  if contains x (fvs a)
    then fresh-id x
    else pure x

mutual
  rnbTel : ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Telescope' → F Telescope'
  rnbTel env f []              = pure []
  rnbTel env f ((y , t) ∷ tel) = do t' ← rn-bound env f t
                                    y' ← f y
                                    tel' ← rnbTel ((y , y') ∷ env) f tel
                                    pure $ (y' , t') ∷ tel'

  instance

    rnbDef : RnBound Definition'
    rnbDef = record { rn-bound = rn-bound' } where
      rn-bound' : ∀ {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Definition' → F Definition'
      rn-bound' env f (function cs      ) = function <$> (rn-bound env f cs)
      rn-bound' env f (data-type pars cs) = pure $ data-type pars cs
      rn-bound' env f (record-type c fs ) = pure $ record-type c fs
      rn-bound' env f (data-cons d      ) = pure $ data-cons d
      rn-bound' env f (axiom            ) = pure $ axiom
      rn-bound' env f (prim-fun         ) = pure $ prim-fun

    rnbList : {{_ : RnBound A}} → RnBound (List A)
    rnbList = record { rn-bound = rn-bound' } where
      rn-bound' : {{_ : RnBound A}} {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → List A → F (List A)
      rn-bound' env f as = mapM (rn-bound env f) as

    rnbArg : {{_ : RnBound A}} → RnBound (Arg A)
    rnbArg = record { rn-bound = rn-bound' } where
      rn-bound' : {{_ : RnBound A}} {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Arg A → F (Arg A)
      rn-bound' env f (arg i a) = arg i <$> (rn-bound env f a)

    rnbAbs : {{_ : RnBound A}} → RnBound (Abs A)
    rnbAbs = record { rn-bound = rn-bound' } where
      rn-bound' : {{_ : RnBound A}} {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Abs A → F (Abs A)
      rn-bound' env f (abs y a) = do
        y' ← f y
        abs y' <$> (rn-bound ((y , y') ∷ env) f a)

    {-# TERMINATING #-}
    rnbSort : RnBound Sort'
    rnbSort = record { rn-bound = rn-bound' } where
      rn-bound' : {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Sort' → F Sort'
      rn-bound' env f (set t    ) = set <$> (rn-bound env f t)
      rn-bound' env f (lit n    ) = pure $ lit n
      rn-bound' env f (prop t   ) = prop <$> (rn-bound env f t)
      rn-bound' env f (propLit n) = pure $ propLit n
      rn-bound' env f (inf n    ) = pure $ inf n
      rn-bound' env f (unknown  ) = pure $ unknown

    rnbPattern : RnBound Pattern'
    rnbPattern = record { rn-bound = rn-bound' } where
      rn-bound' : {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Pattern' → F Pattern'
      rn-bound' env f (con c ps) = con c <$> (rn-bound env f ps)
      rn-bound' env f (dot t   ) = dot <$> (rn-bound env f t)
      rn-bound' env f (var y)    with lookup' y env
      ...                           | just y' = pure $ var y'
      ...                           | nothing = pure $ var y
      rn-bound' env f (lit l   ) = pure $ lit l
      rn-bound' env f (proj f' ) = pure $ proj f'
      rn-bound' env f (absurd y) = pure $ absurd y

    rnbClause : RnBound Clause'
    rnbClause = record { rn-bound = rn-bound' } where
      rn-bound' : {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Clause' → F Clause'
      rn-bound' env f (clause tel ps t) = do
        tel' ← rnbTel env f tel
        let env' = env ++ List.zip (List.map proj₁ tel) (List.map proj₁ tel')
        clause tel' <$> (rn-bound env' f ps) <*> (rn-bound env' f t)
      rn-bound' env f (absurd-clause tel ps) = do
        tel' ← rnbTel env f tel
        let env' = env ++ List.zip (List.map proj₁ tel) (List.map proj₁ tel')
        absurd-clause tel' <$> (rn-bound env' f ps)

    -- FIXME: when replacing a var, the var-arguments need to be reapplied.
    rnbTerm : RnBound Term'
    rnbTerm = record { rn-bound = rn-bound' } where
      rn-bound' : {F : Functor' ℓ} {{_ : Monad ℓ F}} → List (String × String) → (String → F String) → Term' → F Term'
      rn-bound' env f (var y args) with lookup' y env
      ...                             | just y' = var y' <$> (rn-bound env f args)
      ...                             | nothing = var y <$> (rn-bound env f args)
      rn-bound' env f (con c args     ) = con c <$> (rn-bound env f args)
      rn-bound' env f (def f' args    ) = def f' <$> (rn-bound env f args)
      rn-bound' env f (lam v t        ) = lam v <$> (rn-bound env f t)
      rn-bound' env f (pat-lam cs args) = pat-lam <$> (rn-bound env f cs) <*> (rn-bound env f args)
      rn-bound' env f (pi a b         ) = pi <$> (rn-bound env f a) <*> (rn-bound env f b)
      rn-bound' env f (agda-sort s    ) = agda-sort <$> (rn-bound env f s)
      rn-bound' env f (lit l          ) = pure $ lit l
      rn-bound' env f (meta a b       ) = pure $ meta a b
      rn-bound' env f (unknown        ) = pure $ unknown
