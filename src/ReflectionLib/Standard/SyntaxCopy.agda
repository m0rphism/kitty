module ReflectionLib.Standard.SyntaxCopy where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Word
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Sigma
open import Agda.Primitive

-- Fixity

data Associativity : Set where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : Set where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : Set where
  fixity : Associativity → Precedence → Fixity

-- Names

postulate Name               : Set
postulate primQNameEquality  : Name → Name → Bool
postulate primQNameLess      : Name → Name → Bool
postulate primShowQName      : Name → String
postulate primQNameFixity    : Name → Fixity
postulate primQNameToWord64s : Name → Σ Word64 (λ _ → Word64)

-- Metavariables

postulate Meta             : Set
postulate primMetaEquality : Meta → Meta → Bool
postulate primMetaLess     : Meta → Meta → Bool
postulate primShowMeta     : Meta → String
postulate primMetaToNat    : Meta → Nat

-- Arguments --

-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : Set where
  visible hidden instance′ : Visibility

-- Arguments can be relevant or irrelevant.
data Relevance : Set where
  relevant irrelevant : Relevance

-- Arguments also have a quantity.
data Quantity : Set where
  quantity-0 quantity-ω : Quantity

-- Relevance and quantity are combined into a modality.
data Modality : Set where
  modality : (r : Relevance) (q : Quantity) → Modality

data ArgInfo : Set where
  arg-info : (v : Visibility) (m : Modality) → ArgInfo

data Arg {a} (A : Set a) : Set a where
  arg : (i : ArgInfo) (x : A) → Arg A

-- Name abstraction --

data Abs {a} (A : Set a) : Set a where
  abs : (s : String) (x : A) → Abs A

-- Literals --

data Literal : Set where
  nat    : (n : Nat)    → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

-- Terms and patterns --

mutual
  Type = Term

  data Term : Set where
    var       : (x : Nat) (args : List (Arg Term)) → Term
    con       : (c : Name) (args : List (Arg Term)) → Term
    def       : (f : Name) (args : List (Arg Term)) → Term
    lam       : (v : Visibility) (t : Abs Term) → Term
    pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
    pi        : (a : Arg Type) (b : Abs Type) → Term
    agda-sort : (s : Sort) → Term
    lit       : (l : Literal) → Term
    meta      : (x : Meta) → List (Arg Term) → Term                -- A hole `?`
    unknown   : Term                                               -- `_` expression

  data Sort : Set where
    set     : (t : Term) → Sort
    lit     : (n : Nat) → Sort
    prop    : (t : Term) → Sort
    propLit : (n : Nat) → Sort
    inf     : (n : Nat) → Sort
    unknown : Sort

  data Pattern : Set where
    con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
    dot    : (t : Term)    → Pattern
    var    : (x : Nat)     → Pattern  -- `x` is a Debruijn index into the clause's telescope.
    lit    : (l : Literal) → Pattern
    proj   : (f : Name)    → Pattern
    absurd : (x : Nat)     → Pattern  -- absurd patterns counts as variables

  -- A clause has a telescope which is used to typecheck both the patterns and the body.
  -- The pattern variables refer to the telescope with DeBruijn indices.
  -- The clause telescope is a reversed type context: In `x ∷ y ∷ z`
  -- `z` is the most recently bound variable, i.e. we refer to
  -- `x` with index `2` and to `z` with index `0`.
  data Clause : Set where
    clause        : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) (t : Term) → Clause
    absurd-clause : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) → Clause

-- Definitions --

data Definition : Set where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

-- Errors --

data ErrorPart : Set where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  nameErr : Name → ErrorPart

-- TC monad --

postulate
  TC               : ∀ {a} → Set a → Set a
  returnTC         : ∀ {a} {A : Set a} → A → TC A
  bindTC           : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC ⊤
  typeError        : ∀ {a} {A : Set a} → List ErrorPart → TC A
  inferType        : Term → TC Type
  checkType        : Term → Type → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : Set a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : Set a} → A → TC Term
  unquoteTC        : ∀ {a} {A : Set a} → Term → TC A
  quoteωTC         : ∀ {A : Setω} → A → TC Term
  getContext       : TC (List (Arg Type))
  extendContext    : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
  inContext        : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → Type → TC ⊤
  declarePostulate : Arg Name → Type → TC ⊤
  defineFun        : Name → List Clause → TC ⊤
  getType          : Name → TC Type
  getDefinition    : Name → TC Definition
  blockOnMeta      : ∀ {a} {A : Set a} → Meta → TC A
  commitTC         : TC ⊤
  isMacro          : Name → TC Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A

  -- Makes the following primitives to reconstruct hidden arguments
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : Set a} → TC A → TC A

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → Nat → List ErrorPart → TC ⊤

  -- Only allow reduction of specific definitions while executing the TC computation
  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A

  -- Don't allow reduction of specific definitions while executing the TC computation
  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : Set a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : Set a} → TC (Σ A λ _ → Bool) → TC A
