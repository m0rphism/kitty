module ReflectionLib.Named.Match where

open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Standard.DecEq
open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.Rewrite
open import ReflectionLib.Classes.DecEq public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List using (List; _∷_ ; []; concat)
open import Data.List.Relation.Unary.All using (All; _∷_ ; [])
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Function using (_$_; case_of_; id)

-- * Holes can appear multiple times → check if all occurences are equal if used on match side
-- * Support for quoting and unquoting with special postulate for holes
-- * Holes can have additional guards for matching
-- * `+` and `*` repetitions to match on arbitrary repetitions of patterns

HoleCtx : ∀ {ℓ} → (HoleType → Set ℓ) → Set ℓ
HoleCtx I = List (Σ HoleType I)

private variable
  m n n₁ n₂ n₃   : ℕ
  ℓ ℓ' ℓ₁ ℓ₂     : Level
  A B C          : Set ℓ
  I              : A → Set ℓ
  µ µ₁ µ₂ µ₃     : HoleCtx I
  µs µs₁ µs₂ µs₃ : List (HoleCtx I)

data TermPat (I : HoleType → Set ℓ) : HoleCtx I → Set ℓ where
  ⟪⟫        : (a : I `Term) → TermPat I ((`Term , a) ∷ [])
  ⟪_⟫       : (a : I `Term) → TermPat I µ → TermPat I ((`Term , a) ∷ µ)
  var       : String → All (λ µ → Arg (TermPat I µ)) µs → TermPat I (concat µs)
  con       : Name → All (λ µ → Arg (TermPat I µ)) µs → TermPat I (concat µs)
  def       : Name → All (λ µ → Arg (TermPat I µ)) µs → TermPat I (concat µs)
  lam       : Visibility → Abs (TermPat I µ) → TermPat I µ
  pat-lam   : List Clause' → All (λ µ → Arg (TermPat I µ)) µs → TermPat I  (concat µs)
  pi        : Arg Type' → Abs Type' → TermPat I µ
  agda-sort : Sort' → TermPat I µ
  lit       : Literal → TermPat I µ
  meta      : Meta → All (λ µ → Arg (TermPat I µ)) µs → TermPat I (concat µs)
  unknown   : TermPat I µ

record Pat {ℓ} (P : ℕ → Set ℓ) : Set (lsuc ℓ) where
  field
    Target : Set ℓ

match : {!TermPat ts → Term → Maybe (t ∈ ts → Target t)!}
match = {!!}

match/replace : {!(TermPat ts → TermPat ts) → Term → Maybe Term!}
match/replace = {!!}
