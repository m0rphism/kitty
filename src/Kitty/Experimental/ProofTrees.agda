module Kitty.Experimental.ProofTrees where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Syntax-▷ where
  infixr 5 _▷_
  _▷_ :
    ∀ {z} (Z : Set z)
    → Z
    → Z
  Z ▷ fz = fz

  infixr 5 _▷₀_
  _▷₀_ :
    ∀ {z} (Z : Set z)
    → Z
    → Z
  Z ▷₀ fz = fz

  infixr 5 _▷₁_–_
  _▷₁_–_ :
    ∀ {a} {A : Set a}
      {z} (Z : Set z)
    → (A → Z)
    → (A → Z)
  Z ▷₁ fz – a = fz a

  infixr 5 _▷₂_–_–_
  _▷₂_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {z} (Z : Set z)
    → (A → B → Z)
    → (A → B → Z)
  Z ▷₂ fz – a – b = fz a b

  infixr 5 _▷₃_–_–_–_
  _▷₃_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {z} (Z : Set z)
    → (A → B → C → Z)
    → (A → B → C → Z)
  Z ▷₃ fz – a – b – c = fz a b c

  infixr 5 _▷₄_–_–_–_–_
  _▷₄_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {z} (Z : Set z)
    → (A → B → C → D → Z)
    → (A → B → C → D → Z)
  Z ▷₄ fz – a – b – c – d = fz a b c d

  infixr 5 _▷₅_–_–_–_–_–_
  _▷₅_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {e} {E : Set e}
      {z} (Z : Set z)
    → (A → B → C → D → E → Z)
    → (A → B → C → D → E → Z)
  Z ▷₅ fz – a – b – c – d – e = fz a b c d e

  infixr 5 _▷₆_–_–_–_–_–_–_
  _▷₆_–_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {e} {E : Set e}
      {f} {F : Set f}
      {z} (Z : Set z)
    → (A → B → C → D → E → F → Z)
    → (A → B → C → D → E → F → Z)
  Z ▷₆ fz – a – b – c – d – e – f = fz a b c d e f

  infixr 5 _▷₇_–_–_–_–_–_–_–_
  _▷₇_–_–_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {e} {E : Set e}
      {f} {F : Set f}
      {g} {G : Set g}
      {z} (Z : Set z)
    → (A → B → C → D → E → F → G → Z)
    → (A → B → C → D → E → F → G → Z)
  Z ▷₇ fz – a – b – c – d – e – f – g = fz a b c d e f g

  infixr 5 _▷₈_–_–_–_–_–_–_–_–_
  _▷₈_–_–_–_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {e} {E : Set e}
      {f} {F : Set f}
      {g} {G : Set g}
      {h} {H : Set h}
      {z} (Z : Set z)
    → (A → B → C → D → E → F → G → H → Z)
    → (A → B → C → D → E → F → G → H → Z)
  Z ▷₈ fz – a – b – c – d – e – f – g – h = fz a b c d e f g h

  infixr 5 _▷₉_–_–_–_–_–_–_–_–_–_
  _▷₉_–_–_–_–_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : Set b}
      {c} {C : Set c}
      {d} {D : Set d}
      {e} {E : Set e}
      {f} {F : Set f}
      {g} {G : Set g}
      {h} {H : Set h}
      {i} {I : Set i}
      {z} (Z : Set z)
    → (A → B → C → D → E → F → G → H → I → Z)
    → (A → B → C → D → E → F → G → H → I → Z)
  Z ▷₉ fz – a – b – c – d – e – f – g – h – i = fz a b c d e f g h i

-- Not really necessary: if we already now the indices, we don't have
-- to explicitly supply them.
module Syntax-▷-dep where
  infixr 5 _▷_
  _▷_ :
    ∀ {z} (Z : Set z)
    → Z
    → Z
  Z ▷ f = f

  infixr 5 _▷₀_
  _▷₀_ :
    ∀ {z} (Z : Set z)
    → Z
    → Z
  Z ▷₀ f = f

  infixr 5 _▷₁_–_
  _▷₁_–_ :
    ∀ {a} {A : Set a}
      {z} {Z : (a : A) → Set z}
      (Z' : Set z)
    → ((a : A) → Z a)
    → ((a : A) → {{_ : Z' ≡ Z a}} → Z a)
  Z ▷₁ f – a = f a

  infixr 5 _▷₂_–_–_
  _▷₂_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : (a : A) → Set b}
      {z} {Z : (a : A) → (b : B a) → Set z}
      (Z' : Set z)
    → ((a : A) → (b : B a) → Z a b)
    → ((a : A) → (b : B a) → {{_ : Z' ≡ Z a b}} → Z')
  _▷₂_–_–_ Z f a b {{refl}} = f a b

  infixr 5 _▷₃_–_–_–_
  _▷₃_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : (a : A) → Set b}
      {c} {C : (a : A) → (b : B a) → Set c}
      {z} {Z : (a : A) → (b : B a) → (c : C a b) → Set z}
      (Z' : Set z)
    → ((a : A) → (b : B a) → (c : C a b) → Z a b c)
    → ((a : A) → (b : B a) → (c : C a b) → {{_ : Z' ≡ Z a b c}} → Z')
  _▷₃_–_–_–_ Z f a b c {{refl}} = f a b c

  infixr 5 _▷₄_–_–_–_–_
  _▷₄_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : (a : A) → Set b}
      {c} {C : (a : A) → (b : B a) → Set c}
      {d} {D : (a : A) → (b : B a) → (c : C a b) → Set d}
      {z} {Z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → Set z}
      (Z' : Set z)
    → ((a : A) → (b : B a) → (c : C a b) → (d : D a b c) → Z a b c d)
    → ((a : A) → (b : B a) → (c : C a b) → (d : D a b c) → {{_ : Z' ≡ Z a b c d}} → Z')
  _▷₄_–_–_–_–_ Z f a b c d {{refl}} = f a b c d

  infixr 5 _▷₅_–_–_–_–_–_
  _▷₅_–_–_–_–_–_ :
    ∀ {a} {A : Set a}
      {b} {B : (a : A) → Set b}
      {c} {C : (a : A) → (b : B a) → Set c}
      {d} {D : (a : A) → (b : B a) → (c : C a b) → Set d}
      {e} {E : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → Set e}
      {z} {Z : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → Set z}
      (Z' : Set z)
    → ((a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → Z a b c d e)
    → ((a : A) → (b : B a) → (c : C a b) → (d : D a b c) → (e : E a b c d) → {{_ : Z' ≡ Z a b c d e}} → Z')
  _▷₅_–_–_–_–_–_ Z f a b c d e {{refl}} = f a b c d e

module Syntax-by where
  open Syntax-▷ public renaming
    ( _▷₀_     to _by_
    ; _▷₁_–_   to _by₁_–_
    ; _▷₂_–_–_ to _by₂_–_–_)

module Syntax-│ where
  open Syntax-▷ public renaming
    ( _▷₀_     to _│_
    ; _▷₁_–_   to _│₁_–_
    ; _▷₂_–_–_ to _│₂_–_–_)

module Syntax-⊹ where
  open Syntax-▷ public renaming
    ( _▷₀_     to _⊹_
    ; _▷₁_–_   to _⊹₁_–_
    ; _▷₂_–_–_ to _⊹₂_–_–_)

module Syntax-⓪ where
  open Syntax-▷ public renaming
    ( _▷₀_     to _⓪_
    ; _▷₁_–_   to _①_–_
    ; _▷₂_–_–_ to _②_–_–_)

open import Data.Nat

module Test-▷ where
  open Syntax-▷

  data _⊢_ : ℕ → ℕ → Set where
    foo : ∀ x → x ⊢ 0

  test'' : 3 ⊢ 0
  test'' =
    (3 ⊢ 0) ▷₀ foo _
    
  test =
    ℕ ▷₂ _+_
    – ℕ ▷₂ _+_
      – ℕ ▷ 1
      – ℕ ▷ 2
    – ℕ ▷₂ _+_
      – ℕ ▷ 3
      – ℕ ▷ 4

  test' =
    ℕ             ▷₂ _+_
    – ℕ             ▷₂ _+_
      – ℕ             ▷ 1
      – ℕ             ▷ 2
    – ℕ             ▷₂ _+_
      – ℕ             ▷ 3
      – ℕ             ▷ 4

module Test-▷-dep where
  open Syntax-▷-dep

  data _⊢_ : ℕ → ℕ → Set where
    foo : ∀ x → x ⊢ 0

  test''' : 3 ⊢ 0
  test''' =
    (3 ⊢ 0) ▷₁ foo
      – 3

  test'' : {{_ : 3 ⊢ 0 ≡ 2 ⊢ 0}} → 2 ⊢ 0
  test'' =
    (3 ⊢ 0) ▷₁ foo
      – 2
    
  test =
    ℕ ▷₂ _+_
    – ℕ ▷₂ _+_
      – ℕ ▷ 1
      – ℕ ▷ 2
    – ℕ ▷₂ _+_
      – ℕ ▷ 3
      – ℕ ▷ 4

-- module Test-by where
--   open Syntax-by

--   test =
--     ℕ             by₂ _+_
--     – ℕ             by₂ _+_
--       – ℕ             by 1
--       – ℕ             by 2
--     – ℕ             by₂ _+_
--       – ℕ             by 3
--       – ℕ             by 4

-- module Test-⊹ where
--   open Syntax-⊹

--   test =
--     ℕ             ⊹₂ _+_
--     – ℕ             ⊹₂ _+_
--       – ℕ             ⊹ 1
--       – ℕ             ⊹ 2
--     – ℕ             ⊹₂ _+_
--       – ℕ             ⊹ 3
--       – ℕ             ⊹ 4

-- module Test-│ where
--   open Syntax-│

--   test =
--     ℕ             │₂ _+_
--     – ℕ             │₂ _+_
--       – ℕ             │ 1
--       – ℕ             │ 2
--     – ℕ             │₂ _+_
--       – ℕ             │ 3
--       – ℕ             │ 4

--   test' =
--     ℕ             │₂ _+_
--     – ℕ           │₂ _+_
--       – ℕ         │  1
--       – ℕ         │  2
--     – ℕ           │₂ _+_
--       – ℕ         │  3
--       – ℕ         │  4

-- module Test-box where
--   open Syntax-▷ using () renaming (_▷₀_     to _├_;
--                                    _▷₂_–_–_ to _├─┐₂_–_–_)
--   open Syntax-▷ using () renaming (_▷₀_     to _└_;
--                                    _▷₂_–_–_ to _└─┐₂_–_–_)

--   test =
--     ℕ             └─┐₂ _+_
--     – ℕ             ├─┐₂ _+_
--       – ℕ             ├ 1
--       – ℕ             └ 2
--     – ℕ             └─┐₂ _+_
--       – ℕ             ├ 3
--       – ℕ             └ 4

-- module Test-⓪ where
--   open Syntax-⓪

--   test =
--     ℕ             ② _+_
--     – ℕ             ② _+_
--       – ℕ             ⓪ 1
--       – ℕ             ⓪ 2
--     – ℕ             ② _+_
--       – ℕ             ⓪ 3
--       – ℕ             ⓪ 4
