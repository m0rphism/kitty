module ReflectionLib.Classes.Pretty where

import Level as Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String

open import Reflection hiding (name; Type)
open import Agda.Builtin.Reflection
open import Level using (Level)
open import Function using (_$_)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

record PrettyOpts : Set where
  field
    stripModules : Bool

instance
  pretty-opts-def : PrettyOpts
  pretty-opts-def = record
    { stripModules = true
    }

strip-mod : PrettyOpts
strip-mod = record { stripModules = true }

keep-mod : PrettyOpts
keep-mod = record { stripModules = false }

open PrettyOpts

record Pretty (A : Set ℓ) : Set ℓ where
  field
    pp : PrettyOpts → A → String

open Pretty {{...}} public

toDec : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → Decidable {ℓ} {A} (λ a → p a ≡ true)
toDec p x with p x
toDec p x | false = no λ ()
toDec p x | true = yes refl

over-list : (List Char → List Char) → String → String
over-list f s = String.fromList (f (String.toList s))

over-rev : (List A → List A) → List A → List A
over-rev f s = List.reverse (f (List.reverse s))

-- module-name : String → String
-- module-name = over-list $ takeWhile $ toDec $ λ c → not (c Char.== '.')

strip-modules : String → String
strip-modules = over-list $ over-rev $ takeWhile $ toDec $ λ c → not (c Char.== '.')

ppListV : {{_ : Pretty A}} → PrettyOpts → List A → String
ppListV o [] = ""
ppListV o (x ∷ xs) = "- " ++ pp o x ++ "\n\n" ++ ppListV o xs

printStr : String → TC ⊤
printStr s = debugPrint "reflection-debug" 2 (strErr s ∷ [])

printAST : {{Opts : PrettyOpts}} {{_ : Pretty A}} → A → TC ⊤
printAST {{opts}} ast = printStr (pp opts ast)

printTerm : Term → TC ⊤
printTerm t = debugPrint "reflection-debug" 2 (termErr t ∷ [])

printASTs : {{Opts : PrettyOpts}} {{_ : Pretty A}} → List A → TC ⊤
printASTs {{opts}} asts = printStr (ppListV opts asts)

failStr : ∀ {ℓ} {A : Set ℓ} → String → TC A
failStr s = typeError (strErr s ∷ [])
