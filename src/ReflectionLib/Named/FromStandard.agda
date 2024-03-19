module ReflectionLib.Named.FromStandard where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product hiding (_<*>_)
open import Data.List as List hiding (_++_)
open import Data.Char as Char
open import Data.String as String
open import Data.Nat.Show renaming (show to ℕ→String)

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ)
open import Function using (_$_)

open import ReflectionLib.Named.Syntax
open import ReflectionLib.Named.VeryPretty
open import ReflectionLib.Standard.VeryPretty
open import ReflectionLib.Classes.Pretty
open import ReflectionLib.Standard.Syntax
open import ReflectionLib.Categorical

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  F : Functor' ℓ

ToM : Set ℓ → Set ℓ
ToM = FreshT {0ℓ} (λ A → Result A (List String))

with-trace : {{_ : Pretty A}} → A → ToM B → ToM B
with-trace a mb = stateT λ s → mapErr
  (λ ss → _∷ ss $ "In context: " ++ pp strip-mod a ++ "\n")
  (runStateT mb s)

record ToNamed (Src : Set) (Tgt : Set) : Set₁ where
  field
    to-named : List String → Src → ToM Tgt

  to-named-trace : {{_ : Pretty Src}} → List String → Src → ToM Tgt
  to-named-trace env src = with-trace src (to-named env src)

open ToNamed {{...}} renaming (to-named to ⟪_∥_⟫'; to-named-trace to ⟪_∥_⟫)

-- to-named : {{_ : ToNamed A B}} {{_ : Pretty A}} → A → FreshT {0ℓ} TC B
-- to-named a = stateT λ s → case-Result (runStateT ⟪ [] ∥ a ⟫ s)
--   (λ { (b , s) → pure (b , s) })
--   (λ e         → failStr (String.concat e))

to-named : ∀ {{_ : Monad ℓ F}} {{_ : MonadTC ℓ F}} {{_ : MonadFresh ℓ F}}
             {{_ : ToNamed A B}} {{_ : Pretty A}} → A → F B
to-named a = do
  s ← get
  case-Result (runStateT ⟪ [] ∥ a ⟫ s)
    (λ { (b , s) → do put s; pure b })
    (λ e         → liftTC (failStr (String.concat e)))

get-name : List String → ℕ → ToM String
get-name [] n = lift $ err $ _∷ [] $ "Found unbound DeBruijn Variable '" ++ ℕ→String n ++ "'.\n"
get-name (x ∷ xs) zero    = pure x
get-name (x ∷ xs) (suc n) = get-name xs n

mutual
  trans-tel : List String → Telescope → ToM (List String × Telescope')
  trans-tel γ [] = pure $ γ , []
  trans-tel γ ((x , t) ∷ tel) = do
    x' ← fresh-id x
    t' ← ⟪ γ ∥ t ⟫
    γ' , tel' ← trans-tel (x' ∷ γ) tel
    pure $ γ' , (x' , t') ∷ tel'

  instance

    DB-Term : ToNamed Term Term'
    DB-Term .⟪_∥_⟫' γ (var x args)      = var <$> get-name γ x <*> ⟪ γ ∥ args ⟫ 
    DB-Term .⟪_∥_⟫' γ (con c args)      = con c <$> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (def f args)      = def f <$> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (lam v t)         = lam v <$> ⟪ γ ∥ t ⟫'
    DB-Term .⟪_∥_⟫' γ (pat-lam cs args) = pat-lam <$> ⟪ γ ∥ cs ⟫ <*> ⟪ γ ∥ args ⟫
    DB-Term .⟪_∥_⟫' γ (pi a b)          = pi <$> ⟪ γ ∥ a ⟫ <*> ⟪ γ ∥ b ⟫
    DB-Term .⟪_∥_⟫' γ (agda-sort s)     = agda-sort <$> ⟪ γ ∥ s ⟫
    DB-Term .⟪_∥_⟫' γ (lit l)           = pure $ lit l
    DB-Term .⟪_∥_⟫' γ (meta x t)        = meta x <$> ⟪ γ ∥ t ⟫
    DB-Term .⟪_∥_⟫' γ unknown           = pure unknown

    DB-Abs : {{_ : ToNamed A B}} {{_ : Pretty A}} → ToNamed (Abs A) (Abs B)
    DB-Abs .⟪_∥_⟫' γ (abs x a) = do
      x' ← fresh-id x
      abs x' <$> ⟪ x' ∷ γ ∥ a ⟫'

    DB-Pattern : ToNamed Pattern Pattern'
    DB-Pattern .⟪_∥_⟫' γ (con c ps) = con c <$> ⟪ γ ∥ ps ⟫
    DB-Pattern .⟪_∥_⟫' γ (dot t)    = dot <$> ⟪ γ ∥ t ⟫
    DB-Pattern .⟪_∥_⟫' γ (var x)    = var <$> get-name γ x
    DB-Pattern .⟪_∥_⟫' γ (lit l)    = pure $ lit l
    DB-Pattern .⟪_∥_⟫' γ (proj f)   = pure $ proj f
    DB-Pattern .⟪_∥_⟫' γ (absurd x) = absurd <$> get-name γ x

    DB-Clause : ToNamed Clause Clause'
    DB-Clause .⟪_∥_⟫' γ (clause tel ps t) = do
      (γ' , tel') ← trans-tel γ tel
      clause tel' <$> ⟪ γ' ∥ ps ⟫ <*> ⟪ γ' ∥ t ⟫
    DB-Clause .⟪_∥_⟫' γ (absurd-clause tel ps) = do
      (γ' , tel') ← trans-tel γ tel
      absurd-clause tel' <$> ⟪ γ' ∥ ps ⟫

    DB-Sort : ToNamed Sort Sort'
    DB-Sort .⟪_∥_⟫' γ (set t)     = set <$> ⟪ γ ∥ t ⟫
    DB-Sort .⟪_∥_⟫' γ (lit n)     = pure $ lit n
    DB-Sort .⟪_∥_⟫' γ (prop t)    = prop <$> ⟪ γ ∥ t ⟫
    DB-Sort .⟪_∥_⟫' γ (propLit n) = pure $ propLit n
    DB-Sort .⟪_∥_⟫' γ (inf n)     = pure $ inf n
    DB-Sort .⟪_∥_⟫' γ unknown     = pure $ unknown

    DB-Arg : {{_ : ToNamed A B}} {{_ : Pretty A}} → ToNamed (Arg A) (Arg B)
    DB-Arg .⟪_∥_⟫' γ (arg i x) = arg i <$> ⟪ γ ∥ x ⟫'

    {-# TERMINATING #-}
    DB-List : {{_ : ToNamed A B}} {{_ : Pretty A}} → ToNamed (List A) (List B)
    DB-List .⟪_∥_⟫' γ []       = pure []
    DB-List .⟪_∥_⟫' γ (x ∷ xs) = _∷_ <$> ⟪ γ ∥ x ⟫ <*> ⟪ γ ∥ xs ⟫'
