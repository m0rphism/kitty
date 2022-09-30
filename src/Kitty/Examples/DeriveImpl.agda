module Kitty.Examples.DeriveImpl where

  -- unquoteDecl desc    = deriveDesc   (quote 𝕄) (quote _⊢_) desc
  -- unquoteDecl to      = deriveTo     (quote 𝕄) (quote _⊢_) (quote desc) to
  -- unquoteDecl from    = deriveFrom   (quote 𝕄) (quote _⊢_) (quote desc) from
  -- unquoteDecl from∘to = deriveFromTo (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) from∘to
  -- unquoteDecl to∘from = deriveToFrom (quote 𝕄) (quote _⊢_) (quote desc) (quote to) (quote from) to∘from

  -- open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)
  -- open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
  -- open import Data.Fin     using (Fin; zero; suc)
  -- open import Kitty.Derive.Common
  -- open import Function using (_$_)

  -- to∘from' : ∀ {µ M} → (x : Tm 𝕄 desc µ M) → to (from x) ≡ x 
  -- to∘from' (`var x) = {!!}
  -- to∘from' (`con (zero , µ' , p , e , e' , refl)) =
  --   cong `con $
  --   cong-Σ refl $
  --   cong-Σ refl $
  --   cong-Σ refl $
  --   cong-× (to∘from' e) $
  --   cong-× (to∘from' e') $
  --   refl
