module KitTheory.Generics-Example where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import KitTheory.Modes
open import KitTheory.Prelude

data Mode : Set where
  𝕖 : Mode

𝕄 : Modes
𝕄 = record { VarMode = Mode ; TermMode = Mode ; m→M = λ m → m }
open Modes 𝕄

open import KitTheory.Generics 𝕄

data STLCCon : Set where
  con-λ con-· : STLCCon

STLC : Desc
STLC = `σ STLCCon λ where
  con-λ → `X (𝕖 ∷ []) 𝕖 (`■ 𝕖)
  con-· → `X [] 𝕖 (`X [] 𝕖 (`■ 𝕖))

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
  x y z                     : µ ∋ 𝕖
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Tm STLC µ 𝕖


open import KitTheory.Kit (𝕋 STLC)
open import KitTheory.Compose (𝕋 STLC) (KT STLC)

open KitTraversal (KT STLC)
open KitAssoc (KA STLC)

open Kit {{...}}
open ComposeKit {{...}}

instance
  𝕂ᵣ = kitᵣ
  𝕂ₛ = kitₛ
  𝕂ᵣᵣ = kitᵣᵣ
  𝕂ᵣₛ = kitᵣₛ
  𝕂ₛᵣ = kitₛᵣ
  𝕂ₛₛ = kitₛₛ

module With-Patterns where
  open Terms (𝕋 STLC) using (_⊢_)

  pattern `λ_ e     = `con ⟨ con-λ , ⟨ e , refl ⟩ ⟩
  pattern _·_ e₁ e₂ = `con ⟨ con-· , ⟨ e₁ , ⟨ e₂ , refl ⟩ ⟩ ⟩
  pattern `_ x      = `var x

  id : Tm STLC [] 𝕖
  id = `λ ` here refl

  id·id : Tm STLC [] 𝕖
  id·id = (`λ ` here refl) · (`λ ` here refl)

  foo : ∀ {µ} → µ ⊢ 𝕖 → µ ⊢ 𝕖
  foo (` x)     = {!!}
  foo (`λ e)    = {!!}
  foo (e₁ · e₂) = {!!}

module With-Iso where
  open Agda.Primitive using (Level; _⊔_; lsuc)
  record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      to      : A → B
      from    : B → A
      from∘to : ∀ a → from (to a) ≡ a
      to∘from : ∀ b → to (from b) ≡ b

  data _⊢_ : List VarMode → TermMode → Set where
    `_    : µ ∋ 𝕖  →  µ ⊢ 𝕖
    λx_   : (µ , 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖

  to : (µ ⊢ M) → Tm STLC µ M
  to (` x)     = `var x
  to (λx e)    = `con ⟨ con-λ , ⟨ to e , refl ⟩ ⟩
  to (e₁ · e₂) = `con ⟨ con-· , ⟨ to e₁ , ⟨ to e₂ , refl ⟩ ⟩ ⟩

  from : Tm STLC µ M → (µ ⊢ M)
  from {M = 𝕖} (`var x)                          = ` x
  from (`con ⟨ con-λ , ⟨ e , refl ⟩ ⟩)           = λx (from e)
  from (`con ⟨ con-· , ⟨ e₁ , ⟨ e₂ , refl ⟩ ⟩ ⟩) = from e₁ · from e₂

  from∘to : (a : µ ⊢ M) → from (to a) ≡ a
  from∘to (` x) = refl
  from∘to (λx e) rewrite from∘to e = refl
  from∘to (e₁ · e₂) rewrite from∘to e₁ | from∘to e₂ = refl

  to∘from : (b : Tm STLC µ M) → to (from b) ≡ b
  to∘from {M = 𝕖} (`var x) = refl
  to∘from (`con ⟨ con-λ , ⟨ e , refl ⟩ ⟩) rewrite to∘from e = refl
  to∘from (`con ⟨ con-· , ⟨ e₁ , ⟨ e₂ , refl ⟩ ⟩ ⟩) rewrite to∘from e₁ | to∘from e₂ = refl

  iso : ∀ {µ M} → (µ ⊢ M) ≃ Tm STLC µ M
  iso = record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }



-- -- Types and Contexts ----------------------------------------------------------

-- open import KitTheory.Types 𝕋

-- -- Each variable mode corresponds to a term mode that represents its type.
-- kit-type : KitType
-- kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕥 } }

-- open KitType kit-type public

-- open import KitTheory.OPE 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type public

-- variable
--   Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
--   T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M


