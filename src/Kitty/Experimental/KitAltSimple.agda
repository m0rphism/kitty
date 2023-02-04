open import Kitty.Modes

-- Version of KitAlt with a simpler KitTraversal.⋯-↑ field.

module Kitty.Experimental.KitAltSimple {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Kitty.Prelude
open import Level using (_⊔_)

open import Kitty.Experimental.Star

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Alternative KitTraversal ----------------------------------------------------

open import Kitty.Kit 𝕋
open import Kitty.Homotopy

open Kit {{...}}

_–[_]→*_ : List VarMode → (_ : List Kit) → List VarMode → Set _
µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

_↑**_ : {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
[] ↑** µ' = []
(_∷_ {b = 𝕂} f fs) ↑** µ' = (Kit._↑*_ 𝕂 f µ') ∷ (fs ↑** µ')

instance
  kit-[] : List Kit
  kit-[] = []

  kit-∷ : {{𝕂 : Kit}} → {{𝕂s : List Kit}} → List Kit
  kit-∷ {{𝕂}} {{𝕂s}} = 𝕂 ∷ 𝕂s

record KitTraversalAlt : Set₁ where
  constructor mkKitTraversalAlt
  infixl  5  _⋯_  _⋯*_

  field
    _⋯_   : ∀ {{𝕂 : Kit}} →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

  _⋯*_ : ∀ {𝕂s : List Kit} →
          µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

  field
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id _ (f _ x)
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
          (∀ m (x : µ₁ ∋ m) → ` x ⋯* f ≡ ` x ⋯* g) →
          (t : µ₁ ⊢ M) → t ⋯* f ≡ t ⋯* g

-- Deriving KitTraversal, KitAssoc, and KitAssocLemmas -------------------------

module Derive (KT : KitTraversalAlt) where
  open KitTraversalAlt KT public

  private
    kit-traversal : KitTraversal
    kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

  open KitTraversal kit-traversal hiding (_⋯_; ⋯-var; kitᵣ; kitₛ) public

  ~-cong-⋯ :
    ∀ {{𝕂 : Kit}} {f g : µ₁ –[ 𝕂 ]→ µ₂}  (v : µ₁ ⊢ M)
    → f ~ g
    → v ⋯ f ≡ v ⋯ g
  ~-cong-⋯ {f = f} {g} v f~g =
    ⋯-↑ (f ∷ [])
        (g ∷ [])
        (λ m x →
          begin
            (` x) ⋯ f
          ≡⟨ ⋯-var x f ⟩
            `/id _ (f _ x)
          ≡⟨ cong (`/id _) (f~g _ x) ⟩
            `/id _ (g _ x)
          ≡⟨ sym (⋯-var x g) ⟩
            (` x) ⋯ g
          ∎)
        v

  private
    kit-homotopy : KitHomotopy kit-traversal
    kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

  open import Kitty.Compose 𝕋 kit-traversal kit-homotopy

  open ComposeKit {{...}} public

  private
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
    ⋯-assoc {{𝕂₁}} {{𝕂₂}} {{𝕂}} v f g =
      v ⋯ f ⋯ g                            ≡⟨ refl ⟩
      v ⋯* (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
        ≡⟨ ⋯-↑ (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
              ((g ∘ₖ f) ∷[ 𝕂 ] [])
              (λ m₁ x →
                ` x ⋯ f ⋯ g               ≡⟨ cong (_⋯ g) (⋯-var x f) ⟩
                (`/id _ (f _ x)) ⋯ g      ≡⟨ tm-⋯-∘ f g x ⟩
                `/id _ ((g ∘ₖ f) _ x)     ≡⟨ cong (λ h → `/id _ h) (sym (dist-↑*-∘ [] g f _ x)) ⟩
                `/id _ ((g ∘ₖ f) _ x)     ≡⟨ sym (⋯-var x (g ∘ₖ f)) ⟩
                ` x ⋯ (g ∘ₖ f)            ∎)
              v
        ⟩
      v ⋯* (_∷_ {b = 𝕂} (g ∘ₖ f) [])       ≡⟨ refl ⟩
      v ⋯ (g ∘ₖ f)       ∎

    kit-assoc : KitAssoc
    kit-assoc = record { ⋯-assoc = ⋯-assoc }

  open KitAssoc kit-assoc public hiding (kitᵣᵣ; kitᵣₛ; kitₛᵣ; kitₛₛ; wk-kitᵣ; wk-kitₛ)

  private
    ⋯-id' : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
    ⋯-id' {{𝕂}} {µ} {M} v =
      ⋯-↑ (idₖ ∷[ 𝕂 ] [])
          []
          (λ m x →
            ` x ⋯ idₖ {{𝕂}}           ≡⟨ ⋯-var x idₖ ⟩
            `/id _ ((idₖ {{𝕂}}) _ x)  ≡⟨ cong (λ h → `/id _ h) (id↑*~id [] _ _ x) ⟩
            `/id _ (idₖ {{𝕂}} _ x)    ≡⟨⟩
            `/id _ (id/` _ x)         ≡⟨ id/`/id x ⟩
            ` x                       ∎)
          v

    kitassoc-lemmas : KitAssocLemmas
    kitassoc-lemmas = record { ⋯-id = ⋯-id' }

  open KitAssocLemmas kitassoc-lemmas public

  instance
    kitᵣ  = KitTraversal.kitᵣ kit-traversal
    kitₛ  = KitTraversal.kitₛ kit-traversal
    kitᵣᵣ = KitAssoc.kitᵣᵣ kit-assoc
    kitₛᵣ = KitAssoc.kitₛᵣ kit-assoc
    kitᵣₛ = KitAssoc.kitᵣₛ kit-assoc
    kitₛₛ = KitAssoc.kitₛₛ kit-assoc
    wk-kitᵣ = KitAssoc.wk-kitᵣ kit-assoc
    wk-kitₛ = KitAssoc.wk-kitₛ kit-assoc

  open Kit {{...}} public
  open import Kitty.Kit 𝕋 public


