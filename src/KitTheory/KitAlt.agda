open import KitTheory.Modes

-- Alternative to KitTraversal, KitAssoc, and KitAssocLemmas using the
-- approach from the agda-stdlib.

module KitTheory.KitAlt {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import KitTheory.Prelude
open import Level using (_⊔_)

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Star-Lists and Folds --------------------------------------------------------

data Star {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) : List B → A → A → Set (ℓ₁ ⊔ ℓ₂) where
  [] : ∀ {x} → Star R [] x x
  _∷_ : ∀ {x y z b bs} → R b x y → Star R bs y z → Star R (b ∷ bs) x z

infixr 5 _∷[_]_
pattern _∷[_]_  f b fs = _∷_ {b = b} f fs

fold-star : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b x y → T y) →
  T a → Star R bs a b → T b
fold-star f ta [] = ta
fold-star f ta (rab ∷ rbc) = fold-star f (f _ _ _ ta rab) rbc

fold-star' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
  (∀ b x y → T x → R b y x → T y) →
  T a → Star R bs b a → T b
fold-star' f ta [] = ta
fold-star' f ta (rab ∷ rbc) = f _ _ _ (fold-star' f ta rbc) rab

-- Alternative KitTraversal ----------------------------------------------------

open import KitTheory.Kit 𝕋

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
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
          (∀ µ m (x : (µ ++ µ₁) ∋ m) → ` x ⋯* (f ↑** µ) ≡ ` x ⋯* (g ↑** µ)) →
          (t : (µ ++ µ₁) ⊢ M) → t ⋯* (f ↑** µ) ≡ t ⋯* (g ↑** µ)

  ⋯→⋯*₁ :
    ∀ {𝕂s : List Kit}
      {m} (C : ∀ µ → (m ∷ µ) ⊢ M → µ ⊢ M)
      {µ₁ µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂)
      {µ} {t : (m ∷ µ ++ µ₁) ⊢ M} →
    (∀ {{𝕂}} {µ₁} {µ₂} (f : µ₁ –[ 𝕂 ]→ µ₂) t → C µ₁ t ⋯ f ≡ C µ₂ (t ⋯ f ↑ m)) →
    C (µ ++ µ₁) t ⋯* (fs ↑** µ) ≡
    C (µ ++ µ₂) (t ⋯* (fs ↑** (m ∷ µ)))
  ⋯→⋯*₁ C [] ass = refl
  ⋯→⋯*₁ {𝕂s = 𝕂 ∷ 𝕂s} {m = m} C {µ₁ = µ₁} {µ₂ = µ₂} (f ∷ fs) {µ = µ} {t = t} ass =
    let instance _ = 𝕂 in
    C (µ ++ µ₁) t ⋯* ((f ∷ fs) ↑** µ)                      ≡⟨ refl ⟩
    C (µ ++ µ₁) t ⋯* (fs ↑** µ) ⋯ (f ↑* µ)                 ≡⟨ cong (_⋯ _) (⋯→⋯*₁ C fs ass) ⟩
    C (µ ++ _ ) (t ⋯* (fs ↑** (m ∷ µ))) ⋯ (f ↑* µ)         ≡⟨ ass (f ↑* µ) _ ⟩
    C (µ ++ µ₂) (t ⋯* (fs ↑** (m ∷ µ)) ⋯ (f ↑* (m ∷ µ))) ≡⟨ refl ⟩
    C (µ ++ µ₂) (t ⋯* ((f ∷ fs) ↑** (m ∷ µ))) ∎

  -- ⋯→⋯* :
  --   ∀ {𝕂s : List Kit}
  --     µ' (C : ∀ µ → (µ' ++ µ) ⊢ M → µ ⊢ M)
  --     {µ₁ µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂)
  --     µ {t : (µ' ++ µ ++ µ₁) ⊢ M} →
  --   (∀ {{𝕂}} {µ₁} {µ₂} (f : µ₁ –[ 𝕂 ]→ µ₂) t → C µ₁ t ⋯ f ≡ C µ₂ (t ⋯ f ↑* µ')) →
  --   C (µ ++ µ₁) t ⋯* (fs ↑** µ) ≡
  --   C (µ ++ µ₂) (t ⋯* subst₂ (_–[ _ ]→*_) (++-assoc µ' µ µ₁) (++-assoc µ' µ µ₂) (fs ↑** (µ' ++ µ)))
  -- ⋯→⋯* [] C {µ₁ = µ₁} {µ₂ = .µ₁} [] µ ass = refl
  -- ⋯→⋯* {𝕂s = 𝕂 ∷ 𝕂s} [] C {µ₁ = µ₁} {µ₂ = µ₂} (f ∷ fs) µ {t = t} ass =
  --   let instance _ = 𝕂 in
  --   C (µ ++ µ₁) t ⋯* ((f ↑* µ) ∷ (fs ↑** µ))   ≡⟨ refl ⟩
  --   C (µ ++ µ₁) t ⋯* (fs ↑** µ) ⋯ (f ↑* µ)     ≡⟨ cong (_⋯ _) (⋯→⋯* [] C fs µ ass) ⟩
  --   C (µ ++ _ ) (t ⋯* (fs ↑** µ)) ⋯ (f ↑* µ)   ≡⟨ ass (f ↑* µ) _ ⟩
  --   C (µ ++ µ₂) (t ⋯* (fs ↑** µ) ⋯ (f ↑* µ))   ≡⟨ refl ⟩
  --   C (µ ++ µ₂) (t ⋯* ((f ↑* µ) ∷ (fs ↑** µ))) ∎
  -- ⋯→⋯* {𝕂s = 𝕂s} (µ' , m) C {µ₁ = µ₁} {µ₂ = µ₂} fs µ {t = t} ass =
  --   C (µ ++ µ₁) t ⋯* (fs ↑** µ) ≡⟨ {!!} ⟩
  --   C (µ ++ µ₂) (t ⋯*
  --      subst₂ (_–[ 𝕂s ]→*_)
  --      (cong (m ∷_) (++-assoc µ' µ µ₁)) (cong (m ∷_) (++-assoc µ' µ µ₂))
  --      (fs ↑** (m ∷ (µ' ++ µ))))
  --      ∎


-- Deriving KitTraversal, KitAssoc, and KitAssocLemmas -------------------------

module Derive (KT : KitTraversalAlt) where
  open KitTraversalAlt KT

  kit-traversal : KitTraversal
  kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

  open import KitTheory.Compose 𝕋 kit-traversal

  open ComposeKit {{...}}

  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc {{𝕂₁}} {{𝕂₂}} {{𝕂}} v f g =
    v ⋯ f ⋯ g                            ≡⟨ refl ⟩
    v ⋯* (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
      ≡⟨ ⋯-↑ {µ = []}
             (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
             ((g ∘ₖ f) ∷[ 𝕂 ] [])
             (λ µ m₁ x →
               ` x ⋯ f ↑* µ ⋯ g ↑* µ                 ≡⟨ cong (_⋯ (g ↑* µ)) (⋯-var x (f ↑* µ)) ⟩
               (`/id _ ((f ↑* µ) _ x)) ⋯ g ↑* µ      ≡⟨ tm-⋯-∘ (f ↑* µ) (g ↑* µ) x ⟩
               `/id _ (((g ↑* µ) ∘ₖ (f ↑* µ)) _ x)   ≡⟨ cong (λ h → `/id _ (h _ x)) (sym (dist-↑*-∘ µ g f)) ⟩
               `/id _ ((g ∘ₖ f ↑* µ) _ x)            ≡⟨ sym (⋯-var x (g ∘ₖ f ↑* µ)) ⟩
               ` x ⋯ (g ∘ₖ f) ↑* µ                   ∎)
             v
      ⟩
    v ⋯* (_∷_ {b = 𝕂} (g ∘ₖ f) [])       ≡⟨ refl ⟩
    v ⋯ (g ∘ₖ f)       ∎

  kit-assoc : KitAssoc
  kit-assoc = record { ⋯-assoc = ⋯-assoc }

  open KitAssoc kit-assoc

  ⋯-id' : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id' {{𝕂}} {µ} {M} v =
    ⋯-↑ {µ = []}
        (idₖ ∷[ 𝕂 ] [])
        []
        (λ µ m x →
          ` x ⋯ idₖ {{𝕂}} ↑* µ          ≡⟨ ⋯-var x (idₖ ↑* µ) ⟩
          `/id _ ((idₖ {{𝕂}} ↑* µ) _ x) ≡⟨ cong (λ h → `/id _ (h _ x)) (id↑*≡id µ _) ⟩
          `/id _ (idₖ {{𝕂}} _ x)        ≡⟨⟩
          `/id _ (id/` _ x)             ≡⟨ id/`/id x ⟩
          ` x                           ∎)
        v

  kitassoc-lemmas : KitAssocLemmas
  kitassoc-lemmas = record { ⋯-id = ⋯-id' }

