module Kitty.Experimental.Examples.SystemF-Kits.Definitions-KitAlt where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Kitty.Prelude using (_∋_; _▷_; _▷▷_) public
open import Kitty.Modes using (Modes; Terms)

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_ --  _↪_  _⊢_∶_  _⊢*_∶_
infixr  5  ∀α_  λx_  Λα_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `ᵅ_  `ˣ_

-- Modes -----------------------------------------------------------------------

-- Variable Modes
data Modeᵥ : Set where
  𝕖 : Modeᵥ  -- Expression-level variables
  𝕥 : Modeᵥ  -- Type-level variables

-- Term Modes
data Modeₜ : Set where
  𝕖 : Modeₜ  -- Expressions
  𝕥 : Modeₜ  -- Types
  𝕜 : Modeₜ  -- Kinds

-- Mapping variable modes to the term modes they represent.
m→M : Modeᵥ → Modeₜ
m→M 𝕖 = 𝕖
m→M 𝕥 = 𝕥

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : 𝕖 ∈ µ
  α β γ                     : 𝕥 ∈ µ
  X Y Z                     : m ∈ µ

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List Modeᵥ → Modeₜ → Set where
  `ˣ_   : µ ∋ 𝕖  →  µ ⊢ 𝕖
  `ᵅ_   : µ ∋ 𝕥  →  µ ⊢ 𝕥
  λx_   : µ ▷ 𝕖 ⊢ 𝕖  →  µ ⊢ 𝕖
  Λα_   : µ ▷ 𝕥 ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀α_   : µ ▷ 𝕥 ⊢ 𝕥  →  µ ⊢ 𝕥
  _·_   : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _∙_   : µ ⊢ 𝕖  →  µ ⊢ 𝕥  →  µ ⊢ 𝕖
  _⇒_   : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  ★     : µ ⊢ 𝕜

-- Common constructor for both expression and type variables.
`_ : µ ∋ m → µ ⊢ m→M m
`_ {m = 𝕖} = `ˣ_
`_ {m = 𝕥} = `ᵅ_

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = _⊢_ ; `_ = `_ }

variable
  e e₁ e₂ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t' t₁' t₂' : µ ⊢ 𝕥
  k k₁ k₂ k' k₁' k₂' : µ ⊢ 𝕜
  E E₁ E₂ E' E₁' E₂' : µ ⊢ M

-- Application of Renamings and Substitutions ----------------------------------

open import Kitty.Kit 𝕋
open import Kitty.Experimental.KitAlt 𝕋
open Kit {{...}} public

kit-traversal-alt : KitTraversalAlt
kit-traversal-alt = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var; ⋯-↑ = ⋯-↑ } where
  -- Traverse a term with a renaming or substitution (depending on the kit).
  _⋯_ : ∀ {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  (`ˣ x)    ⋯ f = `/id _ (f _ x)
  (`ᵅ α)    ⋯ f = `/id _ (f _ α)
  (λx t)    ⋯ f = λx (t ⋯ (f ↑ 𝕖))
  (Λα t)    ⋯ f = Λα (t ⋯ (f ↑ 𝕥))
  (∀α t)    ⋯ f = ∀α (t ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  (t₁ ∙ t₂) ⋯ f = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
  (t₁ ⇒ t₂) ⋯ f = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
  ★         ⋯ f = ★
  -- Applying a renaming or substitution to a variable does the expected thing.
  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (` x) ⋯ f ≡ `/id _ (f _ x)
  ⋯-var {m = 𝕖} _ _ = refl
  ⋯-var {m = 𝕥} _ _ = refl

  infixl  5  _⋯_  _⋯*_
  _⋯*_ : ∀ {𝕂s : List Kit} →
          µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

  ⋯→⋯*₁' :
    ∀ {𝕂s : List Kit}
      {m} (C : ∀ µ → (µ ▷ m) ⊢ M → µ ⊢ M)
      {µ₁ µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂)
      {µ} {t : (µ₁ ▷▷ µ ▷ m) ⊢ M} →
    (∀ {{𝕂}} {µ₁} {µ₂} (f : µ₁ –[ 𝕂 ]→ µ₂) t → C µ₁ t ⋯ f ≡ C µ₂ (t ⋯ f ↑ m)) →
    C (µ₁ ▷▷ µ) t ⋯* (fs ↑** µ) ≡
    C (µ₂ ▷▷ µ) (t ⋯* (fs ↑** (µ ▷ m)))
  ⋯→⋯*₁' C [] ass = refl
  ⋯→⋯*₁' {𝕂s = 𝕂 ∷ 𝕂s} {m = m} C {µ₁ = µ₁} {µ₂ = µ₂} (f ∷ fs) {µ = µ} {t = t} ass =
    let instance _ = 𝕂 in
    C (µ₁ ▷▷ µ) t ⋯* ((f ∷ fs) ↑** µ)                      ≡⟨ refl ⟩
    C (µ₁ ▷▷ µ) t ⋯* (fs ↑** µ) ⋯ (f ↑* µ)                 ≡⟨ cong (_⋯ _) (⋯→⋯*₁' C fs ass) ⟩
    C (_  ▷▷ µ) (t ⋯* (fs ↑** (µ ▷ m))) ⋯ (f ↑* µ)         ≡⟨ ass (f ↑* µ) _ ⟩
    C (µ₂ ▷▷ µ) (t ⋯* (fs ↑** (µ ▷ m)) ⋯ (f ↑* (µ ▷ m))) ≡⟨ refl ⟩
    C (µ₂ ▷▷ µ) (t ⋯* ((f ∷ fs) ↑** (µ ▷ m))) ∎

  ⋯-↑-λ' : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (λx t) ⋯* (fs ↑** µ) ≡ λx (t ⋯* (fs ↑** (µ ▷ 𝕖)))
  ⋯-↑-λ' µ [] = refl
  ⋯-↑-λ' {𝕂 ∷ 𝕂s} µ (f ∷ fs) = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-λ' µ fs) refl

  ⋯-↑-λ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (λx t) ⋯* (fs ↑** µ) ≡ λx (t ⋯* (fs ↑** (µ ▷ 𝕖)))
  ⋯-↑-λ µ fs = ⋯→⋯*₁' (λ _ → λx_) fs λ _ _ → refl

  ⋯-↑-Λ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (Λα t) ⋯* (fs ↑** µ) ≡ Λα (t ⋯* (fs ↑** (µ ▷ 𝕥)))
  ⋯-↑-Λ µ fs = ⋯→⋯*₁' (λ _ → Λα_) fs λ _ _ → refl

  ⋯-↑-∀ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (∀α t) ⋯* (fs ↑** µ) ≡ ∀α (t ⋯* (fs ↑** (µ ▷ 𝕥)))
  ⋯-↑-∀ µ fs = ⋯→⋯*₁' (λ _ → ∀α_) fs λ _ _ → refl

  ⋯-↑-★ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            ★ ⋯* (fs ↑** µ) ≡ ★
  ⋯-↑-★ µ [] = refl
  ⋯-↑-★ µ (f ∷ fs) rewrite ⋯-↑-★ µ fs = refl

  ⋯-↑-· : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t₁ t₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (t₁ · t₂) ⋯* (fs ↑** µ) ≡ (t₁ ⋯* (fs ↑** µ)) · (t₂ ⋯* (fs ↑** µ))
  ⋯-↑-· µ [] = refl
  ⋯-↑-· {𝕂 ∷ 𝕂s} µ {t₁ = t₁} {t₂ = t₂} (f ∷ fs) =
    let instance _ = 𝕂 in
    t₁ · t₂ ⋯* ((f ∷ fs) ↑** µ)                          ≡⟨⟩
    t₁ · t₂ ⋯* (fs ↑** µ) ⋯ (f ↑* µ)                     ≡⟨ cong (_⋯ (f ↑* µ)) (⋯-↑-· µ fs) ⟩
    ((t₁ ⋯* (fs ↑** µ)) · (t₂ ⋯* (fs ↑** µ))) ⋯ (f ↑* µ) ≡⟨⟩
    (t₁ ⋯* ((f ∷ fs) ↑** µ)) · (t₂ ⋯* ((f ∷ fs) ↑** µ))  ∎

  ⋯-↑-∙ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t₁ t₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (t₁ ∙ t₂) ⋯* (fs ↑** µ) ≡ (t₁ ⋯* (fs ↑** µ)) ∙ (t₂ ⋯* (fs ↑** µ))
  ⋯-↑-∙ µ [] = refl
  ⋯-↑-∙ {𝕂 ∷ 𝕂s} µ {t₁ = t₁} {t₂ = t₂} (f ∷ fs) =
    let instance _ = 𝕂 in
    t₁ ∙ t₂ ⋯* ((f ∷ fs) ↑** µ)                          ≡⟨⟩
    t₁ ∙ t₂ ⋯* (fs ↑** µ) ⋯ (f ↑* µ)                     ≡⟨ cong (_⋯ (f ↑* µ)) (⋯-↑-∙ µ fs) ⟩
    ((t₁ ⋯* (fs ↑** µ)) ∙ (t₂ ⋯* (fs ↑** µ))) ⋯ (f ↑* µ) ≡⟨⟩
    (t₁ ⋯* ((f ∷ fs) ↑** µ)) ∙ (t₂ ⋯* ((f ∷ fs) ↑** µ))  ∎

  ⋯-↑-⇒ : ∀ {𝕂s : List Kit} µ {µ₁ µ₂ t₁ t₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) →
            (t₁ ⇒ t₂) ⋯* (fs ↑** µ) ≡ (t₁ ⋯* (fs ↑** µ)) ⇒ (t₂ ⋯* (fs ↑** µ))
  ⋯-↑-⇒ µ [] = refl
  ⋯-↑-⇒ {𝕂 ∷ 𝕂s} µ {t₁ = t₁} {t₂ = t₂} (f ∷ fs) =
    let instance _ = 𝕂 in
    t₁ ⇒ t₂ ⋯* ((f ∷ fs) ↑** µ)                          ≡⟨⟩
    t₁ ⇒ t₂ ⋯* (fs ↑** µ) ⋯ (f ↑* µ)                     ≡⟨ cong (_⋯ (f ↑* µ)) (⋯-↑-⇒ µ fs) ⟩
    ((t₁ ⋯* (fs ↑** µ)) ⇒ (t₂ ⋯* (fs ↑** µ))) ⋯ (f ↑* µ) ≡⟨⟩
    (t₁ ⋯* ((f ∷ fs) ↑** µ)) ⇒ (t₂ ⋯* ((f ∷ fs) ↑** µ))  ∎

  ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
        (∀ µ m (x : (µ₁ ▷▷ µ) ∋ m) → ` x ⋯* (f ↑** µ) ≡ ` x ⋯* (g ↑** µ)) →
        (t : (µ₁ ▷▷ µ) ⊢ M) → t ⋯* (f ↑** µ) ≡ t ⋯* (g ↑** µ)
  ⋯-↑ f g ass (`ˣ x) = ass _ 𝕖 x
  ⋯-↑ f g ass (`ᵅ x) = ass _ 𝕥 x
  ⋯-↑ {µ = µ} f g ass (λx t) =
    (λx t) ⋯* (f ↑** µ)       ≡⟨ ⋯-↑-λ µ f ⟩
    λx (t ⋯* (f ↑** (µ ▷ 𝕖))) ≡⟨ cong λx_ (⋯-↑ f g ass t) ⟩
    λx (t ⋯* (g ↑** (µ ▷ 𝕖))) ≡⟨ sym (⋯-↑-λ µ g) ⟩
    (λx t) ⋯* (g ↑** µ)       ∎
  ⋯-↑ {µ = µ} f g ass (Λα t) =
    (Λα t) ⋯* (f ↑** µ)       ≡⟨ ⋯-↑-Λ µ f ⟩
    Λα (t ⋯* (f ↑** (µ ▷ 𝕥))) ≡⟨ cong Λα_ (⋯-↑ f g ass t) ⟩
    Λα (t ⋯* (g ↑** (µ ▷ 𝕥))) ≡⟨ sym (⋯-↑-Λ µ g) ⟩
    (Λα t) ⋯* (g ↑** µ)       ∎
  ⋯-↑ {µ = µ} f g ass (∀α t) =
    (∀α t) ⋯* (f ↑** µ)       ≡⟨ ⋯-↑-∀ µ f ⟩
    ∀α (t ⋯* (f ↑** (µ ▷ 𝕥))) ≡⟨ cong ∀α_ (⋯-↑ f g ass t) ⟩
    ∀α (t ⋯* (g ↑** (µ ▷ 𝕥))) ≡⟨ sym (⋯-↑-∀ µ g) ⟩
    (∀α t) ⋯* (g ↑** µ)       ∎
  ⋯-↑ {µ = µ} f g ass (t₁ · t₂) =
    t₁ · t₂ ⋯* (f ↑** µ)                  ≡⟨ ⋯-↑-· µ f ⟩
    (t₁ ⋯* (f ↑** µ)) · (t₂ ⋯* (f ↑** µ)) ≡⟨ cong₂ _·_ (⋯-↑ f g ass t₁) (⋯-↑ f g ass t₂) ⟩
    (t₁ ⋯* (g ↑** µ)) · (t₂ ⋯* (g ↑** µ)) ≡⟨ sym (⋯-↑-· µ g) ⟩
    t₁ · t₂ ⋯* (g ↑** µ)                  ∎
  ⋯-↑ {µ = µ} f g ass (t₁ ∙ t₂) =
    t₁ ∙ t₂ ⋯* (f ↑** µ)                  ≡⟨ ⋯-↑-∙ µ f ⟩
    (t₁ ⋯* (f ↑** µ)) ∙ (t₂ ⋯* (f ↑** µ)) ≡⟨ cong₂ _∙_ (⋯-↑ f g ass t₁) (⋯-↑ f g ass t₂) ⟩
    (t₁ ⋯* (g ↑** µ)) ∙ (t₂ ⋯* (g ↑** µ)) ≡⟨ sym (⋯-↑-∙ µ g) ⟩
    t₁ ∙ t₂ ⋯* (g ↑** µ)                  ∎
  ⋯-↑ {µ = µ} f g ass (t₁ ⇒ t₂) =
    t₁ ⇒ t₂ ⋯* (f ↑** µ)                  ≡⟨ ⋯-↑-⇒ µ f ⟩
    (t₁ ⋯* (f ↑** µ)) ⇒ (t₂ ⋯* (f ↑** µ)) ≡⟨ cong₂ _⇒_ (⋯-↑ f g ass t₁) (⋯-↑ f g ass t₂) ⟩
    (t₁ ⋯* (g ↑** µ)) ⇒ (t₂ ⋯* (g ↑** µ)) ≡⟨ sym (⋯-↑-⇒ µ g) ⟩
    t₁ ⇒ t₂ ⋯* (g ↑** µ)                  ∎
  ⋯-↑ {µ = µ} f g ass ★ =
    ★ ⋯* (f ↑** µ) ≡⟨ ⋯-↑-★ µ f ⟩
    ★              ≡⟨ sym (⋯-↑-★ µ g) ⟩
    ★ ⋯* (g ↑** µ) ∎

open KitTraversalAlt kit-traversal-alt public

-- instance 𝕂ᵣ = kitᵣ
-- instance 𝕂ₛ = kitₛ

-- -- Composition of Renamings and Substitutions ----------------------------------

-- open import Kitty.Compose 𝕋 kit-traversal
-- open ComposeKit {{...}} public

-- kit-assoc : KitAssoc
-- kit-assoc = record { ⋯-assoc = ⋯-assoc } where
--   ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
--               (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
--     (v ⋯ f) ⋯ g ≡ v ⋯ (g ∘ₖ f)
--   ⋯-assoc (`ˣ x) f g =
--     `/id _ (f _ x) ⋯ g    ≡⟨ tm-⋯-∘ f g x ⟩
--     `/id _ ((g ∘ₖ f) _ x) ∎
--   ⋯-assoc (`ᵅ α) f g =
--     `/id _ (f _ α) ⋯ g    ≡⟨ tm-⋯-∘ f g α ⟩
--     `/id _ ((g ∘ₖ f) _ α) ∎
--   ⋯-assoc (λx e) f g = cong λx_
--     (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
--     e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
--     e ⋯ (g ∘ₖ f) ↑ _         ∎)
--   ⋯-assoc (Λα e) f g = cong Λα_
--     (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
--     e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
--     e ⋯ (g ∘ₖ f) ↑ _         ∎)
--   ⋯-assoc (∀α e) f g = cong ∀α_
--     (e ⋯ f ↑ _ ⋯ g ↑ _       ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
--     e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
--     e ⋯ (g ∘ₖ f) ↑ _         ∎)
--   ⋯-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
--   ⋯-assoc (e₁ ∙ e₂) f g = cong₂ _∙_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
--   ⋯-assoc (e₁ ⇒ e₂) f g = cong₂ _⇒_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)
--   ⋯-assoc ★         f g = refl

-- open KitAssoc kit-assoc public

-- instance 𝕂ᵣᵣ = kitᵣᵣ
-- instance 𝕂ᵣₛ = kitᵣₛ
-- instance 𝕂ₛᵣ = kitₛᵣ
-- instance 𝕂ₛₛ = kitₛₛ

-- -- Applying the identity renaming/substitution does nothing.
-- kit-assoc-lemmas : KitAssocLemmas
-- kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
--   ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
--   ⋯-id               (`ˣ x)                             = id/`/id x
--   ⋯-id               (`ᵅ α)                             = id/`/id α
--   ⋯-id {µ = µ} {{𝕂}} (λx t)    rewrite id↑≡id {{𝕂}} 𝕖 µ = cong λx_ (⋯-id t)
--   ⋯-id {µ = µ} {{𝕂}} (Λα t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong Λα_ (⋯-id t)
--   ⋯-id {µ = µ} {{𝕂}} (∀α t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong ∀α_ (⋯-id t)
--   ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
--   ⋯-id               (t₁ ∙ t₂)                          = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
--   ⋯-id               (t₁ ⇒ t₂)                          = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
--   ⋯-id               ★                                  = refl

-- open KitAssocLemmas kit-assoc-lemmas public

-- -- Types and Contexts ----------------------------------------------------------

-- open import Kitty.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- -- Each variable mode corresponds to a term mode that represents its type.
-- kit-type : KitType
-- kit-type = record { ↑ₜ = λ { 𝕖 → 𝕥 ; 𝕥 → 𝕜 ; 𝕜 → 𝕜 } }

-- open KitType kit-type public

-- variable
--   Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
--   T T₁ T₂ T' T₁' T₂' : µ ∶⊢ M

-- -- Type System -----------------------------------------------------------------

-- data _⊢_∶_ : Ctx µ → µ ⊢ M → µ ∶⊢ M → Set where
--   τ-` : ∀ {Γ : Ctx µ} {t : µ ∶⊢ 𝕖} {x : 𝕖 ∈ µ} →
--     wk-telescope Γ x ≡ t →
--     Γ ⊢ ` x ∶ t
--   τ-λ : ∀ {Γ : Ctx µ} →
--     Γ ,, t₁ ⊢ e ∶ wk _ t₂ →
--     Γ ⊢ λx e ∶ t₁ ⇒ t₂
--   τ-Λ :
--     Γ ,, ★ ⊢ e ∶ t₂ →
--     Γ ⊢ Λα e ∶ ∀α t₂
--   τ-· :
--     Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
--     Γ ⊢ e₂ ∶ t₁ →
--     Γ ⊢ e₁ · e₂ ∶ t₂
--   τ-∙ : ∀ {Γ : Ctx µ} →
--     Γ ⊢ e ∶ ∀α t₂ →
--     Γ ⊢ e ∙ t ∶ t₂ ⋯ ⦅ t ⦆
--   τ-𝕥 :
--     Γ ⊢ t ∶ ★
--   τ-𝕜 :
--     Γ ⊢ ★ ∶ ★

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ = ∀ {m₁} → (x : µ₁ ∋ m₁) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)

-- -- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : µ ⊢ 𝕖 → Set where
--     `x  : Neutral (` x)
--     _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
--     _∙t : Neutral e → Neutral (e ∙ t)

--   data Value : µ ⊢ 𝕖 → Set where
--     λx_     : Value e → Value (λx e)
--     Λα_     : Value e → Value (Λα e)
--     neutral : Neutral e → Value e

-- data _↪_ : µ ⊢ 𝕖 → µ ⊢ 𝕖 → Set where
--   β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
--     (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
--   β-Λ : ∀ {t : µ ⊢ 𝕥} →
--     (Λα e) ∙ t ↪ e ⋯ ⦅ t ⦆
--   ξ-λ :
--     e ↪ e' →
--     λx e ↪ λx e'
--   ξ-Λ :
--     e ↪ e' →
--     Λα e ↪ Λα e'
--   ξ-·₁ :
--     e₁ ↪ e₁' →
--     e₁ · e₂ ↪ e₁' · e₂
--   ξ-·₂ :
--     e₂ ↪ e₂' →
--     e₁ · e₂ ↪ e₁ · e₂'
--   ξ-∙ :
--     e ↪ e' →
--     e ∙ t ↪ e' ∙ t
