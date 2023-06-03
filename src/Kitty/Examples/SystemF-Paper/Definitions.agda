module Kitty.Examples.SystemF-Paper.Definitions where

open import Kitty.Examples.SystemF-Paper.Kits
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- -- Modes -----------------------------------------------------------------------

data Mode : ModeTy → Set where
  𝕖 : Mode Var   -- Expressions
  𝕥 : Mode Var   -- Types
  𝕜 : Mode Term  -- Kinds

variable
  mt                        : ModeTy
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode mt
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List (Mode Var)
  x y z                     : µ ∋ m

-- Syntax ----------------------------------------------------------------------

-- Expressions, Types, and Kinds
data _⊢_ : List (Mode Var) → Mode mt → Set where
  `_        : ∀ {m}  →  µ ∋ m  →  µ ⊢ m
  λx_       : (𝕖 ∷ µ) ⊢ 𝕖  →  µ ⊢ 𝕖
  Λα_       : (𝕥 ∷ µ) ⊢ 𝕖  →  µ ⊢ 𝕖
  ∀[α∶_]_   : µ ⊢ 𝕜  →  (𝕥 ∷ µ) ⊢ 𝕥  →  µ ⊢ 𝕥
  _·_       : µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
  _∙_       : µ ⊢ 𝕖  →  µ ⊢ 𝕥  →  µ ⊢ 𝕖
  _⇒_       : µ ⊢ 𝕥  →  µ ⊢ 𝕥  →  µ ⊢ 𝕥
  ★         : µ ⊢ 𝕜

variable
  e e₁ e₂ e₃ e' e₁' e₂' : µ ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂' : µ ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂' : µ ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂' : µ ⊢ m

-- Substitution & Lemmas -------------------------------------------------------

terms : Terms
terms = record
  { Mode        = Mode
  ; _⊢_         = _⊢_
  ; `_          = `_
  ; `-injective = λ { refl → refl }
  }

open Terms terms hiding (Mode; _⊢_; `_)

_⋯_ :
  ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} 
  → µ₁ ⊢ m → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ m
(` x)          ⋯ ϕ = `/id (ϕ _ x)
(λx t)         ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(Λα t)         ⋯ ϕ = Λα (t ⋯ (ϕ ↑ 𝕥))
(∀[α∶ t₁ ] t₂) ⋯ ϕ = ∀[α∶ t₁ ⋯ ϕ ] (t₂ ⋯ (ϕ ↑ 𝕥))
(t₁ · t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ∙ t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
(t₁ ⇒ t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
★              ⋯ ϕ = ★

⋯-id :
  ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ} (t : µ ⊢ m)
  → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id ⦃ K ⦄ (` x)    = id/`/id ⦃ K ⦄ x
⋯-id (λx t)         = cong λx_ (t ⋯ (id ↑ 𝕖) ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
                                t ⋯ id       ≡⟨ ⋯-id t ⟩
                                t            ∎)
⋯-id (Λα t)         = cong Λα_ (t ⋯ (id ↑ 𝕥) ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
                                t ⋯ id       ≡⟨ ⋯-id t ⟩
                                t            ∎)
⋯-id (∀[α∶ t₁ ] t₂) = cong₂ ∀[α∶_]_ (⋯-id t₁)
                                    (t₂ ⋯ (id ↑ 𝕥) ≡⟨ cong (t₂ ⋯_) (~-ext id↑~id) ⟩
                                     t₂ ⋯ id       ≡⟨ ⋯-id t₂ ⟩
                                     t₂            ∎)
⋯-id (t₁ · t₂)      = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ∙ t₂)      = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)      = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★              = refl

traversal : Traversal
traversal = record
  { _⋯_   = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id  = ⋯-id
  }

open Traversal traversal hiding (_⋯_; ⋯-id)

⋯-assoc :
  ∀ {_∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : Scoped}
    ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    {µ₁ µ₂ µ₃}
    (t : µ₁ ⊢ m) (ϕ₁ : µ₁ –[ K₁ ]→ µ₂) (ϕ₂ : µ₂ –[ K₂ ]→ µ₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₘ ϕ₂)
⋯-assoc (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
⋯-assoc (λx t)         ϕ₁ ϕ₂ = cong λx_ ((t ⋯ (ϕ₁ ↑ 𝕖)) ⋯ (ϕ₂ ↑ 𝕖)  ≡⟨ ⋯-assoc t (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ⟩
                                         t ⋯ ((ϕ₁ ↑ 𝕖) ·ₘ (ϕ₂ ↑ 𝕖)) ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))) ⟩
                                         t ⋯ ((ϕ₁ ·ₘ ϕ₂) ↑ 𝕖)       ∎)
⋯-assoc (Λα t)         ϕ₁ ϕ₂ = cong Λα_ ((t ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)  ≡⟨ ⋯-assoc t (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
                                         t ⋯ ((ϕ₁ ↑ 𝕥) ·ₘ (ϕ₂ ↑ 𝕥)) ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
                                         t ⋯ ((ϕ₁ ·ₘ ϕ₂) ↑ 𝕥)       ∎)
⋯-assoc (∀[α∶ t₁ ] t₂) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ (⋯-assoc t₁ ϕ₁ ϕ₂)
                                        ((t₂ ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)  ≡⟨ ⋯-assoc t₂ (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
                                         t₂ ⋯ ((ϕ₁ ↑ 𝕥) ·ₘ (ϕ₂ ↑ 𝕥)) ≡⟨ cong (t₂ ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
                                         t₂ ⋯ ((ϕ₁ ·ₘ ϕ₂) ↑ 𝕥)       ∎)
⋯-assoc (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ∙ t₂)      ϕ₁ ϕ₂ = cong₂ _∙_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc ★              ϕ₁ ϕ₂ = refl

compose-traversal : ComposeTraversal
compose-traversal = record { ⋯-assoc = ⋯-assoc }

open ComposeTraversal compose-traversal hiding (⋯-assoc)

-- Type System -----------------------------------------------------------------

types : Types
types = record { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 } }

open Types types

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ
  T T₁ T₂ T' T₁' T₂' : µ ∶⊢ m

data _⊢_∶_ : Ctx µ → µ ⊢ m → µ ∶⊢ m → Set where
  ⊢` : ∀ {x : µ ∋ m} {T : µ ∶⊢ m} →
    Γ ∋ x ∶ T →
    Γ ⊢ ` x ∶ T
  ⊢λ : ∀ {e : (𝕖 ∷ µ) ⊢ 𝕖} →
    (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
    Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ :
    (k ∷ₜ Γ) ⊢ e ∶ t₂ →
    Γ ⊢ Λα e ∶ ∀[α∶ k ] t₂
  ⊢· :
    Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙ : {Γ : Ctx µ} →
    (k₂ ∷ₜ Γ) ⊢ t₁ ∶ k₁ →
    Γ ⊢ t₂ ∶ k₂ →
    Γ ⊢ e₁ ∶ ∀[α∶ k₂ ] t₁ →
    Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆
  ⊢τ :
    Γ ⊢ t ∶ ★

typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing typing hiding (_⊢_∶_; ⊢`) 

_⊢⋯_ :
  ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    ⦃ TK : TypingKit K W C₁ C₂ ⦄
    {µ₁ µ₂ mt} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {m : Mode mt}
    {e : µ₁ ⊢ m} {t : µ₁ ∶⊢ m} {ϕ : µ₁ –[ K ]→ µ₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ⊢x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ = ⊢λ (subst (_ ⊢ _ ∶_) (sym (⋯-↑-wk t₂ _ _)) (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ = subst (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
                                                 (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢τ ⊢⋯ ⊢ϕ = ⊢τ

typing-traversal : TypingTraversal
typing-traversal = record { _⊢⋯_ = _⊢⋯_ }

open TypingTraversal typing-traversal hiding (_⊢⋯_)

-- Semantics -------------------------------------------------------------------

mutual
  data Neutral : µ ⊢ m → Set where
    `_  : ∀ (x : µ ∋ m) → Neutral (` x)
    _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙t : Neutral e₁ → Neutral (e₁ ∙ t₂)

  data Value : µ ⊢ m → Set where
    λx_     : ∀ (e : (𝕖 ∷ µ) ⊢ 𝕖) → Value (λx e)
    Λα_     : ∀ (e : (𝕥 ∷ µ) ⊢ 𝕖) → Value (Λα e)
    neutral : Neutral e → Value e

data _↪_ : µ ⊢ m → µ ⊢ m → Set where
  β-λ : ∀ {e₂ : µ ⊢ 𝕖} →
    (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ : ∀ {t₂ : µ ⊢ 𝕥} →
    (Λα e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆
  ξ-λ :
    e ↪ e' →
    λx e ↪ λx e'
  ξ-Λ :
    e ↪ e' →
    Λα e ↪ Λα e'
  ξ-·₁ :
    e₁ ↪ e₁' →
    e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂ :
    e₂ ↪ e₂' →
    e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙₁ :
    e₁ ↪ e₁' →
    e₁ ∙ t₂ ↪ e₁' ∙ t₂

-- Subject Reduction -----------------------------------------------------------

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e' →
  Γ ⊢ e' ∶ t
subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂)   β-λ          = subst (_ ⊢ _ ∶_) ({!wk-cancels-⦅⦆-⋯ t₂ _!}) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁))         β-Λ          = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
subject-reduction (⊢λ ⊢e)                      (ξ-λ e↪e')    = ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e)                      (ξ-Λ e↪e')    = ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₁ e₁↪e₁') = ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                 (ξ-·₂ e₂↪e₂') = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁)             (ξ-∙₁ e₁↪e₁') = ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
