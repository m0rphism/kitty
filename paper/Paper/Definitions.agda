module Paper.Definitions where

--! F >

open import Paper.Kits
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

-- Sorts -----------------------------------------------------------------------

--! Sort
data Sort : SortTy → Set where -- Our syntax supports:
  𝕖  : Sort Var    -- expressions and expression variables;
  𝕥  : Sort Var    -- types and type variables; and
  𝕜  : Sort NoVar  -- kinds, but no kind variables.

-- Syntax ----------------------------------------------------------------------

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : List (Sort Var)
  x y z x₁ x₂                : S ∋ s

--! Syntax
data _⊢_ : List (Sort Var) → Sort st → Set where
  `_        : S ∋ s → S ⊢ s                -- Expr and Type Var
  λx_       : (𝕖 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖          -- Expr Abstraction
  Λα_       : (𝕥 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖          -- Type Abstraction
  ∀[α∶_]_   : S ⊢ 𝕜 → (𝕥 ∷ S) ⊢ 𝕥 → S ⊢ 𝕥  -- Univ Quant
  _·_       : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖        -- Expr Application
  _∙_       : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖        -- Type Application
  _⇒_       : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥        -- Function Type
  ★         : S ⊢ 𝕜                        -- Type Kind

private variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂'  : S ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂'  : S ⊢ s

-- Substitution & Lemmas -------------------------------------------------------

module Example1 where
  pattern [_,_] x y = x ∷ y ∷ []

  --! ExampleSubRen
  _→ᵣ_ _→ₛ_ : List (Sort Var) → List (Sort Var) → Set
  S₁ →ᵣ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s
  S₁ →ₛ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s

  --! ExampleSub
  σ : [ 𝕖 , 𝕥 ] →ₛ []                   -- replaces:
  σ .𝕖 zero        = λx (` zero)        --   expr-var 0 with an expr
  σ .𝕥 (suc zero)  = ∀[α∶ ★ ] (` zero)  --   type-var 1 with a type

--! Terms
SystemF-Terms : Terms
SystemF-Terms = record
  { Sort         = Sort
  ; _⊢_          = _⊢_
  ; `_           = `_
  ; `-injective  = λ { refl → refl } }

open Terms SystemF-Terms hiding (Sort; _⊢_; `_)

--! TraversalOp
_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (ϕ _ x)
(λx t)          ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(Λα t)          ⋯ ϕ = Λα (t ⋯ (ϕ ↑ 𝕥))
(∀[α∶ t₁ ] t₂)  ⋯ ϕ = ∀[α∶ t₁ ⋯ ϕ ] (t₂ ⋯ (ϕ ↑ 𝕥))
(t₁ · t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ∙ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
★               ⋯ ϕ = ★

--! TraversalId
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
--! TraversalIdProofInteresting
⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (λx t)          = cong λx_ (
  t ⋯ (id ↑ 𝕖)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
--! TraversalIdProofRest
⋯-id (Λα t)          = cong Λα_ (
  t ⋯ (id ↑ 𝕥)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
⋯-id (∀[α∶ t₁ ] t₂)  = cong₂ ∀[α∶_]_ (⋯-id t₁) (
  t₂ ⋯ (id ↑ 𝕥)  ≡⟨ cong (t₂ ⋯_) (~-ext id↑~id) ⟩
  t₂ ⋯ id        ≡⟨ ⋯-id t₂ ⟩
  t₂             ∎)
⋯-id (t₁ ∙ t₂)       = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★               = refl

--! Traversal {
traversal : Traversal
traversal = record
  { _⋯_    = _⋯_
  ; ⋯-var  = λ x ϕ → refl
  ; ⋯-id   = ⋯-id }

open Traversal traversal hiding (_⋯_; ⋯-id)
--! }

--! Assoc
⋯-assoc :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
--! AssocProofInteresting
⋯-assoc (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
⋯-assoc (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-assoc t₁ ϕ₁ ϕ₂)
                                          (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (λx t)         ϕ₁ ϕ₂ = cong λx_ (
  (t ⋯ (ϕ₁ ↑ 𝕖)) ⋯ (ϕ₂ ↑ 𝕖)   ≡⟨ ⋯-assoc t (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕖) ·ₖ (ϕ₂ ↑ 𝕖))  ≡⟨ cong (t ⋯_) (sym (
                                   ~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕖)        ∎)
--! AssocProofRest
⋯-assoc (Λα t)         ϕ₁ ϕ₂ = cong Λα_ (
  (t ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
    ≡⟨ ⋯-assoc t (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
    ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
    ∎)
⋯-assoc (∀[α∶ t₁ ] t₂) ϕ₁ ϕ₂ =
  cong₂ ∀[α∶_]_ (⋯-assoc t₁ ϕ₁ ϕ₂) (
    (t₂ ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
      ≡⟨ ⋯-assoc t₂ (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
    t₂ ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
      ≡⟨ cong (t₂ ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
    t₂ ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
      ∎)
⋯-assoc (t₁ ∙ t₂)      ϕ₁ ϕ₂ =
  cong₂ _∙_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂)      ϕ₁ ϕ₂ =
  cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc ★              ϕ₁ ϕ₂ = refl

--! ComposeTraversal {
compose-traversal : ComposeTraversal
compose-traversal = record { ⋯-assoc = ⋯-assoc }

open ComposeTraversal compose-traversal hiding (⋯-assoc)
--! }

-- Type System -----------------------------------------------------------------

--! Types {
types : Types
types = record { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 } }

open Types types
--! }

private variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

--! Typing
data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢`  :  ∀ {x : S ∋ s} {T : S ∶⊢ s} →
         Γ ∋ x ∶ T →
         Γ ⊢ ` x ∶ T
  ⊢λ  :  ∀ {e : (𝕖 ∷ S) ⊢ 𝕖} →
         (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
         Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ  :  (k ∷ₜ Γ) ⊢ e ∶ t₂ →
         Γ ⊢ Λα e ∶ ∀[α∶ k ] t₂
  ⊢·  :  Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
         Γ ⊢ e₂ ∶ t₁ →
         Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙  :  {Γ : Ctx S} →
         (k₂ ∷ₜ Γ) ⊢ t₁ ∶ k₁ →
         Γ ⊢ t₂ ∶ k₂ →
         Γ ⊢ e₁ ∶ ∀[α∶ k₂ ] t₁ →
         Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆
  ⊢τ  :  Γ ⊢ t ∶ ★

--! TypingInst {
typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing typing hiding (_⊢_∶_; ⊢`) 
--! }

--! Preserve
_⊢⋯_ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    ⦃ TK : TypingKit K W C₁ C₂ ⦄
    {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ⊢x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ = ⊢λ (subst  (_ ⊢ _ ∶_)
                                   (sym (⋯-↑-wk t₂ _ _))
                                   (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ =
  subst  (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
         (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢τ ⊢⋯ ⊢ϕ = ⊢τ

--! TypingTraversal {
typing-traversal : TypingTraversal
typing-traversal = record { _⊢⋯_ = _⊢⋯_ }

open TypingTraversal typing-traversal hiding (_⊢⋯_)
--! }

-- Semantics -------------------------------------------------------------------

--! Values {
mutual
  data Neutral : S ⊢ s → Set where
    `_   : ∀ (x : S ∋ s) → Neutral (` x)
    _·_  : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
    _∙t  : Neutral e₁ → Neutral (e₁ ∙ t₂)

  data Value : S ⊢ s → Set where
    λx_      : ∀ (e : (𝕖 ∷ S) ⊢ 𝕖) → Value (λx e)
    Λα_      : ∀ (e : (𝕥 ∷ S) ⊢ 𝕖) → Value (Λα e)
    neutral  : Neutral e → Value e
--! }

--! Reduction
data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ   :  ∀ {e₂ : S ⊢ 𝕖} → (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ   :  ∀ {t₂ : S ⊢ 𝕥} → (Λα e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆
  ξ-λ   :  e ↪ e' → λx e ↪ λx e'
  ξ-Λ   :  e ↪ e' → Λα e ↪ Λα e'
  ξ-·₁  :  e₁ ↪ e₁' → e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂  :  e₂ ↪ e₂' → e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙₁  :  e₁ ↪ e₁' → e₁ ∙ t₂ ↪ e₁' ∙ t₂

-- Subject Reduction -----------------------------------------------------------

--! SubjectReduction
subject-reduction : Γ ⊢ e ∶ t → e ↪ e' → Γ ⊢ e' ∶ t
--! SubjectReductionProofInteresting
subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂) β-λ =
  subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆-⋯ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁)) β-Λ =
  ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
--! SubjectReductionProofRest
subject-reduction (⊢λ ⊢e) (ξ-λ e↪e') =
  ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e) (ξ-Λ e↪e') =
  ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') =
  ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') =
  ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁) (ξ-∙₁ e₁↪e₁') =
  ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')
