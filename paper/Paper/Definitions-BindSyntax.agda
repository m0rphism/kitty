module Paper.Definitions-BindSyntax where

--! FB >

open import Paper.Kits
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; ∃-syntax; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  `λ_  `Λ_  `∀_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Sorts -----------------------------------------------------------------------

--! Sort
data Sort : SortTy → Set where
  𝕖  : Sort Var    -- Expressions
  𝕥  : Sort Var    -- Types
  𝕜  : Sort NoVar  -- Kinds
  𝕓  : ∀ {st} → Sort Var → Sort st → Sort NoVar  -- Binder

↑ᵗ : ∀ {st} → Sort st → ∃[ st' ] Sort st'
↑ᵗ 𝕖       = _ , 𝕥
↑ᵗ 𝕥       = _ , 𝕜
↑ᵗ 𝕜       = _ , 𝕜
↑ᵗ (𝕓 S s) = _ , 𝕓 S (proj₂ (↑ᵗ s))

-- Syntax ----------------------------------------------------------------------

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : List (Sort Var)
  x y z x₁ x₂                : S ∋ s

open import Data.List using (_++_)

--! Syntax
data _⊢_ : List (Sort Var) → Sort st → Set where
  `_        : S ∋ s → S ⊢ s                -- Term and Type Variables
  `λ_       : S ⊢ 𝕓 𝕖 𝕖 → S ⊢ 𝕖          -- Term Abstraction
  `Λ_       : S ⊢ 𝕓 𝕥 𝕖 → S ⊢ 𝕖          -- Type Abstraction
  `∀_       : S ⊢ 𝕓 𝕥 𝕥 → S ⊢ 𝕥           -- Universal Quantification
  _·_       : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖        -- Term Application
  _∙_       : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖        -- Type Application
  _⇒_       : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥        -- Function Type
  ★         : S ⊢ 𝕜                        -- Type Kind
  [x∶_]_    : ∀ {s'} → S ⊢ proj₂ (↑ᵗ s') → (s' ∷ S) ⊢ s → S ⊢ 𝕓 s' s   -- Binder

variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂'  : S ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂'  : S ⊢ s

-- Substitution & Lemmas -------------------------------------------------------

--! Terms {
terms : Terms
terms = record
  { Sort         = Sort
  ; _⊢_          = _⊢_
  ; `_           = `_
  ; `-injective  = λ { refl → refl } }

open Terms terms hiding (Sort; _⊢_; `_)
--! }

--! TraversalOp
_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (ϕ _ x)
(`λ t)          ⋯ ϕ = `λ (t ⋯ ϕ)
(`Λ t)          ⋯ ϕ = `Λ (t ⋯ ϕ)
(`∀ t)          ⋯ ϕ = `∀ (t ⋯ ϕ)
(t₁ · t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ∙ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
★               ⋯ ϕ = ★
([x∶ t ] e)     ⋯ ϕ = [x∶ (t ⋯ ϕ) ] (e ⋯ (ϕ ↑ _))

--! TraversalId
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
--! TraversalIdProofInteresting
⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (`λ t)          = cong `λ_ (⋯-id t)
--! TraversalIdProofRest
⋯-id (`Λ t)          = cong `Λ_ (⋯-id t)
⋯-id (`∀ t)          = cong `∀_ (⋯-id t)
⋯-id (t₁ ∙ t₂)       = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★               = refl
⋯-id ([x∶ t ] e) = cong₂ [x∶_]_ (⋯-id t) (
  e ⋯ (id ↑ _) ≡⟨ cong (e ⋯_) (~-ext id↑~id) ⟩
  e ⋯ id         ≡⟨ ⋯-id e ⟩
  e              ∎)

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
⋯-assoc (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (`λ t)         ϕ₁ ϕ₂ = cong `λ_ (⋯-assoc t ϕ₁ ϕ₂)
--! AssocProofRest
⋯-assoc (`Λ t)         ϕ₁ ϕ₂ = cong `Λ_ (⋯-assoc t ϕ₁ ϕ₂)
⋯-assoc (`∀ t)         ϕ₁ ϕ₂ = cong `∀_ (⋯-assoc t ϕ₁ ϕ₂)
⋯-assoc (t₁ ∙ t₂)      ϕ₁ ϕ₂ = cong₂ _∙_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-assoc t₁ ϕ₁ ϕ₂) (⋯-assoc t₂ ϕ₁ ϕ₂)
⋯-assoc ★              ϕ₁ ϕ₂ = refl
⋯-assoc ([x∶ t ] e)     ϕ₁ ϕ₂ = cong₂ [x∶_]_ (⋯-assoc t ϕ₁ ϕ₂) (
  (e ⋯ (ϕ₁ ↑ _)) ⋯ (ϕ₂ ↑ _)   ≡⟨ ⋯-assoc e (ϕ₁ ↑ _) (ϕ₂ ↑ _) ⟩
  e ⋯ ((ϕ₁ ↑ _) ·ₖ (ϕ₂ ↑ _))  ≡⟨ cong (e ⋯_) (sym (
                                   ~-ext (dist-↑-· _ ϕ₁ ϕ₂))) ⟩
  e ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ _)        ∎)

--! ComposeTraversal {
compose-traversal : ComposeTraversal
compose-traversal = record { ⋯-assoc = ⋯-assoc }

open ComposeTraversal compose-traversal hiding (⋯-assoc)
--! }

-- Type System -----------------------------------------------------------------

--! Types {
types : Types
types = record { ↑ᵗ = ↑ᵗ }

open Types types hiding (↑ᵗ)
--! }

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

--! Typing
data _⊢_∶_ : ∀ {st} {s : Sort st} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢`  :  ∀ {x : S ∋ s} {T : S ∶⊢ s} →
         Γ ∋ x ∶ T →
         Γ ⊢ ` x ∶ T
  -- ⊢λ  :  ∀ {e : (𝕖 ∷ S) ⊢ 𝕖} →
  --        (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
  --        Γ ⊢ `λ [x∶ t₁ ] e ∶ t₁ ⇒ t₂
  ⊢λ  :  ∀ {e : S ⊢ 𝕓 𝕖 𝕖} →
         Γ ⊢ e ∶ [x∶ t₁ ] (wk _ t₂) →
         Γ ⊢ `λ e ∶ t₁ ⇒ t₂
  ⊢Λ  :  ∀ {e : S ⊢ 𝕓 𝕥 𝕖} →
         Γ ⊢ e ∶ [x∶ k ] t₂ →
         Γ ⊢ `Λ e ∶ `∀ [x∶ k ] t₂
  ⊢·  :  Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
         Γ ⊢ e₂ ∶ t₁ →
         Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙  :  {Γ : Ctx S} →
         (k₂ ∷ₜ Γ) ⊢ t₁ ∶ k₁ →
         Γ ⊢ t₂ ∶ k₂ →
         Γ ⊢ e₁ ∶ `∀ [x∶ k₂ ] t₁ →
         Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆
  ⊢τ  :  Γ ⊢ t ∶ ★
  ⊢bind : ∀ {e : (s' ∷ S) ⊢ s} {t₁ : S ∶⊢ s'} {t₂ : (s' ∷ S) ∶⊢ s} {- {k : S ∶⊢ proj₂ (↑ᵗ s')} -} →
    -- Γ ⊢ t₁ ∶ k →
    (t₁ ∷ₜ Γ) ⊢ e ∶ t₂ →
    Γ ⊢ [x∶ t₁ ] e ∶ [x∶ t₁ ] t₂




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
⊢λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ = ⊢λ (subst (λ ■ → _ ⊢ _ ∶ [x∶ _ ] ■) (sym (⋯-↑-wk t₂ _ _)) (⊢e ⊢⋯ ⊢ϕ))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ ⊢ϕ)
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ =
  subst  (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
         (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢τ ⊢⋯ ⊢ϕ = ⊢τ
⊢bind ⊢e ⊢⋯ ⊢ϕ = ⊢bind (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))

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
    `λ_      : ∀ (e : S ⊢ 𝕓 𝕖 𝕖) → Value (`λ e)
    `Λ_      : ∀ (e : S ⊢ 𝕓 𝕥 𝕖) → Value (`Λ e)
    neutral  : Neutral e → Value e
--! }

--! Reduction
data _↪_ : ∀ {st} {s : Sort st} → S ⊢ s → S ⊢ s → Set where
  β-λ    :  ∀ {e₂ : S ⊢ 𝕖} → (`λ [x∶ t₁ ] e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ    :  ∀ {t₂ : S ⊢ 𝕥} → (`Λ [x∶ k₁ ] e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆
  ξ-λ    :  E ↪ E' → `λ E ↪ `λ E'
  ξ-Λ    :  E ↪ E' → `Λ E ↪ `Λ E'
  ξ-·₁   :  E₁ ↪ E₁' → E₁ · E₂ ↪ E₁' · E₂
  ξ-·₂   :  E₂ ↪ E₂' → E₁ · E₂ ↪ E₁  · E₂'
  ξ-∙₁   :  E₁ ↪ E₁' → E₁ ∙ E₂ ↪ E₁' ∙ E₂
  ξ-bind :  E₂ ↪ E₂' → [x∶ E₁ ] E₂ ↪ [x∶ E₁ ] E₂'

-- Subject Reduction -----------------------------------------------------------

--! SubjectReduction
subject-reduction : Γ ⊢ E₁ ∶ E₂ → E₁ ↪ E₁' → Γ ⊢ E₁' ∶ E₂
--! SubjectReductionProofInteresting
subject-reduction (⊢· {t₂ = t₂} (⊢λ (⊢bind ⊢e₁)) ⊢e₂) β-λ =
  subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆-⋯ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ (⊢bind ⊢e₁))) β-Λ =
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
subject-reduction (⊢bind ⊢e₁) (ξ-bind e₁↪e₁') =
  ⊢bind (subject-reduction ⊢e₁ e₁↪e₁')

