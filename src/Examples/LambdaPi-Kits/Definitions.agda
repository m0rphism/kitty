module Examples.LambdaPi-Kits.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; ∃-syntax)
open import Level using (Level; _⊔_)
open import Function using (id; _∘_; const)
open import Data.String

open import KitTheory.Prelude using (_∋_; _▷_) public

infix   3  _⊢_∶_  _⊢*_∶_  _⇓_
infixr  5  λ→_
infixl  6  _·_
infix   7  `_

-- Syntax ----------------------------------------------------------------------

data Mode : Set where
  𝕥 : Mode

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Mode
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Mode
  x y z                     : m ∈ µ
  ℓ ℓ₁ ℓ₂                    : Level
  A B C D E                 : Set ℓ

data Term : List Mode → Mode → Set where
  `_  : m ∈ µ → Term µ m
  _·_ : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
  λ→_ : Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  Π   : Term µ 𝕥 → Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  ★   : Term µ 𝕥

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Term µ 𝕥
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : Term µ 𝕥

-- Substitution ----------------------------------------------------------------

module TermSubst where

  -- Modes and Terms

  open import KitTheory.Modes

  𝕄 : Modes
  𝕄 = record { VarMode = Mode ; TermMode = Mode ; m→M = id }

  𝕋 : Terms 𝕄
  𝕋 = record { _⊢_ = Term ; `_ = `_ }

  -- Kits and Traversals

  open import KitTheory.Kit 𝕋
  open Kit {{...}} public

  infixl  5  _⋯_
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ m → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ m
  (` x)     ⋯ f = tm _ (f _ x)
  (λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ 𝕥))
  Π t₁ t₂   ⋯ f = Π (t₁ ⋯ f) (t₂ ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  ★         ⋯ f = ★

  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
          (` x) ⋯ f ≡ tm _ (f _ x)
  ⋯-var _ _ = refl

  kit-traversal : KitTraversal
  kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

  open KitTraversal kit-traversal public hiding (_⋯_; ⋯-var)

  instance 𝕂ᵣ = kitᵣ
  instance 𝕂ₛ = kitₛ

  -- Traversal Composition

  open import KitTheory.Compose 𝕋 kit-traversal
  open ComposeKit {{...}} public

  kit-assoc : KitAssoc
  kit-assoc = record { ⋯-assoc = ⋯-assoc } where
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : Term µ₁ m) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
    ⋯-assoc (` x)     f g = tm-⋯-∘ f g x
    ⋯-assoc (t₁ · t₂) f g = cong₂ _·_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
    ⋯-assoc (λ→ t)    f g = cong λ→_
      (t ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t (f ↑ _) (g ↑ _) ⟩
      t ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
      t ⋯ (g ∘ₖ f) ↑ _         ∎)
    ⋯-assoc (Π t₁ t₂) f g = cong₂ Π (⋯-assoc t₁ f g)
      (t₂ ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t₂ (f ↑ _) (g ↑ _) ⟩
      t₂ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t₂ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
      t₂ ⋯ (g ∘ₖ f) ↑ _         ∎)
    ⋯-assoc ★         f g = refl

  open KitAssoc kit-assoc public

  instance 𝕂ᵣᵣ = kitᵣᵣ
  instance 𝕂ᵣₛ = kitᵣₛ
  instance 𝕂ₛᵣ = kitₛᵣ
  instance 𝕂ₛₛ = kitₛₛ

  -- Applying the identity renaming/substitution does nothing.
  kit-assoc-lemmas : KitAssocLemmas
  kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
    ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ m) →
          v ⋯ idₖ {{𝕂}} ≡ v
    ⋯-id               (` x)                              = tm-vr x
    ⋯-id {µ = µ} {{𝕂}} (λ→ t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong λ→_ (⋯-id t)
    ⋯-id {µ = µ} {{𝕂}} (Π t₁ t₂) rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₂ Π (⋯-id t₁) (⋯-id t₂)
    ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
    ⋯-id               ★                                  = refl

  open KitAssocLemmas kit-assoc-lemmas public

  -- Types and Contexts

  -- open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

  -- -- Each variable mode corresponds to a term mode that represents its type.
  -- kit-type : KitType
  -- kit-type = record { ↑ₜ = λ { 𝕥 → 𝕥 } }

  -- -- open KitType kit-type public renaming (Ctx to Ctx'; wk-telescope to wk-telescope')

-- Semantics -------------------------------------------------------------------

data ValMode : Set where
  𝕧 𝕟 : ValMode

variable M M₁ M₂ : ValMode

m→M : Mode → ValMode
m→M 𝕥 = 𝕟

mutual
  data Value : List Mode → ValMode → Set where
    -- `_      : m ∈ µ → Value µ (m→M m)
    `_      : 𝕥 ∈ µ → Value µ 𝕟
    _·_     : Value µ 𝕟 → Value µ 𝕧 → Value µ 𝕟
    λ→_     : Value (𝕥 ∷ µ) 𝕧 → Value µ 𝕧
    Π       : Value µ 𝕧 → Value (𝕥 ∷ µ) 𝕧 → Value µ 𝕧
    ★       : Value µ 𝕧
    neutral : Value µ 𝕟 → Value µ 𝕧

module ValueSubst where

  -- Modes and Terms

  ``_ : m ∈ µ → Value µ (m→M m)
  ``_ {m = 𝕥} x = ` x

  open import KitTheory.Modes

  𝕄 : Modes
  𝕄 = record { VarMode = Mode ; TermMode = ValMode ; m→M = m→M }

  𝕋 : Terms 𝕄
  𝕋 = record { _⊢_ = Value ; `_ = ``_ }

  -- Kits and Traversals

  open import KitTheory.Kit 𝕋
  open Kit {{...}} public

  infixl  5  _⋯_
  _⋯_ : ∀ {{𝕂 : Kit}} → Value µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → Value µ₂ M
  (` x)     ⋯ f = tm _ (f _ x)
  (λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ 𝕥))
  Π t₁ t₂   ⋯ f = Π (t₁ ⋯ f) (t₂ ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  ★         ⋯ f = ★
  neutral n ⋯ f = neutral (n ⋯ f)

  kit-traversal : KitTraversal
  kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (`` x) ⋯ f ≡ tm _ (f _ x)
    ⋯-var {m = 𝕥} _ _ = refl

  open KitTraversal kit-traversal public hiding (_⋯_)

  instance 𝕂ᵣ = kitᵣ
  instance 𝕂ₛ = kitₛ

  -- Traversal Composition

  open import KitTheory.Compose 𝕋 kit-traversal
  open ComposeKit {{...}} public

  kit-assoc : KitAssoc
  kit-assoc = record { ⋯-assoc = ⋯-assoc } where
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : Value µ₁ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
    ⋯-assoc (` x)     f g = tm-⋯-∘ f g x
    ⋯-assoc (t₁ · t₂) f g = cong₂ _·_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
    ⋯-assoc (λ→ t)    f g = cong λ→_
      (t ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t (f ↑ _) (g ↑ _) ⟩
      t ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
      t ⋯ (g ∘ₖ f) ↑ _         ∎)
    ⋯-assoc (Π t₁ t₂) f g = cong₂ Π (⋯-assoc t₁ f g)
      (t₂ ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc t₂ (f ↑ _) (g ↑ _) ⟩
      t₂ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t₂ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
      t₂ ⋯ (g ∘ₖ f) ↑ _         ∎)
    ⋯-assoc ★         f g = refl
    ⋯-assoc (neutral n) f g = cong neutral (⋯-assoc n f g)

  open KitAssoc kit-assoc public

  instance 𝕂ᵣᵣ = kitᵣᵣ
  instance 𝕂ᵣₛ = kitᵣₛ
  instance 𝕂ₛᵣ = kitₛᵣ
  instance 𝕂ₛₛ = kitₛₛ

  -- Applying the identity renaming/substitution does nothing.
  kit-assoc-lemmas : KitAssocLemmas
  kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
    ⋯-id : ∀ {{𝕂 : Kit}} (v : Value µ M) →
          v ⋯ idₖ {{𝕂}} ≡ v
    ⋯-id               (` x)                              = tm-vr x
    ⋯-id {µ = µ} {{𝕂}} (λ→ t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong λ→_ (⋯-id t)
    ⋯-id {µ = µ} {{𝕂}} (Π t₁ t₂) rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₂ Π (⋯-id t₁) (⋯-id t₂)
    ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
    ⋯-id               ★                                  = refl
    ⋯-id               (neutral n)                        = cong neutral (⋯-id n)

  open KitAssocLemmas kit-assoc-lemmas public

  -- Types and Contexts

  open import KitTheory.Types 𝕋

  kit-type : KitType
  kit-type = record { ↑ₜ = λ { M → 𝕧 } }

  open import KitTheory.OPE 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type public

  open KitType kit-type public

open TermSubst public
open ValueSubst using (Ctx; wk-telescope; _▶_; OPE; ope-keep; ope-drop; ope-id; ope-pres-telescope) renaming (_⋯_ to _⋯ᵥ_; _↑_ to _↑ᵥ_) public

⟦_⟧ : Value µ M → Term µ 𝕥
⟦ ` x ⟧          = ` x
⟦ n · v ⟧        = ⟦ n ⟧ · ⟦ v ⟧
⟦ λ→ v ⟧         = λ→ ⟦ v ⟧
⟦ Π v₁ v₂ ⟧      = Π ⟦ v₁ ⟧ ⟦ v₂ ⟧
⟦ ★ ⟧            = ★
⟦ neutral n ⟧    = ⟦ n ⟧

⟦_⟧' : Value µ M → Term µ m
⟦_⟧' {m = 𝕥} = ⟦_⟧

variable
  v v₁ v₂ v₃ v' v₁' v₂' v₃' : Value µ 𝕧
  τ τ₁ τ₂ τ₃ τ' τ₁' τ₂' τ₃' : Value µ 𝕧
  n n₁ n₂ n₃ n' n₁' n₂' n₃' : Value µ 𝕟
  Γ Γ₁ Γ₂ Γ' : Ctx µ

data _⇓_ : Term µ 𝕥 → Value µ 𝕧 → Set where
  ⇓-λ :
    e ⇓ v →
    λ→ e ⇓ λ→ v
  ⇓-Π :
    t₁ ⇓ τ₁ →
    t₂ ⇓ τ₂ →
    Π t₁ t₂ ⇓ Π τ₁ τ₂
  ⇓-` :
    ` x ⇓ neutral (` x)
  ⇓-·ᵥ : {t₁ : Term µ 𝕥} →
    t₁ ⇓ λ→ v₁ →
    t₂ ⇓ v₂ →
    ⟦ v₁ ⟧ ⋯ ⦅ ⟦ v₂ ⟧ ⦆ ⇓ v →
    t₁ · t₂ ⇓ v
  ⇓-·ₙ : {t₁ : Term µ 𝕥} →
    t₁ ⇓ neutral n₁ →
    t₂ ⇓ v₂ →
    t₁ · t₂ ⇓ neutral (n₁ · v₂)
  ⇓-★ :
    ★ ⇓ ★ {µ}

_⇓'_ : Term µ m → Value µ 𝕧 → Set
_⇓'_ {m = 𝕥} = _⇓_

-- Typing ----------------------------------------------------------------------

data _⊢_∶_ : Ctx µ → Term µ 𝕥 → Value µ 𝕧 → Set where
  τ-` : ∀ {Γ : Ctx µ} {t : Value µ 𝕧} {x : 𝕥 ∈ µ} →
    wk-telescope Γ x ≡ t →
    Γ ⊢ ` x ∶ t
  τ-λ : ∀ {Γ : Ctx µ} →
    Γ ⊢ t₁ ∶ ★ →
    t₁ ⇓ τ₁ →
    Γ ▶ τ₁ ⊢ e ∶ τ₂ →
    Γ ⊢ λ→ e ∶ Π τ₁ τ₂
  τ-· : ∀ {Γ : Ctx µ} →
    Γ ⊢ e₁ ∶ Π τ₁ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    ⟦ τ₂ ⟧ ⋯ ⦅ e₂ ⦆ ⇓ τ →
    Γ ⊢ e₁ · e₂ ∶ τ
  τ-Π : ∀ {Γ : Ctx µ} →
    t₁ ⇓ τ₁ →
    Γ      ⊢ t₁      ∶ ★ →
    Γ ▶ τ₁ ⊢ t₂      ∶ ★ →
    Γ      ⊢ Π t₁ t₂ ∶ ★
  τ-★ : ∀ {Γ : Ctx µ} →
    Γ ⊢ ★ ∶ ★

_⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
_⊢*_∶_ {µ₂ = µ₂} {µ₁ = µ₁} Γ₂ σ Γ₁ =
  (x : µ₁ ∋ 𝕥) → ∃[ τ ] (
    ⟦ wk-telescope Γ₁ x ⟧ ⋯ σ ⇓ τ ×
    Γ₂ ⊢ σ _ x ∶ τ
  )
