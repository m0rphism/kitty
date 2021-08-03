module Examples.LambdaPi-Kits.Definitions-ValueMode where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_)
open import Level using (Level; _⊔_)
open import Function using (id; _∘_; const)
open import Data.String

open import KitTheory.Prelude using (_∋_; _,_) public

infix   3  _⊢_∶_  _⊢*_∶_  _⇓_
infixr  5  λ→_
infixl  6  _·_
infix   7  `_

-- Syntax ----------------------------------------------------------------------

data Modeᵥ : Set where
  𝕥 𝕟 : Modeᵥ

data Modeₜ : Set where
  𝕥 𝕧 𝕟 : Modeₜ

m→M : Modeᵥ → Modeₜ
m→M 𝕥 = 𝕥
m→M 𝕟 = 𝕟

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Modeᵥ
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : Modeₜ
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List Modeᵥ
  µ₁₁ µ₁₂ µ₂₁ µ₂₂           : List Modeᵥ
  x y z                     : m ∈ µ
  ℓ ℓ₁ ℓ₂                    : Level
  A B C D E                 : Set ℓ

data Term : List Modeᵥ → Modeₜ → Set where
  `[_]_ : m→M m ≡ M → m ∈ µ → Term µ M
  _·_   : Term µ 𝕥 → Term µ 𝕥 → Term µ 𝕥
  λ→_   : Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  Π     : Term µ 𝕥 → Term (𝕥 ∷ µ) 𝕥 → Term µ 𝕥
  ★     : Term µ 𝕥

  _·ⁿ_ : Term µ 𝕟 → Term µ 𝕧 → Term µ 𝕟

  λ→ᵛ_     : Term (𝕟 ∷ µ) 𝕧 → Term µ 𝕧
  Πᵛ       : Term µ 𝕧 → Term (𝕟 ∷ µ) 𝕧 → Term µ 𝕧
  ★ᵛ       : Term µ 𝕧
  neutralᵛ : Term µ 𝕟 → Term µ 𝕧

pattern `_ x = `[ refl ] x

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Term µ 𝕥
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : Term µ 𝕥
  v v₁ v₂ v₃ v' v₁' v₂' v₃' : Term µ 𝕧
  τ τ₁ τ₂ τ₃ τ' τ₁' τ₂' τ₃' : Term µ 𝕧
  n n₁ n₂ n₃ n' n₁' n₂' n₃' : Term µ 𝕟

-- Substitution ----------------------------------------------------------------

-- Modes and Terms

open import KitTheory.Modes

𝕄 : Modes
𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

𝕋 : Terms 𝕄
𝕋 = record { _⊢_ = Term ; `_ = `_ }

-- Kits and Traversals

open import KitTheory.Kit 𝕋
open Kit {{...}} public

kit-traversal : KitTraversal
kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ M
  (` x)     ⋯ f = tm _ (f _ x)
  (λ→ t)    ⋯ f = λ→ (t ⋯ (f ↑ 𝕥))
  Π t₁ t₂   ⋯ f = Π (t₁ ⋯ f) (t₂ ⋯ (f ↑ 𝕥))
  (t₁ · t₂) ⋯ f = (t₁ ⋯ f) · (t₂ ⋯ f)
  ★         ⋯ f = ★

  (n₁ ·ⁿ v₂) ⋯ f = (n₁ ⋯ f) ·ⁿ (v₂ ⋯ f)

  (λ→ᵛ v) ⋯ f  = λ→ᵛ (v ⋯ (f ↑ 𝕟))
  Πᵛ v₁ v₂ ⋯ f = Πᵛ (v₁ ⋯ f) (v₂ ⋯ (f ↑ 𝕟))
  ★ᵛ ⋯ f       = ★ᵛ
  neutralᵛ n ⋯ f = neutralᵛ (n ⋯ f)

  ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
          (` x) ⋯ f ≡ tm _ (f _ x)
  ⋯-var _ _ = refl

open KitTraversal kit-traversal public

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Traversal Composition

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : Term µ₁ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
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
  ⋯-assoc t         f g = {!!}

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ M) →
         v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id               (` x)                              = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λ→ t)    rewrite id↑≡id {{𝕂}} 𝕥 µ = cong λ→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Π t₁ t₂) rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₂ Π (⋯-id t₁) (⋯-id t₂)
  ⋯-id               (t₁ · t₂)                          = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id               ★                                  = refl
  ⋯-id               t                                  = {!!}

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts

open import KitTheory.Types 𝕋 kit-traversal kit-assoc kit-assoc-lemmas

-- Each variable mode corresponds to a term mode that represents its type.
kit-type : KitType
kit-type = record { ↑ₜ = λ { _ → 𝕧 } }

open KitType kit-type public

variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx µ

-- Semantics -------------------------------------------------------------------

-- mutual
--   data Neutral : List Mode → Mode → Set where
--     `_  : m ∈ µ → Neutral µ m
--     _·_ : Neutral µ 𝕥 → Value µ 𝕥 → Neutral µ 𝕥

--   data Value : List Mode → Mode → Set where
--     λ→_     : Value (𝕥 ∷ µ) 𝕥 → Value µ 𝕥
--     Π       : Value µ 𝕥 → Value (𝕥 ∷ µ) 𝕥 → Value µ 𝕥
--     ★       : Value µ 𝕥
--     neutral : Neutral µ 𝕥 → Value µ 𝕥

𝕟↔𝕥₁ : Modeᵥ → Modeᵥ
𝕟↔𝕥₁ 𝕥 = 𝕟
𝕟↔𝕥₁ 𝕟 = 𝕥

𝕟↔𝕥₁-idem : ∀ m → 𝕟↔𝕥₁ (𝕟↔𝕥₁ m) ≡ m
𝕟↔𝕥₁-idem 𝕥 = refl
𝕟↔𝕥₁-idem 𝕟 = refl

𝕟↔𝕥₁-inj : 𝕟↔𝕥₁ m₁ ≡ 𝕟↔𝕥₁ m₂ → m₁ ≡ m₂
𝕟↔𝕥₁-inj {𝕥} {𝕥} refl = refl
𝕟↔𝕥₁-inj {𝕟} {𝕟} refl = refl

𝕟↔𝕥 : List Modeᵥ → List Modeᵥ
𝕟↔𝕥 [] = []
𝕟↔𝕥 (µ , m) = 𝕟↔𝕥₁ m ∷ 𝕟↔𝕥 µ

𝕟↔𝕥-idem : ∀ µ → 𝕟↔𝕥 (𝕟↔𝕥 µ) ≡ µ
𝕟↔𝕥-idem [] = refl
𝕟↔𝕥-idem (µ , m) = cong₂ _,_ (𝕟↔𝕥-idem µ) (𝕟↔𝕥₁-idem m)

𝕟↔𝕥` : µ ∋ m → 𝕟↔𝕥 µ ∋ 𝕟↔𝕥₁ m
𝕟↔𝕥` (here refl) = here refl
𝕟↔𝕥` (there x) = there (𝕟↔𝕥` x)

𝕟↔𝕥`` : 𝕟↔𝕥 µ ∋ 𝕟↔𝕥₁ m → µ ∋ m
𝕟↔𝕥`` {µ = µ , m} (here px) = here (𝕟↔𝕥₁-inj px)
𝕟↔𝕥`` {µ = µ , m} (there x) = there (𝕟↔𝕥`` x)

mutual
  ⟦_⟧ᵥ : Term (𝕟↔𝕥 µ) 𝕧 → Term µ 𝕥
  ⟦ `[_]_ {𝕥} () x ⟧ᵥ
  ⟦ `[_]_ {𝕟} () x ⟧ᵥ
  ⟦ λ→ᵛ v ⟧ᵥ      = λ→ ⟦ v ⟧ᵥ
  ⟦ Πᵛ τ₁ τ₂ ⟧ᵥ   = Π ⟦ τ₁ ⟧ᵥ ⟦ τ₂ ⟧ᵥ
  ⟦ ★ᵛ ⟧ᵥ         = ★
  ⟦ neutralᵛ n ⟧ᵥ = ⟦ n ⟧ₙ

  ⟦_⟧ₙ : Term (𝕟↔𝕥 µ) 𝕟 → Term µ 𝕥
  ⟦ `[_]_ {𝕟} refl x ⟧ₙ   = ` (𝕟↔𝕥`` x)
  ⟦ n ·ⁿ v ⟧ₙ = ⟦ n ⟧ₙ · ⟦ v ⟧ᵥ

data _⇓_ : Term µ 𝕥 → Term (𝕟↔𝕥 µ) 𝕧 → Set where
  ⇓-λ :
    e ⇓ v →
    λ→ e ⇓ λ→ᵛ v
  ⇓-Π :
    t₁ ⇓ τ₁ →
    t₂ ⇓ τ₂ →
    Π t₁ t₂ ⇓ Πᵛ τ₁ τ₂
  ⇓-` :
    ` x ⇓ neutralᵛ (` 𝕟↔𝕥` x)
  ⇓-·ᵥ : {t₁ : Term (µ , 𝕥) 𝕥} →
    t₁ ⇓ λ→ᵛ v₁ →
    t₂ ⇓ v₂ →
    ⟦ v₁ ⟧ᵥ ⋯ ⦅ ⟦ v₂ ⟧ᵥ ⦆ ⇓ v →
    t₁ · t₂ ⇓ v
  ⇓-·ₙ : {t₁ : Term (µ , 𝕥) 𝕥} →
    t₁ ⇓ neutralᵛ n₁ →
    t₂ ⇓ v₂ →
    t₁ · t₂ ⇓ neutralᵛ (n₁ ·ⁿ v₂)
  ⇓-★ :
    ★ {µ} ⇓ ★ᵛ

-- Typing ----------------------------------------------------------------------

data _⊢_∶_ : Ctx (𝕟↔𝕥 µ) → Term µ 𝕥 → Term (𝕟↔𝕥 µ) 𝕧 → Set where
  τ-` : ∀ {Γ : Ctx (𝕟↔𝕥 µ)} {τ : Term (𝕟↔𝕥 µ) 𝕧} {x : 𝕥 ∈ µ} →
    wk-telescope Γ (𝕟↔𝕥` x) ≡ τ →
    Γ ⊢ ` x ∶ τ
  τ-λ : ∀ {Γ : Ctx (𝕟↔𝕥 µ)} →
    Γ ⊢ t₁ ∶ ★ᵛ →
    t₁ ⇓ τ₁ →
    Γ ,, τ₁ ⊢ e ∶ τ₂ →
    Γ ⊢ λ→ e ∶ Πᵛ τ₁ τ₂
  τ-· : ∀ {Γ : Ctx (𝕟↔𝕥 µ)} →
    Γ ⊢ e₁ ∶ Πᵛ τ₁ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    ⟦ τ₂ ⟧ᵥ ⋯ ⦅ ⟦ τ₁ ⟧ᵥ ⦆ ⇓ τ →
    Γ ⊢ e₁ · e₂ ∶ τ
  τ-Π :
    t₁ ⇓ τ₁ →
    Γ       ⊢ t₁      ∶ ★ᵛ →
    Γ ,, τ₁ ⊢ t₂      ∶ ★ᵛ →
    Γ       ⊢ Π t₁ t₂ ∶ ★ᵛ
  τ-★ :
    Γ ⊢ ★ ∶ ★ᵛ

-- _⊢*_∶_ : Ctx µ₂ → µ₁ →ₛ µ₂ → Ctx µ₁ → Set
-- _⊢*_∶_ {µ₁ = µ₁} Γ₂ σ Γ₁ =
--   (x : µ₁ ∋ 𝕥) → Γ₂ ⊢ σ _ x ∶ (wk-telescope Γ₁ x ⋯ σ)
