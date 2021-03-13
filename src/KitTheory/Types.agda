open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Types
    (VarMode  : Set)
    (TermMode : Set)
    (m→M      : VarMode → TermMode)
    (_⊢_      : List VarMode → TermMode → Set)
    (`_       : ∀ {µ m} → m ∈ µ → µ ⊢ m→M m)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

open import KitTheory.Kit           VarMode TermMode m→M _⊢_ `_
open import KitTheory.Compose       VarMode TermMode m→M _⊢_ `_
open import KitTheory.ComposeLemmas VarMode TermMode m→M _⊢_ `_

open Kit {{...}}
open KitTraversal {{...}}
open ComposeKit {{...}}
open KitAssoc {{...}}
open KitAssocLemmas {{...}}

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kitᵣᵣ
private instance _ = kitᵣₛ
private instance _ = kitₛᵣ
private instance _ = kitₛₛ

private
  variable
    m m' m₁ m₂    : VarMode
    µ µ' µ₁ µ₂ µ₃ : List VarMode
    M M' M₁ M₂    : TermMode
    x y z         : m ∈ µ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

record KitType : Set₁ where
  field
    -- {{term-traversal}} : KitTraversal
    {{kit-assoc-lemmas}} : KitAssocLemmas
    ↑ₜ : TermMode → TermMode

  _∶⊢_ : List VarMode → TermMode → Set
  µ ∶⊢ M = µ ⊢ ↑ₜ M

  depth : ∀ {x : A} {xs : List A} → x ∈ xs → ℕ
  depth (here px) = zero
  depth (there x) = suc (depth x)

  -- We need to drop one extra using `suc`, because otherwise the types in a
  -- context are allowed to use themselves.
  drop-∈ : ∀ {x : A} {xs : List A} → x ∈ xs → List A → List A
  drop-∈ = drop ∘ suc ∘ depth

  Ctx : List VarMode → Set
  Ctx µ = ∀ {m} → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m

  private variable Γ Γ₁ Γ₂ : Ctx µ

  infixl  5  _,,_

  _,,_ : Ctx µ → µ ∶⊢ m→M m → Ctx (m ∷ µ)
  (Γ ,, t) (here refl) = t
  (Γ ,, t) (there x) = Γ x

  -- wk-drop : ∀ n → Type (List.drop n µ) m → Type µ m
  -- wk-drop              zero    t = t
  -- wk-drop {µ = []}     (suc n) t = t -- This case (index > length) cannot happen with drop-∈
  -- wk-drop {µ = m' ∷ µ} (suc n) t = wkt (wk-drop n t)

  wk-drop-∈ : (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m → µ ∶⊢ m→M m
  wk-drop-∈ (here _)  t = wk _ t
  wk-drop-∈ (there x) t = wk _ (wk-drop-∈ x t)

  -- Our context is defined as a telescope.
  -- This function automatically weakens all the types in a `Ctx µ` such that they
  -- refer to `µ` instead of a `µ`-suffix.
  wk-telescope : Ctx µ → µ ∋ m → µ ∶⊢ m→M m
  wk-telescope Γ x = wk-drop-∈ x (Γ x)

  -- Order Preserving Embeddings for Contexts. Required by wk-⊢', where we can't
  -- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
  -- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
  -- constructor).
  -- Also arbitrary renamings would allow swapping types in the context which
  -- could violate the telescoping (I think).
  data OPE : µ₁ →ᵣ µ₂ → Ctx µ₁ → Ctx µ₂ → Set where
    ope-id : ∀ {Γ : Ctx µ} →
      OPE idᵣ Γ Γ
    ope-keep  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₁ ∶⊢ m→M m} →
      OPE  ρ       Γ₁        Γ₂ →
      OPE (ρ ↑ m) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ ρ))
    ope-drop  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₂ ∶⊢ m→M m} →
      OPE  ρ        Γ₁  Γ₂ →
      OPE (wk ∘ᵣ ρ) Γ₁ (Γ₂ ,, T)

  ope-pres-telescope : ∀ {ρ : µ₁ →ᵣ µ₂} (x : µ₁ ∋ m) →
    OPE ρ Γ₁ Γ₂ →
    wk-drop-∈ (ρ m x) (Γ₂ (ρ m x)) ≡ wk-drop-∈ x (Γ₁ x) ⋯ ρ
  ope-pres-telescope x           ope-id = sym (⋯-id _)
  ope-pres-telescope (here refl) (ope-keep {ρ = ρ} {T = T} ope) = sym (dist-↑-ren T ρ)
  ope-pres-telescope (there x)   (ope-keep {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
    wk _ (wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x))) ≡⟨ cong (wk _) (ope-pres-telescope x ope) ⟩
    wk _ (wk-drop-∈ x (Γ₁ x) ⋯ ρ)         ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
    wk _ (wk-drop-∈ x (Γ₁ x)) ⋯ ρ ↑ _     ∎
  ope-pres-telescope x           (ope-drop {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) =
    wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk ≡⟨ cong (_⋯ wk) (ope-pres-telescope x ope) ⟩
    wk-drop-∈ x (Γ₁ x) ⋯ ρ         ⋯ wk ≡⟨ ⋯-assoc (wk-drop-∈ x (Γ₁ x)) ρ wk ⟩
    wk-drop-∈ x (Γ₁ x) ⋯ wk ∘ᵣ ρ        ∎
