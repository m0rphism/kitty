open import KitTheory.Modes
open import KitTheory.Kit using (KitTraversal)
open import KitTheory.Compose using (KitAssoc)
open KitAssoc using (KitAssocLemmas)

module KitTheory.Types {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) (A : KitAssoc 𝕋 T) (AL : KitAssocLemmas A) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import KitTheory.Prelude

open Modes 𝕄
open Terms 𝕋
open KitTheory.Kit 𝕋
open KitTheory.Kit.KitTraversal T
open KitTheory.Compose 𝕋 T
open KitTheory.Compose.KitAssoc A
open KitTheory.Compose.KitAssoc.KitAssocLemmas AL

open Kit {{...}}
open ComposeKit {{...}}

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level

record KitType : Set₁ where
  private instance _ = kitᵣ
  private instance _ = kitₛ
  private instance _ = kitᵣᵣ
  private instance _ = kitᵣₛ
  private instance _ = kitₛᵣ
  private instance _ = kitₛₛ

  field
    ↑ₜ : TermMode → TermMode

  infix  3  _∶⊢_

  _∶⊢_ : List VarMode → TermMode → Set
  µ ∶⊢ M = µ ⊢ ↑ₜ M

  depth : ∀ {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
  depth (here px) = zero
  depth (there x) = suc (depth x)

  -- We need to drop one extra using `suc`, because otherwise the types in a
  -- context are allowed to use themselves.
  drop-∈ : ∀ {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
  drop-∈ = drop ∘ suc ∘ depth

  Ctx : List VarMode → Set
  Ctx µ = ∀ {m} → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m→M m

  ∅ : Ctx []
  ∅ ()

  private
    variable
      Γ Γ₁ Γ₂    : Ctx µ

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
