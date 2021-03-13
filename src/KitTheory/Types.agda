open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

module KitTheory.Types
    (VarKind  : Set)
    (TermKind : Set)
    (k→K      : VarKind → TermKind)
    (_⊢_      : List VarKind → TermKind → Set)
    (`_       : ∀ {κ k} → k ∈ κ → κ ⊢ k→K k)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

open import KitTheory.Kit           VarKind TermKind k→K _⊢_ `_
open import KitTheory.Compose       VarKind TermKind k→K _⊢_ `_
open import KitTheory.ComposeLemmas VarKind TermKind k→K _⊢_ `_

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
    k k' k₁ k₂    : VarKind
    κ κ' κ₁ κ₂ κ₃ : List VarKind
    K K' K₁ K₂    : TermKind
    x y z         : k ∈ κ
    ℓ ℓ₃          : Level
    A B C         : Set ℓ

record KitType : Set₁ where
  field
    -- {{term-traversal}} : KitTraversal
    {{kit-assoc-lemmas}} : KitAssocLemmas
    ↑ₜ : TermKind → TermKind

  _∶⊢_ : List VarKind → TermKind → Set
  κ ∶⊢ K = κ ⊢ ↑ₜ K

  depth : ∀ {x : A} {xs : List A} → x ∈ xs → ℕ
  depth (here px) = zero
  depth (there x) = suc (depth x)

  -- We need to drop one extra using `suc`, because otherwise the types in a
  -- context are allowed to use themselves.
  drop-∈ : ∀ {x : A} {xs : List A} → x ∈ xs → List A → List A
  drop-∈ = drop ∘ suc ∘ depth

  Ctx : List VarKind → Set
  Ctx κ = ∀ {k} → (x : κ ∋ k) → drop-∈ x κ ∶⊢ k→K k

  private variable Γ Γ₁ Γ₂ : Ctx κ

  infixl  5  _,,_

  _,,_ : Ctx κ → κ ∶⊢ k→K k → Ctx (k ∷ κ)
  (Γ ,, t) (here refl) = t
  (Γ ,, t) (there x) = Γ x

  -- wk-drop : ∀ n → Type (List.drop n κ) k → Type κ k
  -- wk-drop              zero    t = t
  -- wk-drop {κ = []}     (suc n) t = t -- This case (index > length) cannot happen with drop-∈
  -- wk-drop {κ = k' ∷ κ} (suc n) t = wkt (wk-drop n t)

  wk-drop-∈ : (x : κ ∋ k) → drop-∈ x κ ∶⊢ k→K k → κ ∶⊢ k→K k
  wk-drop-∈ (here _)  t = wk _ t
  wk-drop-∈ (there x) t = wk _ (wk-drop-∈ x t)

  -- Our context is defined as a telescope.
  -- This function automatically weakens all the types in a `Ctx κ` such that they
  -- refer to `κ` instead of a `κ`-suffix.
  wk-telescope : Ctx κ → κ ∋ k → κ ∶⊢ k→K k
  wk-telescope Γ x = wk-drop-∈ x (Γ x)

  -- Order Preserving Embeddings for Contexts. Required by wk-⊢', where we can't
  -- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
  -- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
  -- constructor).
  -- Also arbitrary renamings would allow swapping types in the context which
  -- could violate the telescoping (I think).
  data OPE : κ₁ →ᵣ κ₂ → Ctx κ₁ → Ctx κ₂ → Set where
    ope-id : ∀ {Γ : Ctx κ} →
      OPE idᵣ Γ Γ
    ope-keep  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : κ₁ ∶⊢ k→K k} →
      OPE  ρ       Γ₁        Γ₂ →
      OPE (ρ ↑ k) (Γ₁ ,, T) (Γ₂ ,, (T ⋯ ρ))
    ope-drop  : ∀ {ρ : κ₁ →ᵣ κ₂} {Γ₁ : Ctx κ₁} {Γ₂ : Ctx κ₂} {T : κ₂ ∶⊢ k→K k} →
      OPE  ρ        Γ₁  Γ₂ →
      OPE (wk ∘ᵣ ρ) Γ₁ (Γ₂ ,, T)

  ope-pres-telescope : ∀ {ρ : κ₁ →ᵣ κ₂} (x : κ₁ ∋ k) →
    OPE ρ Γ₁ Γ₂ →
    wk-drop-∈ (ρ k x) (Γ₂ (ρ k x)) ≡ wk-drop-∈ x (Γ₁ x) ⋯ ρ
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
