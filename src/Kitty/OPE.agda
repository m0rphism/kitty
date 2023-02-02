open import Kitty.Modes
open import Kitty.Kit using (KitTraversal; KitHomotopy)
open import Kitty.Compose using (KitAssoc)
open import Kitty.Types using (KitType)
open KitAssoc using (KitAssocLemmas)

module Kitty.OPE {𝕄 : Modes} {𝕋 : Terms 𝕄} {T : KitTraversal 𝕋} {H : KitHomotopy 𝕋 T} {A : KitAssoc 𝕋 T H} (AL : KitAssocLemmas A) (KT : KitType 𝕋) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Prelude

open Modes 𝕄
open Terms 𝕋
open Kitty.Kit 𝕋
open Kitty.Kit.KitTraversal T
open Kitty.Compose 𝕋 T
open Kitty.Compose.KitAssoc A
open Kitty.Compose.KitAssoc.KitAssocLemmas AL
open Kitty.Types.KitType KT

open Kit {{...}}
open ComposeKit {{...}}

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kitᵣᵣ
private instance _ = kitᵣₛ
private instance _ = kitₛᵣ
private instance _ = kitₛₛ

private
  variable
    Γ Γ₁ Γ₂    : Ctx µ

-- wk-drop : ∀ n → Type (List.drop n µ) m → Type µ m
-- wk-drop              zero    t = t
-- wk-drop {µ = []}     (suc n) t = t -- This case (index > length) cannot happen with drop-∈
-- wk-drop {µ = m' ∷ µ} (suc n) t = wkt (wk-drop n t)

wk-drop-∈ : (x : µ ∋ m) → drop-∈ x µ ⊢ M → µ ⊢ M
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
    OPE (ρ ↑ m) (Γ₁ ▶ T) (Γ₂ ▶ (T ⋯ ρ))
  ope-drop  : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₂ ∶⊢ m→M m} →
    OPE  ρ        Γ₁  Γ₂ →
    OPE (wk ∘ᵣ ρ) Γ₁ (Γ₂ ▶ T)

ope-pres-telescope : ∀ {ρ : µ₁ →ᵣ µ₂} (x : µ₁ ∋ m) →
  OPE ρ Γ₁ Γ₂ →
  wk-telescope Γ₂ (ρ m x) ≡ wk-telescope Γ₁ x ⋯ ρ
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

-- _∋*_∶_ : Ctx µ₂ → µ₁ →ᵣ µ₂ → Ctx µ₁ → Set
-- _∋*_∶_ {µ₁ = µ₁} Γ₂ ρ Γ₁ = ∀ {m} (x : µ₁ ∋ m) → wk-telescope Γ₂ (ρ _ x) ≡ wk-telescope Γ₁ x ⋯ ρ

-- ope-pres-telescope : ∀ {ρ : µ₁ →ᵣ µ₂} →
--   OPE ρ Γ₁ Γ₂ →
--   Γ₂ ∋* ρ ∶ Γ₁
-- ope-pres-telescope ope-id                                     x           = sym (⋯-id _)
-- ope-pres-telescope (ope-keep {ρ = ρ} {T = T} ope)             (here refl) = sym (dist-↑-ren T ρ)
-- ope-pres-telescope (ope-keep {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) (there x)   =
--   wk _ (wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x))) ≡⟨ cong (wk _) (ope-pres-telescope ope x) ⟩
--   wk _ (wk-drop-∈ x (Γ₁ x) ⋯ ρ)         ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
--   wk _ (wk-drop-∈ x (Γ₁ x)) ⋯ ρ ↑ _     ∎
-- ope-pres-telescope (ope-drop {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ope) x           =
--   wk-drop-∈ (ρ _ x) (Γ₂ (ρ _ x)) ⋯ wk ≡⟨ cong (_⋯ wk) (ope-pres-telescope ope x) ⟩
--   wk-drop-∈ x (Γ₁ x) ⋯ ρ         ⋯ wk ≡⟨ ⋯-assoc (wk-drop-∈ x (Γ₁ x)) ρ wk ⟩
--   wk-drop-∈ x (Γ₁ x) ⋯ wk ∘ᵣ ρ        ∎

-- ∋*-id : ∀ {Γ : Ctx µ} →
--   Γ ∋* idᵣ ∶ Γ
-- ∋*-id {Γ = Γ} x =
--   wk-telescope Γ (idᵣ _ x) ≡⟨⟩
--   wk-telescope Γ x         ≡⟨ sym (⋯-id _) ⟩
--   wk-telescope Γ x ⋯ idᵣ   ∎

-- ∋*-keep : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₁ ∶⊢ m→M m} →
--    Γ₂            ∋*  ρ      ∶  Γ₁ →
--   (Γ₂ ▶ (T ⋯ ρ)) ∋* (ρ ↑ m) ∶ (Γ₁ ▶ T)
-- ∋*-keep {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* (here refl) =
--   wk-telescope (Γ₂ ▶ (T ⋯ ρ)) ((ρ ↑ _) _ (here refl)) ≡⟨⟩
--   T ⋯ ρ ⋯ wk                                          ≡⟨ sym (dist-↑-ren T ρ) ⟩
--   T ⋯ wk ⋯ (ρ ↑ _)                                    ≡⟨⟩
--   wk-telescope (Γ₁ ▶ T) (here refl) ⋯ ρ ↑ _           ∎
-- ∋*-keep {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* (there x) =
--   wk-telescope (Γ₂ ▶ (T ⋯ ρ)) ((ρ ↑ _) _ (there x)) ≡⟨⟩
--   wk-telescope Γ₂ (ρ _ x) ⋯ wk                      ≡⟨ cong (_⋯ wk) (∋* x) ⟩
--   wk-telescope Γ₁ x ⋯ ρ ⋯ wk                        ≡⟨ sym (dist-↑-ren (wk-drop-∈ x (Γ₁ x)) ρ) ⟩
--   wk-telescope Γ₁ x ⋯ wk ⋯ ρ ↑ _                    ≡⟨⟩
--   wk-telescope (Γ₁ ▶ T) (there x) ⋯ ρ ↑ _           ∎

-- ∋*-drop : ∀ {ρ : µ₁ →ᵣ µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {T : µ₂ ∶⊢ m→M m} →
--    Γ₂      ∋*  ρ        ∶ Γ₁ →
--   (Γ₂ ▶ T) ∋* (wk ∘ᵣ ρ) ∶ Γ₁
-- ∋*-drop {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* x =
--   wk-telescope (Γ₂ ▶ T) ((wk ∘ᵣ ρ) _ x)       ≡⟨⟩
--   wk-telescope (Γ₂ ▶ T) (((ρ ↑ _) ∘ᵣ wk) _ x) ≡⟨⟩
--   wk-telescope Γ₂ (ρ _ x) ⋯ wk                ≡⟨ cong (_⋯ wk) (∋* x) ⟩
--   wk-telescope Γ₁ x ⋯ ρ ⋯ wk                  ≡⟨ ⋯-assoc (wk-telescope Γ₁ x) ρ wk ⟩
--   wk-telescope Γ₁ x ⋯ wk ∘ᵣ ρ                 ∎
