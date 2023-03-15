open import Kitty.Term.Modes
open import Kitty.Term.Sub
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.Types using (KitType)

module Kitty.Typing.OPE {𝕄 : Modes} {𝕋 : Terms 𝕄} {𝕊 : SubWithLaws 𝕋} {T : Traversal 𝕋 𝕊} {H : KitHomotopy 𝕋 𝕊 T}
                        {𝕊C : SubCompose 𝕋 𝕊 T H} {C : ComposeTraversal 𝕋 𝕊 T H 𝕊C} (KT : KitType 𝕋) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude

open Modes 𝕄
open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open Kitty.Term.Traversal.Traversal T
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open Kitty.Term.ComposeTraversal.ComposeTraversal C
open Kitty.Typing.Types.KitType KT

open Kit ⦃ … ⦄
open KitT ⦃ … ⦄
open ComposeKit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄
open SubCompose ⦃ … ⦄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ ℓ₁ ℓ₂ : Level

private instance _ = kitᵣ
private instance _ = kitₛ
private instance _ = kittᵣ
private instance _ = kittₛ
private instance _ = ckitᵣ
private instance _ = ckitₛᵣ
private instance _ = ckitₛₛ
private instance _ = 𝕊
private instance _ = 𝕊C

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

infix   4  _∋_∶_
_∋_∶_ : Ctx µ → µ ∋ m → µ ∶⊢ m→M m → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

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
    OPE (ρ ·ₖ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) Γ₁ (Γ₂ ▶ T)

ope-pres-telescope : ∀ {µ₁} {µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ρ : µ₁ →ᵣ µ₂} {m} (x : µ₁ ∋ m) →
  OPE ρ Γ₁ Γ₂ →
  wk-telescope Γ₂ (x & ρ) ≡ wk-telescope Γ₁ x ⋯ ρ
ope-pres-telescope {µ₁} {µ₂} {Γ₁} {Γ₂} {ρ} {m} x ope-id =
  wk-telescope Γ₁ (x & idᵣ) ≡⟨ cong (wk-telescope Γ₁) (&-id x) ⟩
  wk-telescope Γ₁ x         ≡⟨ sym (⋯-id (wk-telescope Γ₁ x)) ⟩
  wk-telescope Γ₁ x ⋯ idᵣ   ∎
ope-pres-telescope {µ₁} {µ₂} {Γ₁} {Γ₂} {ρ} {m} x@(here refl) (ope-keep {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ T ⋯ ρ') (x & ρ' ↑ m) ≡⟨ cong (wk-telescope (Γ₂' ▶ T ⋯ ρ')) (&-↑-here ρ') ⟩
  wk-telescope (Γ₂' ▶ T ⋯ ρ') (here refl)  ≡⟨⟩
  wk _ (T ⋯ ρ')                            ≡⟨ sym (dist-↑-f T ρ') ⟩
  wk _ T ⋯ (ρ' ↑ m)                        ≡⟨⟩
  wk-telescope (Γ₁' ▶ T) x ⋯ (ρ' ↑ m)      ∎
ope-pres-telescope {µ₁} {µ₂} {Γ₁} {Γ₂} {ρ} {m} x@(there y)   (ope-keep {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ T ⋯ ρ') (x & ρ' ↑ _)     ≡⟨ cong (wk-telescope (Γ₂' ▶ T ⋯ ρ')) (&-↑-there ρ' y) ⟩
  wk-telescope (Γ₂' ▶ T ⋯ ρ') (there (y & ρ')) ≡⟨⟩
  wk _ (wk-telescope Γ₂' (y & ρ'))             ≡⟨ cong (wk _) (ope-pres-telescope y ope) ⟩
  wk _ (wk-telescope Γ₁' y ⋯ ρ')               ≡⟨ sym (dist-↑-f (wk-telescope Γ₁' y) ρ') ⟩
  wk _ (wk-telescope Γ₁' y) ⋯ (ρ' ↑ _)         ≡⟨⟩
  wk-telescope (Γ₁' ▶ T) x ⋯ (ρ' ↑ _)          ∎
ope-pres-telescope {µ₁} {µ₂} {Γ₁} {Γ₂} {ρ} {m} x           (ope-drop {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ T) (x & (ρ' ·ₖ wkₖ _ id))     ≡⟨ cong (wk-telescope (Γ₂' ▶ T)) (&-·ₖ-&/⋯ ρ' (wkₖ _ id) x) ⟩
  wk-telescope (Γ₂' ▶ T) ((x & ρ') & wkₖ _ id)      ≡⟨ cong (wk-telescope (Γ₂' ▶ T)) (&-wkₖ-wk id (x & ρ')) ⟩
  wk-telescope (Γ₂' ▶ T) (there (x & ρ' & id))      ≡⟨ cong (λ ■ → wk-telescope (Γ₂' ▶ T) (there ■)) (&-id (x & ρ')) ⟩
  wk-telescope (Γ₂' ▶ T) (there (x & ρ'))           ≡⟨⟩
  wk _ (wk-telescope Γ₂' (x & ρ'))                  ≡⟨⟩
  wk-telescope Γ₂' (x & ρ') ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨ cong (_⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) (ope-pres-telescope x ope) ⟩
  wk-telescope Γ₁ x ⋯ ρ' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id    ≡⟨ ⋯-assoc (wk-telescope Γ₁ x) ρ' (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) ⟩
  wk-telescope Γ₁ x ⋯ (ρ' ·ₖ wkₖ _ id)              ∎

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
