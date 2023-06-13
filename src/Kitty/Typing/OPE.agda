open import Kitty.Term.Terms
open import Kitty.Term.Sub
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)
open import Kitty.Typing.TypeSorts using (TypeSorts)
open import Kitty.Typing.CtxRepr using (CtxRepr)

module Kitty.Typing.OPE
  {𝕋 : Terms}
  {ℓ}
  {𝕊 : SubWithLaws 𝕋 ℓ}
  {T  : Traversal 𝕋 𝕊}
  {H  : KitHomotopy T}
  {𝕊C : SubCompose H}
  (C  : ComposeTraversal 𝕊C)
  {TM : TypeSorts 𝕋}
  (ℂ  : CtxRepr TM)
  where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Kitty.Term.Prelude
open import Kitty.Util.List

open Terms 𝕋
open import Kitty.Term.Kit 𝕋
open Kitty.Term.Traversal.Traversal T
open import Kitty.Term.KitT T
open import Kitty.Term.ComposeKit H
open Kitty.Term.ComposeTraversal.ComposeTraversal C
open Kitty.Typing.TypeSorts.TypeSorts TM

open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open Kit ⦃ … ⦄
open KitT ⦃ … ⦄
open ComposeKit ⦃ … ⦄
open SubCompose 𝕊C
open CtxRepr ℂ

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx
    ℓ₁ ℓ₂ : Level

private instance _ = Kᵣ
private instance _ = Kₛ
private instance _ = Wᵣ
private instance _ = Wₛ
private instance _ = Cᵣ
private instance _ = Cₛᵣ
private instance _ = Cₛₛ
private instance _ = 𝕊
private instance _ = 𝕊C

private
  variable
    Γ Γ₁ Γ₂    : Ctx S

-- wk-drop : ∀ n → Type (List.drop n S) s → Type S s
-- wk-drop              zero    t = t
-- wk-drop {S = []}     (suc n) t = t -- This case (index > length) cannot happen with drop-∈
-- wk-drop {S = s' ∷ S} (suc n) t = wkt (wk-drop n t)

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s' → S ⊢ s'
wk-drop-∈ (here _)  t = t ⋯ wknᵣ
wk-drop-∈ (there x) t = wk-drop-∈ x t ⋯ wknᵣ

-- Our context is defined as a telescope.
-- This function automatically weakens all the types in a `Ctx S` such that they
-- refer to `S` instead of a `S`-suffix.
wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (lookup Γ x)

infix   4  _∋_∶_
_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

wk-telescope-here : ∀ {S s} (Γ : Ctx S) (T : S ∶⊢ s) →
  wk-telescope (Γ ▶ T) (here refl) ≡ T ⋯ wknᵣ
wk-telescope-here {S} {s} Γ T =
  wk-telescope (Γ ▶ T) (here refl)  ≡⟨⟩
  lookup (Γ ▶ T) (here refl) ⋯ wknᵣ ≡⟨ cong (_⋯ wknᵣ) (lookup-▶-here Γ T) ⟩
  T ⋯ wknᵣ                          ∎

wk-telescope-there : ∀ {S s sx} (Γ : Ctx S) (T : S ∶⊢ s) (x : S ∋ sx) →
  wk-telescope (Γ ▶ T) (there x) ≡ wk-telescope Γ x ⋯ wknᵣ
wk-telescope-there {S} {s} {sx} Γ T x =
  wk-telescope (Γ ▶ T) (there x)                ≡⟨⟩
  wk-drop-∈ x (lookup (Γ ▶ T) (there x)) ⋯ wknᵣ ≡⟨ cong (λ ■ → wk-drop-∈ x ■ ⋯ wknᵣ) (lookup-▶-there Γ T x) ⟩
  wk-drop-∈ x (lookup Γ x) ⋯ wknᵣ               ≡⟨⟩
  wk-telescope Γ x ⋯ wknᵣ                       ∎

wk-telescope-there' : ∀ {S s sx} (Γ : Ctx (S ▷ s)) (x : S ∋ sx) →
  wk-telescope Γ (there x) ≡ wk-telescope (Γ ↓ᶜ) x ⋯ wknᵣ
wk-telescope-there' {S} {s} {sx} Γ x =
  wk-telescope Γ (there x)                ≡⟨⟩
  wk-drop-∈ x (lookup Γ (there x)) ⋯ wknᵣ ≡⟨ cong (λ ■ → wk-drop-∈ x ■ ⋯ wknᵣ) (sym (lookup-↓ᶜ Γ x)) ⟩
  wk-drop-∈ x (lookup (Γ ↓ᶜ) x) ⋯ wknᵣ    ≡⟨⟩
  wk-telescope (Γ ↓ᶜ) x ⋯ wknᵣ            ∎

-- Order Preserving Embeddings for Contexts. Required by wk-⊢', where we can't
-- just say Γ₂ ≡ Γ₁ ⋯* ρ because weakenings in ρ require us to fill the gaps
-- between the weakened Γ₁ types with new Γ₂ types (the `T` in the `ope-drop`
-- constructor).
-- Also arbitrary renamings would allow swapping types in the context which
-- could violate the telescoping (I think).
data OPE : S₁ →ᵣ S₂ → Ctx S₁ → Ctx S₂ → Set ℓ where
  ope-id : ∀ {Γ : Ctx S} →
    OPE idᵣ Γ Γ
  ope-keep  : ∀ {ρ : S₁ →ᵣ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : S₁ ∶⊢ s} →
    OPE  ρ       Γ₁        Γ₂ →
    OPE (ρ ↑ s) (Γ₁ ▶ T) (Γ₂ ▶ (T ⋯ ρ))
  ope-drop  : ∀ {ρ : S₁ →ᵣ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : S₂ ∶⊢ s} →
    OPE  ρ        Γ₁  Γ₂ →
    OPE (ρ ·ₖ wkₖ ⦃ K = Kᵣ ⦄ _ id) Γ₁ (Γ₂ ▶ T)

ope-pres-telescope : ∀ {S₁} {S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ρ : S₁ →ᵣ S₂} {s} (x : S₁ ∋ s) →
  OPE ρ Γ₁ Γ₂ →
  wk-telescope Γ₂ (x & ρ) ≡ wk-telescope Γ₁ x ⋯ ρ
ope-pres-telescope {S₁} {S₂} {Γ₁} {Γ₂} {ρ} {s} x ope-id =
  wk-telescope Γ₁ (x & idᵣ) ≡⟨ cong (wk-telescope Γ₁) (&-id x) ⟩
  wk-telescope Γ₁ x         ≡⟨ sym (⋯-id (wk-telescope Γ₁ x)) ⟩
  wk-telescope Γ₁ x ⋯ idᵣ   ∎
ope-pres-telescope {S₁} {S₂} {Γ₁} {Γ₂} {ρ} {s} x@(here refl) (ope-keep {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ (T ⋯ ρ')) (x & ρ' ↑ s) ≡⟨ cong (wk-telescope (Γ₂' ▶ (T ⋯ ρ'))) (&-↑-here ρ') ⟩
  wk-telescope (Γ₂' ▶ (T ⋯ ρ')) (here refl)  ≡⟨ wk-telescope-here Γ₂' (T ⋯ ρ') ⟩
  T ⋯ ρ' ⋯ wknᵣ                              ≡⟨ sym (dist-↑-f T ρ') ⟩
  T ⋯ wknᵣ ⋯ (ρ' ↑ s)                        ≡⟨ cong (_⋯ (ρ' ↑ s)) (sym (wk-telescope-here Γ₁' T)) ⟩
  wk-telescope (Γ₁' ▶ T) x ⋯ (ρ' ↑ s)        ∎
ope-pres-telescope {S₁} {S₂} {Γ₁} {Γ₂} {ρ} {s} x@(there y)   (ope-keep {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ (T ⋯ ρ')) (x & ρ' ↑ _)     ≡⟨ cong (wk-telescope (Γ₂' ▶ (T ⋯ ρ'))) (&-↑-there ρ' y) ⟩
  wk-telescope (Γ₂' ▶ (T ⋯ ρ')) (there (y & ρ')) ≡⟨ wk-telescope-there Γ₂' (T ⋯ ρ') (y & ρ') ⟩
  wk-telescope Γ₂' (y & ρ') ⋯ wknᵣ             ≡⟨ cong (_⋯ wknᵣ) (ope-pres-telescope y ope) ⟩
  wk-telescope Γ₁' y ⋯ ρ' ⋯ wknᵣ               ≡⟨ sym (dist-↑-f (wk-telescope Γ₁' y) ρ') ⟩
  wk-telescope Γ₁' y ⋯ wknᵣ ⋯ (ρ' ↑ _)         ≡⟨ cong (_⋯ ρ' ↑ _) (sym (wk-telescope-there Γ₁' T y)) ⟩
  wk-telescope (Γ₁' ▶ T) x ⋯ (ρ' ↑ _)          ∎
ope-pres-telescope {S₁} {S₂} {Γ₁} {Γ₂} {ρ} {s} x           (ope-drop {ρ = ρ'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {T = T} ope) =
  wk-telescope (Γ₂' ▶ T) (x & (ρ' ·ₖ wkₖ _ id))     ≡⟨ cong (wk-telescope (Γ₂' ▶ T)) (&-·ₖ-&/⋯ ρ' (wkₖ _ id) x) ⟩
  wk-telescope (Γ₂' ▶ T) ((x & ρ') & wkₖ _ id)      ≡⟨ cong (wk-telescope (Γ₂' ▶ T)) (&-wkₖ-wk id (x & ρ')) ⟩
  wk-telescope (Γ₂' ▶ T) (there (x & ρ' & id))      ≡⟨ cong (λ ■ → wk-telescope (Γ₂' ▶ T) (there ■)) (&-id (x & ρ')) ⟩
  wk-telescope (Γ₂' ▶ T) (there (x & ρ'))           ≡⟨ wk-telescope-there Γ₂' T (x & ρ') ⟩
  wk-telescope Γ₂' (x & ρ') ⋯ wknᵣ                  ≡⟨⟩
  wk-telescope Γ₂' (x & ρ') ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ≡⟨ cong (_⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id) (ope-pres-telescope x ope) ⟩
  wk-telescope Γ₁ x ⋯ ρ' ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id    ≡⟨ ⋯-assoc (wk-telescope Γ₁ x) ρ' (wkₖ ⦃ K = Kᵣ ⦄ _ id) ⟩
  wk-telescope Γ₁ x ⋯ (ρ' ·ₖ wkₖ _ id)              ∎

-- _∋*_∶_ : Ctx S₂ → S₁ →ᵣ S₂ → Ctx S₁ → Set
-- _∋*_∶_ {S₁ = S₁} Γ₂ ρ Γ₁ = ∀ {s} (x : S₁ ∋ s) → wk-telescope Γ₂ (x & ρ) ≡ wk-telescope Γ₁ x ⋯ ρ

-- ope-pres-telescope : ∀ {ρ : S₁ →ᵣ S₂} →
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

-- ∋*-id : ∀ {Γ : Ctx S} →
--   Γ ∋* idᵣ ∶ Γ
-- ∋*-id {Γ = Γ} x =
--   wk-telescope Γ (idᵣ _ x) ≡⟨⟩
--   wk-telescope Γ x         ≡⟨ sym (⋯-id _) ⟩
--   wk-telescope Γ x ⋯ idᵣ   ∎

-- ∋*-keep : ∀ {ρ : S₁ →ᵣ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : S₁ ∶⊢ s} →
--    Γ₂            ∋*  ρ      ∶  Γ₁ →
--   (Γ₂ ▶ (T ⋯ ρ)) ∋* (ρ ↑ s) ∶ (Γ₁ ▶ T)
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

-- ∋*-drop : ∀ {ρ : S₁ →ᵣ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : S₂ ∶⊢ s} →
--    Γ₂      ∋*  ρ        ∶ Γ₁ →
--   (Γ₂ ▶ T) ∋* (wk ∘ᵣ ρ) ∶ Γ₁
-- ∋*-drop {ρ = ρ} {Γ₁} {Γ₂} {T} ∋* x =
--   wk-telescope (Γ₂ ▶ T) ((wk ∘ᵣ ρ) _ x)       ≡⟨⟩
--   wk-telescope (Γ₂ ▶ T) (((ρ ↑ _) ∘ᵣ wk) _ x) ≡⟨⟩
--   wk-telescope Γ₂ (ρ _ x) ⋯ wk                ≡⟨ cong (_⋯ wk) (∋* x) ⟩
--   wk-telescope Γ₁ x ⋯ ρ ⋯ wk                  ≡⟨ ⋯-assoc (wk-telescope Γ₁ x) ρ wk ⟩
--   wk-telescope Γ₁ x ⋯ wk ∘ᵣ ρ                 ∎
