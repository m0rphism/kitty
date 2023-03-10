open import Kitty.Term.Modes

-- Version of KitAlt with a simpler KitTraversal.⋯-↑ field.

module Kitty.Term.KitAltSimple {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.MultiSub 𝕋
open import Kitty.Term.Prelude
open import Kitty.Term.Sub 𝕋
open import Kitty.Term.Traversal 𝕋
open import Kitty.Util.Star

open Modes 𝕄
open Terms 𝕋
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄
open _⊑ₖ_ ⦃ … ⦄

open import Kitty.Util.SubstProperties

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Alternative KitTraversal ----------------------------------------------------

record KitTraversalAlt : Set₁ where
  constructor mkKitTraversalAlt
  infixl  5  _⋯_

  field
    _⋯_   : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄ →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

  open TraversalOps _⋯_ public

  field
    ⋯-var : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : SubWithLaws ⦄ (x : µ₁ ∋ m) (f : µ₁ –[ 𝕂 ]→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} ⦃ 𝕊 : SubWithLaws ⦄ {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s₁ ]→* µ₂) (gs : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → fs ≈ₓ gs
          → fs ≈ₜ gs

  ~-cong-⋯ :
    ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : SubWithLaws ⦄ {f g : µ₁ –[ 𝕂 ]→ µ₂} (t : µ₁ ⊢ M)
    → f ~ g
    → t ⋯ f ≡ t ⋯ g
  ~-cong-⋯ {µ₁} {µ₂} {M} ⦃ 𝕂 ⦄ ⦃ 𝕊 ⦄ {f} {g} t f~g =
    ⋯-↑ (f ∷ [])
        (g ∷ [])
        (λ {µ} x →
          begin
            (` x) ⋯ f ↑*' µ
          ≡⟨ ⋯-var x (f ↑*' µ) ⟩
            `/id (x & (f ↑*' µ))
          ≡⟨ ~-cong-↑*'' f~g _ x ⟩
            `/id (x & (g ↑*' µ))
          ≡⟨ sym (⋯-var x (g ↑*' µ)) ⟩
            (` x) ⋯ g ↑*' µ 
          ∎)
        t

  -- ↑**-[] : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) (t : µ₁ ⊢ M)
  --       → t ⋯* fs ↑** [] ≡ t ⋯* fs
  -- ↑**-[] [] t =
  --   t ⋯* [] ↑** [] ≡⟨⟩
  --   t ⋯* []        ∎
  -- ↑**-[] {𝕂s = 𝕂 ∷ 𝕂s} (f ∷ fs) t =
  --   let instance _ = 𝕂 in
  --   t ⋯* (f ∷ fs) ↑** []     ≡⟨⟩
  --   t ⋯* fs ↑** [] ⋯ f ↑* [] ≡⟨ cong (_⋯ f ↑* []) (↑**-[] fs t) ⟩
  --   t ⋯* fs ⋯ f ↑* []        ≡⟨ ~-cong-⋯ _ (↑*-[] f) ⟩
  --   t ⋯* fs ⋯ f              ≡⟨⟩
  --   t ⋯* (f ∷ fs)            ∎

  -- ⋯-↑-[] : ∀ {𝕂s₁ 𝕂s₂ : List Kit} ⦃ 𝕊 : SubWithLaws ⦄ {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s₁ ]→* µ₂) (gs : µ₁ –[ 𝕂s₂ ]→* µ₂)
  --          → fs ≈ₓ gs
  --          → ∀ {M} (t : µ₁ ⊢ M) → t ⋯* fs ≡ t ⋯* gs
  -- ⋯-↑-[] {𝕂s₁} {𝕂s₂} ⦃ 𝕊 ⦄ {µ₁} {µ₂} fs gs fs≈ₓgs {M} t =
  --   t ⋯* fs        ≡⟨ {!↑**-[]!} ⟩
  --   t ⋯* fs ↑** [] ≡⟨ ⋯-↑ fs gs fs≈ₓgs t ⟩
  --   t ⋯* gs ↑** [] ≡⟨ {!!} ⟩
  --   t ⋯* gs        ∎

-- Deriving KitTraversal, KitAssoc, and KitAssocLemmas -------------------------

module Derive (KT : KitTraversalAlt) where
  terms : Terms 𝕄
  terms = 𝕋

  open KitTraversalAlt KT public

  private
    ⋯-id' : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : SubWithLaws ⦄ {µ M} (v : µ ⊢ M) → v ⋯ id ⦃ 𝕂 = 𝕂 ⦄ ≡ v
    ⋯-id' ⦃ 𝕂 ⦄ {µ} {M} v =
      ⋯-↑ {µ₁ = µ} (id ∷[ 𝕂 ] [])
          []
          (λ {µ} x →
            ` x ⋯ id ⦃ 𝕂 = 𝕂 ⦄ ↑*' µ        ≡⟨ ⋯-var x (id ↑*' µ) ⟩
            `/id (x & (id ⦃ 𝕂 = 𝕂 ⦄ ↑*' µ)) ≡⟨ ↑*'~↑* µ _ x ⟩
            `/id (x & (id ⦃ 𝕂 = 𝕂 ⦄ ↑* µ))  ≡⟨ id↑*~id µ _ _ x ⟩
            `/id (x & (id ⦃ 𝕂 = 𝕂 ⦄))       ≡⟨ cong `/id (&-id x) ⟩
            `/id (id/` x)                   ≡⟨ id/`/id x ⟩
            ` x                             ∎)
          v

  -- This needs to be another Axiom or a corrolary of ⋯-assoc
  ⋯-x/t-wk' : ∀ ⦃ 𝕂 𝕂' : Kit ⦄ ⦃ 𝕊 : SubWithLaws ⦄ {m'} {m/M : VarMode/TermMode ⦃ 𝕂 ⦄} (x/t : µ₁ ∋/⊢ m/M)
              → (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂' ⦄ _ id) ≡ `/id' (wk m' x/t)
  ⋯-x/t-wk' {µ₁} ⦃ 𝕂 ⦄ ⦃ 𝕂' ⦄ ⦃ 𝕊 ⦄ {m'} {m/M} x/t =
    (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = 𝕂' ⦄ _ id) ≡⟨ {!!} ⟩
    `/id' (wk m' x/t)                 ∎

  kit-traversal : Traversal
  kit-traversal = record
    { _⋯_   = _⋯_
    ; ⋯-var = ⋯-var
    -- ; ⋯-↑   = ⋯-↑
    ; ⋯-id  = ⋯-id'
    -- ; ⋯-x/t-wk = λ x/t → ⋯-x/t-wk' ⦃ 𝕂' = kitᵣ ⦄ x/t
    -- ; ⋯-x/t-wk' = ⋯-x/t-wk'
    }

  -- open Traversal kit-traversal hiding (_⋯_; ⋯-var; kitᵣ; kitₛ) public

  -- ~-cong-⋯ :
  --   ∀ {{𝕂 : Kit}} {f g : µ₁ –[ 𝕂 ]→ µ₂} (v : µ₁ ⊢ M)
  --   → f ~ g
  --   → v ⋯ f ≡ v ⋯ g
  -- ~-cong-⋯ {f = f} {g} v f~g =
  --   ⋯-↑ (f ∷ [])
  --       (g ∷ [])
  --       (λ {µ} x →
  --         begin
  --           (` x) ⋯ f ↑* µ
  --         ≡⟨ ⋯-var x (f ↑* µ) ⟩
  --           `/id _ ((f ↑* µ) _ x)
  --         ≡⟨ cong (`/id _) (~-cong-↑* f~g _ x) ⟩
  --           `/id _ ((g ↑* µ) _ x)
  --         ≡⟨ sym (⋯-var x (g ↑* µ)) ⟩
  --           (` x) ⋯ g ↑* µ 
  --         ∎)
  --       v

  -- kit-homotopy : KitHomotopy kit-traversal
  -- kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

  -- open import Kitty.Term.Compose 𝕋 kit-traversal kit-homotopy

  -- open ComposeKit {{...}} public

  -- private
  --   ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
  --               (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
  --     v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
  --   ⋯-assoc {{𝕂₁}} {{𝕂₂}} {{𝕂}} v f g =
  --     v ⋯ f ⋯ g                            ≡⟨ refl ⟩
  --     v ⋯* (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
  --       ≡⟨ ⋯-↑ (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
  --             ((g ∘ₖ f) ∷[ 𝕂 ] [])
  --             (λ {µ} x →
  --               ` x ⋯ f ↑* µ ⋯ g ↑* µ                ≡⟨ cong (_⋯ g ↑* µ) (⋯-var x (f ↑* µ)) ⟩
  --               (`/id _ ((f ↑* µ) _ x)) ⋯ g ↑* µ     ≡⟨ tm-⋯-∘ (f ↑* µ) (g ↑* µ) x ⟩
  --               `/id _ (((g ↑* µ) ∘ₖ (f ↑* µ)) _ x)  ≡⟨ cong (λ h → `/id {{𝕂}} _ h) (sym (dist-↑*-∘ µ g f _ x)) ⟩
  --               `/id _ (((g ∘ₖ f) ↑* µ) _ x)         ≡⟨ sym (⋯-var x ((g ∘ₖ f) ↑* µ)) ⟩
  --               ` x ⋯ (g ∘ₖ f) ↑* µ                  ∎)
  --             v
  --       ⟩
  --     v ⋯* (_∷_ {b = 𝕂} (g ∘ₖ f) [])       ≡⟨ refl ⟩
  --     v ⋯ (g ∘ₖ f)       ∎

  -- kit-assoc : KitAssoc
  -- kit-assoc = record { ⋯-assoc = ⋯-assoc }

  -- open KitAssoc kit-assoc public hiding (kitᵣᵣ; kitᵣₛ; kitₛᵣ; kitₛₛ; wk-kitᵣ; wk-kitₛ)

  -- private
  --   ⋯-id' : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
  --   ⋯-id' {{𝕂}} {µ} {M} v =
  --     ⋯-↑ {µ₁ = µ} (idₖ ∷[ 𝕂 ] [])
  --         []
  --         (λ {µ} x →
  --           ` x ⋯ idₖ {{𝕂}} ↑* µ           ≡⟨ ⋯-var x (idₖ ↑* µ) ⟩
  --           `/id _ ((idₖ {{𝕂}} ↑* µ) _ x)  ≡⟨ cong (λ h → `/id _ h) (id↑*~id µ _ _ x) ⟩
  --           `/id _ (id/` _ x)              ≡⟨ id/`/id x ⟩
  --           ` x                            ∎)
  --         v

  -- kit-assoc-lemmas : KitAssocLemmas
  -- kit-assoc-lemmas = record { ⋯-id = ⋯-id' }

  -- open KitAssocLemmas kit-assoc-lemmas public

  -- instance
  --   kitᵣ  = KitTraversal.kitᵣ kit-traversal
  --   kitₛ  = KitTraversal.kitₛ kit-traversal
  --   kitᵣᵣ = KitAssoc.kitᵣᵣ kit-assoc
  --   kitₛᵣ = KitAssoc.kitₛᵣ kit-assoc
  --   kitᵣₛ = KitAssoc.kitᵣₛ kit-assoc
  --   kitₛₛ = KitAssoc.kitₛₛ kit-assoc
  --   wk-kitᵣ = KitAssoc.wk-kitᵣ kit-assoc
  --   wk-kitₛ = KitAssoc.wk-kitₛ kit-assoc

  -- open Kit {{...}} public
  -- open import Kitty.Term.Kit 𝕋 public



  -- -- module StarAttempt where
  -- --   open import Kitty.Util.Star
  -- --   open import Kitty.Term.MultiSub 𝕋

  -- --   ↑**-▷ : ∀ {𝕂s : List Kit} {µ₁} {µ₂} {µ} {m} (fs : µ₁ –[ 𝕂s ]→* µ₂) {mx} (x : µ₁ ▷▷ (µ ▷ m) ∋ mx)
  -- --         → (` x) ⋯* fs ↑** (µ ▷ m) ≡ (` x) ⋯* fs ↑** µ ↑** ([] ▷ m)
  -- --   ↑**-▷ {[]}     {µ₁} {µ₂} {µ} {m} []       x = refl
  -- --   ↑**-▷ {𝕂 ∷ 𝕂s} {µ₁} {µ₂} {µ} {m} (f ∷ fs) x =
  -- --     let instance _ = 𝕂 in
  -- --     (` x) ⋯* (f ∷ fs) ↑** (µ ▷ m)                             ≡⟨⟩
  -- --     (` x) ⋯* ((f ↑* (µ ▷ m)) ∷ (fs ↑** (µ ▷ m)))              ≡⟨⟩
  -- --     ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* (µ ▷ m))       ≡⟨ ~-cong-⋯ ((` x) ⋯* (fs ↑** (µ ▷ m))) (↑*-▷ µ m f) ⟩
  -- --     ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑ m)         ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (µ ▷ m)) (~-cong-↑ (~-sym (↑*-[] (f ↑* µ)))) ⟩
  -- --     ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑* [] ↑ m)   ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (µ ▷ m)) (~-sym (↑*-▷ [] m (f ↑* µ))) ⟩
  -- --     ((` x) ⋯* (fs ↑** (µ ▷ m)))        ⋯ (f ↑* µ ↑* ([] ▷ m)) ≡⟨ cong (_⋯ f ↑* µ ↑* ([] ▷ m)) (↑**-▷ fs x) ⟩
  -- --     ((` x) ⋯* (fs ↑** µ ↑** ([] ▷ m))) ⋯ (f ↑* µ ↑* ([] ▷ m)) ≡⟨⟩
  -- --     (` x) ⋯* ((f ↑* µ ↑* ([] ▷ m)) ∷ (fs ↑** µ ↑** ([] ▷ m))) ≡⟨⟩
  -- --     (` x) ⋯* (f ∷ fs) ↑** µ ↑** ([] ▷ m)                      ∎

  -- --   ↑**-here : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) {µ₁'} {m} →
  -- --     (` here refl) ⋯* fs ↑** (µ₁' ▷ m) ≡ ` here refl
  -- --   ↑**-here {[]} {µ₁} {.µ₁} [] {µ₁'} {m} = refl
  -- --   ↑**-here {𝕂s ▷ 𝕂} {µ₁} {µ₂} (f ∷ fs) {µ₁'} {m} =
  -- --     let instance _ = 𝕂 in
  -- --     ` here refl ⋯* (f ∷ fs) ↑** (µ₁' ▷ m)              ≡⟨⟩
  -- --     ` here refl ⋯* (fs ↑** (µ₁' ▷ m)) ⋯ f ↑* (µ₁' ▷ m) ≡⟨ cong (_⋯ f ↑* (µ₁' ▷ m)) (↑**-here fs) ⟩
  -- --     ` here refl ⋯ f ↑* (µ₁' ▷ m)                       ≡⟨ ~-cong-⋯ (` here refl) (↑*-▷ µ₁' m f) ⟩
  -- --     ` here refl ⋯ f ↑* µ₁' ↑ m                         ≡⟨ ⋯-var (here refl) (f ↑* µ₁' ↑ m) ⟩
  -- --     `/id (here refl & f ↑* µ₁' ↑ m)                    ≡⟨ cong `/id (&-↑-here (f ↑* µ₁')) ⟩
  -- --     `/id (id/` ⦃ 𝕂 ⦄ (here refl))                      ≡⟨ id/`/id (here refl) ⟩
  -- --     ` here refl                                        ∎

  -- --   wk-↑-dist-⋯'' : ∀ {𝕂s} {µ₁ µ₂ µ m'} {m} (x : (µ₁ ▷▷ µ) ∋ m) (fs : µ₁ –[ 𝕂s ]→* µ₂) →
  -- --     wk _ (` x) ⋯* fs ↑** (µ ▷ m')  ≡
  -- --     wk _ (` x ⋯* fs ↑** µ)
  -- --   wk-↑-dist-⋯'' {[]} {µ₁} {.µ₁} {µ} {m'} {m} x [] =
  -- --     wk _ (` x) ⋯* [] ↑** (µ ▷ m')  ≡⟨⟩
  -- --     wk _ (` x ⋯* [] ↑** µ)         ∎
  -- --   wk-↑-dist-⋯'' {𝕂s ▷ 𝕂} {µ₁} {µ₂} {µ} {m'} {m} x (f ∷ fs) =
  -- --     let instance _ = 𝕂 in
  -- --     wk _ (` x) ⋯* (f ∷ fs) ↑** (µ ▷ m')           ≡⟨⟩
  -- --     wk _ (` x) ⋯* fs ↑** (µ ▷ m') ⋯ f ↑* (µ ▷ m') ≡⟨ cong (_⋯ f ↑* (µ ▷ m')) (wk-↑-dist-⋯'' x fs) ⟩
  -- --     wk _ (` x ⋯* fs ↑** µ) ⋯ f ↑* (µ ▷ m')        ≡⟨ {!!} ⟩
  -- --     wk _ (` x ⋯* fs ↑** µ ⋯ f ↑* µ)               ≡⟨⟩
  -- --     wk _ (` x ⋯* (f ∷ fs) ↑** µ)                  ∎

  -- --   -- wk-↑-dist-⋯''' : ∀ {𝕂s} {µ₁ µ₂ µ m'} {m} (t : (µ₁ ▷▷ µ) ⊢ m) (fs : µ₁ –[ 𝕂s ]→* µ₂) →
  -- --   --   wk _ t ⋯* fs ↑** (µ ▷ m')  ≡
  -- --   --   wk _ (t ⋯* fs ↑** µ)
  -- --   -- wk-↑-dist-⋯''' {[]} {µ₁} {.µ₁} {µ} {m'} {m} t [] = refl
  -- --   -- wk-↑-dist-⋯''' {𝕂s ▷ 𝕂} {µ₁} {µ₂} {µ} {m'} {m} t (f ∷ fs) =
  -- --   --   let instance _ = 𝕂 in
  -- --   --   wk _ t ⋯* (f ∷ fs) ↑** (µ ▷ m')           ≡⟨⟩
  -- --   --   wk _ t ⋯* fs ↑** (µ ▷ m') ⋯ f ↑* (µ ▷ m') ≡⟨ cong (_⋯ f ↑* (µ ▷ m')) (wk-↑-dist-⋯''' t fs) ⟩
  -- --   --   wk _ (t ⋯* fs ↑** µ) ⋯ f ↑* (µ ▷ m')      ≡⟨ wk-↑-dist-⋯''' (t ⋯* fs ↑** µ) (f ∷ []) ⟩
  -- --   --   wk _ (t ⋯* fs ↑** µ ⋯ f ↑* µ)             ≡⟨⟩
  -- --   --   wk _ (t ⋯* (f ∷ fs) ↑** µ)                ∎

  -- --   open import Data.Nat using (ℕ; zero; suc; _+_)
  -- --   open import Data.Nat using (_<′_; _≤′_; ≤′-step; ≤′-refl)
  -- --   open import Data.Nat.Properties using (suc-injective)
  -- --   open import Data.Nat.Induction
  -- --   open import Induction.WellFounded

  -- --   0≤′n : ∀ {n} → 0 ≤′ n
  -- --   0≤′n {zero} = ≤′-refl
  -- --   0≤′n {suc n} = ≤′-step 0≤′n

  -- --   suc-≤′ : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
  -- --   suc-≤′ {m} {.m} ≤′-refl = ≤′-refl
  -- --   suc-≤′ {m} {.(suc _)} (≤′-step m<n) = ≤′-step (suc-≤′ m<n)

  -- --   wk-↑-dist-⋯''' : ∀ n {𝕂s} (eq : n ≡ length 𝕂s) {µ₁ µ₂ µ m'} {m} (t : (µ₁ ▷▷ µ) ⊢ m) (fs : µ₁ –[ 𝕂s ]→* µ₂) →
  -- --     wk _ t ⋯* fs ↑** (µ ▷ m')  ≡
  -- --     wk _ (t ⋯* fs ↑** µ)
  -- --   wk-↑-dist-⋯''' = <′-rec
  -- --     (λ n → ∀ {𝕂s} (eq : n ≡ length 𝕂s) {µ₁ µ₂ µ m'} {m} (t : (µ₁ ▷▷ µ) ⊢ m) (fs : µ₁ –[ 𝕂s ]→* µ₂)
  -- --         → wk _ t ⋯* fs ↑** (µ ▷ m')  ≡ wk _ (t ⋯* fs ↑** µ))
  -- --     λ where
  -- --       zero IH {[]} eq {µ₁} {.µ₁} {µ} {m'} {m} t [] → refl
  -- --       (suc zero) IH {[] ▷ 𝕂} eq {µ₁} {µ₂} {µ} {m'} {m} t (f ∷ []) →
  -- --         let instance _ = 𝕂 in
  -- --         wk _ t ⋯ f ↑* (µ ▷ m')           ≡⟨ {!!} ⟩
  -- --         wk _ (t ⋯ f ↑* µ)                ∎
  -- --       (suc (suc n)) IH {𝕂s ▷ 𝕂} eq {µ₁} {µ₂} {µ} {m'} {m} t (f ∷ fs) →
  -- --         let instance _ = 𝕂 in
  -- --         wk _ t ⋯* (f ∷ fs) ↑** (µ ▷ m')           ≡⟨⟩
  -- --         wk _ t ⋯* fs ↑** (µ ▷ m') ⋯ f ↑* (µ ▷ m') ≡⟨ cong (_⋯ f ↑* (µ ▷ m')) (IH (suc n) ≤′-refl (suc-injective eq) t fs) ⟩
  -- --         wk _ (t ⋯* fs ↑** µ) ⋯ f ↑* (µ ▷ m')      ≡⟨ IH 1 (suc-≤′ (suc-≤′ 0≤′n) ) refl (t ⋯* fs ↑** µ) (f ∷ []) ⟩
  -- --         wk _ (t ⋯* fs ↑** µ ⋯ f ↑* µ)             ≡⟨⟩
  -- --         wk _ (t ⋯* (f ∷ fs) ↑** µ)                ∎
  -- --   -- wk-↑-dist-⋯''' {.[]} {zero} {eq} {µ₁} {.µ₁} {µ} {m'} {m} t [] = refl
  -- --   -- wk-↑-dist-⋯''' {.(_ ▷ _)} {suc n} {eq} {µ₁} {µ₂} {µ} {m'} {m} t (_∷_ {b = 𝕂} {bs = 𝕂s} f fs) =
  -- --   --   let instance _ = 𝕂 in
  -- --   --   wk _ t ⋯* (f ∷ fs) ↑** (µ ▷ m')           ≡⟨⟩
  -- --   --   wk _ t ⋯* fs ↑** (µ ▷ m') ⋯ f ↑* (µ ▷ m') ≡⟨ cong (_⋯ f ↑* (µ ▷ m')) (wk-↑-dist-⋯''' t fs) ⟩
  -- --   --   wk _ (t ⋯* fs ↑** µ) ⋯ f ↑* (µ ▷ m')      ≡⟨ wk-↑-dist-⋯''' {n = {!!}} {eq = {!!}} (t ⋯* fs ↑** µ) (f ∷ []) ⟩
  -- --   --   wk _ (t ⋯* fs ↑** µ ⋯ f ↑* µ)             ≡⟨⟩
  -- --   --   wk _ (t ⋯* (f ∷ fs) ↑** µ)                ∎

  -- --   wk-↑-dist-⋯' : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₁' µ₂ m'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m') (f : µ₁ –[ 𝕂 ]→ µ₂) →
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ⋯ f ↑ m ↑* µ₁' ≡
  -- --     ` x ⋯ f ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁'     
  -- --   wk-↑-dist-⋯' ⦃ 𝕂 ⦄ {µ₁} {[]} {µ₂} {m'} {m} x f =
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* [] ⋯ f ↑ m ↑* [] ≡⟨ {!!} ⟩
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ⋯ f ↑ m             ≡⟨ cong (_⋯ f ↑ m) (⋯-var x (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id)) ⟩
  -- --     `/id (x & wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ⋯ f ↑ m        ≡⟨ cong (_⋯ f ↑ m) {!!} ⟩
  -- --     ` there x ⋯ f ↑ m                               ≡⟨ ⋯-var (there x) (f ↑ m) ⟩
  -- --     `/id (there x & f ↑ m)                          ≡⟨ cong `/id (&-↑-there f x) ⟩
  -- --     `/id (wk m (x & f))                             ≡⟨ sym (⋯-x/t-wk'' (x & f)) ⟩
  -- --     `/id (x & f) ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id            ≡⟨ cong (_⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) (sym (⋯-var x f)) ⟩
  -- --     ` x ⋯ f ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id                 ≡⟨ {!!} ⟩
  -- --     ` x ⋯ f ↑* [] ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* []     ∎
  -- --   wk-↑-dist-⋯' ⦃ 𝕂 ⦄ {µ₁} {µ₁' ▷ m₁'} {µ₂} {m'} {m} x@(here refl) f =
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* (µ₁' ▷ m₁') ⋯ f ↑ m ↑* (µ₁' ▷ m₁') ≡⟨ {!!} ⟩
  -- --     ` x ⋯ f ↑* (µ₁' ▷ m₁') ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* (µ₁' ▷ m₁')     ∎
  -- --   wk-↑-dist-⋯' ⦃ 𝕂 ⦄ {µ₁} {µ₁' ▷ m₁'} {µ₂} {m'} {m} x@(there y) f =
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* (µ₁' ▷ m₁') ⋯ f ↑ m ↑* (µ₁' ▷ m₁')                ≡⟨ {!!} ⟩
  -- --     ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ↑ m₁' ⋯ f ↑ m ↑* µ₁' ↑ m₁'                    ≡⟨ {!!} ⟩
  -- --     `/id (x & wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ↑ m₁') ⋯ f ↑ m ↑* µ₁' ↑ m₁'               ≡⟨ {!!} ⟩
  -- --     `/id (wk m₁' (y & wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁')) ⋯ f ↑ m ↑* µ₁' ↑ m₁'            ≡⟨ {!!} ⟩
  -- --     ` y ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ f ↑ m ↑* µ₁' ↑ m₁'  ≡⟨ {!!} ⟩
  -- --     ` y ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ⋯ f ↑ m ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id        ≡⟨⟩
  -- --     wk _ (` y ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ⋯ f ↑ m ↑* µ₁')                         ≡⟨ cong (wk _) (wk-↑-dist-⋯' y f) ⟩
  -- --     wk _ (` y ⋯ f ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁')                             ≡⟨ {!!} ⟩
  -- --     ` x ⋯ f ↑* µ₁' ↑ m₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ↑ m₁'                        ≡⟨ {!!} ⟩
  -- --     ` x ⋯ f ↑* (µ₁' ▷ m₁') ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* (µ₁' ▷ m₁')                    ∎

  -- --   -- wk-↑-dist-⋯ : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ M} {m} (t : µ₁ ⊢ M) (f : µ₁ –[ 𝕂 ]→ µ₂) →
  -- --   --   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ⋯ f ↑ m ≡
  -- --   --   t ⋯ f ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id
  -- --   -- wk-↑-dist-⋯ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {M} {m} t f =
  -- --   --   let xx = ⋯-↑ ((f ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ [])
  -- --   --                (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ f ∷ [])
  -- --   --                (λ {µ₁'} x →
  -- --   --                  ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁' ⋯ f ↑ m ↑* µ₁' ≡⟨ wk-↑-dist-⋯' x f ⟩
  -- --   --                  ` x ⋯ f ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ↑* µ₁'     ∎
  -- --   --                ) t in
  -- --   --   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ⋯ f ↑ m                  ≡⟨⟩
  -- --   --   t ⋯* ((f ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ [])        ≡⟨ sym (↑**-[] ((f ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ []) t) ⟩
  -- --   --   t ⋯* ((f ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ []) ↑** [] ≡⟨ xx ⟩
  -- --   --   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ f ∷ []) ↑** []       ≡⟨ ↑**-[] (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ f ∷ []) t ⟩
  -- --   --   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ∷ f ∷ [])              ≡⟨⟩
  -- --   --   t ⋯ f ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id                      ∎

  -- --   ↑**-there : ∀ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) {µ₁'} {m} {mx} (x : (µ₁ ▷▷ µ₁') ∋ mx) →
  -- --     ` there x ⋯* fs ↑** (µ₁' ▷ m) ≡ wkₛ m (` x ⋯* fs ↑** µ₁')
  -- --   ↑**-there {[]} {µ₁} {.µ₁} [] {µ₁'} {m} {mx} x =
  -- --     (` there x) ≡⟨ sym (⋯-x/t-wk'' x) ⟩
  -- --     wkₛ m (` x) ∎
  -- --   ↑**-there {𝕂s ▷ 𝕂} {µ₁} {µ₂} (f ∷ fs) {µ₁'} {m} {mx} x =
  -- --     -- let instance _ = 𝕂 in
  -- --     -- (` there x) ⋯* (f ∷ fs) ↑** (µ₁' ▷ m)              ≡⟨⟩
  -- --     -- (` there x) ⋯* (fs ↑** (µ₁' ▷ m)) ⋯ f ↑* (µ₁' ▷ m) ≡⟨ cong (_⋯ f ↑* (µ₁' ▷ m)) (↑**-there fs x) ⟩
  -- --     -- wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* (µ₁' ▷ m)       ≡⟨ ~-cong-⋯ _ (↑*-▷ µ₁' m f) ⟩
  -- --     -- wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* µ₁' ↑ m         ≡⟨⟩
  -- --     -- (` x) ⋯* fs ↑** µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ f ↑* µ₁' ↑ m ≡⟨ wk-↑-dist-⋯ ((` x) ⋯* fs ↑** µ₁') (f ↑* µ₁') ⟩
  -- --     -- (` x) ⋯* fs ↑** µ₁' ⋯ f ↑* µ₁' ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ≡⟨⟩
  -- --     -- wkₛ m ((` x) ⋯* fs ↑** µ₁' ⋯ f ↑* µ₁')             ≡⟨⟩
  -- --     -- wkₛ m ((` x) ⋯* (f ∷ fs) ↑** µ₁')                  ∎

  -- --     let instance _ = 𝕂 in
  -- --     (` there x) ⋯* (f ∷ fs) ↑** (µ₁' ▷ m)              ≡⟨⟩
  -- --     (` there x) ⋯* (fs ↑** (µ₁' ▷ m)) ⋯ f ↑* (µ₁' ▷ m) ≡⟨ cong (_⋯ f ↑* (µ₁' ▷ m)) (↑**-there fs x) ⟩
  -- --     wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* (µ₁' ▷ m)       ≡⟨ ~-cong-⋯ _ (↑*-▷ µ₁' m f) ⟩
  -- --     wkₛ m ((` x) ⋯* fs ↑** µ₁') ⋯ f ↑* µ₁' ↑ m         ≡⟨ {!!} ⟩
  -- --     `/id (wk m ((` x) ⋯* fs ↑** µ₁')) ⋯ f ↑* µ₁' ↑ m   ≡⟨ {!!} ⟩
  -- --     wkₛ m ((` x) ⋯* fs ↑** µ₁' ⋯ f ↑* µ₁')             ≡⟨⟩
  -- --     wkₛ m ((` x) ⋯* (f ∷ fs) ↑** µ₁')                  ∎

  -- --   ⋯-↑' : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
  -- --         → (∀ {m} (x : µ₁ ∋ m) → (` x) ⋯* f ≡ (` x) ⋯* g)
  -- --         → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁'))
  -- --   ⋯-↑' fs gs fs~gs {[]} x =
  -- --     (` x) ⋯* fs ↑** [] ≡⟨ ↑**-[] fs (` x) ⟩
  -- --     (` x) ⋯* fs        ≡⟨ fs~gs x ⟩
  -- --     (` x) ⋯* gs        ≡⟨ sym (↑**-[] gs (` x)) ⟩
  -- --     (` x) ⋯* gs ↑** [] ∎
  -- --   ⋯-↑' fs gs fs~gs {µ₁' ▷ m'} x@(here refl) =
  -- --     (` x) ⋯* fs ↑** (µ₁' ▷ m') ≡⟨ ↑**-here fs ⟩
  -- --     ` here refl                ≡⟨ sym (↑**-here gs) ⟩
  -- --     (` x) ⋯* gs ↑** (µ₁' ▷ m') ∎
  -- --   ⋯-↑' fs gs fs~gs {µ₁' ▷ m'} {m} x@(there y) =
  -- --     (` x) ⋯* fs ↑** (µ₁' ▷ m')  ≡⟨ ↑**-there fs y ⟩
  -- --     wk m' ((` y) ⋯* fs ↑** µ₁') ≡⟨ cong (wk m') (⋯-↑' fs gs fs~gs y) ⟩
  -- --     wk m' ((` y) ⋯* gs ↑** µ₁') ≡⟨ sym (↑**-there gs y) ⟩
  -- --     (` x) ⋯* gs ↑** (µ₁' ▷ m')  ∎

  -- --   -- ⋯-↑'' : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
  -- --   --        → (∀ {m} (x : µ₁ ∋ m) → (` x) ⋯*' f ≡ (` x) ⋯*' g)
  -- --   --        → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯*' (f ↑** µ₁') ≡ (` x) ⋯*' (g ↑** µ₁'))
  -- --   -- ⋯-↑'' fs gs fs~gs {[]} x =
  -- --   --   (` x) ⋯*' fs ↑** [] ≡⟨ {!↑**-[] fs x!} ⟩
  -- --   --   (` x) ⋯*' fs        ≡⟨ fs~gs x ⟩
  -- --   --   (` x) ⋯*' gs        ≡⟨ {!sym (↑**-[] gs x)!} ⟩
  -- --   --   (` x) ⋯*' gs ↑** [] ∎
  -- --   -- ⋯-↑'' fs gs fs~gs {µ₁' ▷ m'} x@(here refl) =
  -- --   --   (` x) ⋯*' fs ↑** (µ₁' ▷ m')        ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' fs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
  -- --   --   ` here refl                       ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' gs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' gs ↑** (µ₁' ▷ m') ∎
  -- --   -- ⋯-↑'' fs gs fs~gs {µ₁' ▷ m'} {m} x@(there y) =
  -- --   --   (` x) ⋯*' fs ↑** (µ₁' ▷ m')        ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' fs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
  -- --   --   wk m' ((` y) ⋯*' fs ↑** µ₁')       ≡⟨ cong (wk m') (⋯-↑'' fs gs fs~gs y) ⟩
  -- --   --   wk m' ((` y) ⋯*' gs ↑** µ₁')       ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' gs ↑** µ₁' ↑** ([] ▷ m') ≡⟨ {!!} ⟩
  -- --   --   (` x) ⋯*' gs ↑** (µ₁' ▷ m') ∎
