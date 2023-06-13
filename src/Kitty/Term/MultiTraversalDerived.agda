open import Kitty.Term.Terms using (Terms)
open import Kitty.Term.MultiTraversal using (MultiTraversal)

module Kitty.Term.MultiTraversalDerived {𝕋 : Terms} (MT : MultiTraversal 𝕋) where

import Kitty.Term.Sub

module WithSub {ℓ} (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ) where
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
  open ≡-Reasoning

  open import Kitty.Term.Kit 𝕋 public
  open import Kitty.Term.MultiSub 𝕋
  open import Kitty.Term.Prelude
  open import Kitty.Term.Sub 𝕋
  open import Kitty.Term.Traversal 𝕋
  open import Kitty.Util.Star

  open Kit ⦃ … ⦄ public
  open Terms 𝕋 hiding (VarScoped)
  open SubWithLaws 𝕊 public
  open Sub SubWithLaws-Sub public

  open import Kitty.Util.SubstProperties

  terms : Terms
  terms = 𝕋

  open Terms terms public using (#_; VarScoped)

  open MultiTraversal MT public renaming (⋯-var to ⋯-var-MT; _⋯_ to _⋯-MT_)

  open import Kitty.Term.KitOrder terms public
  open _⊑ₖ_ ⦃ … ⦄ public

  -- instance 𝕊 = 𝕊

  private
    ⋯-id' :
      ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ {S st} {s : Sort st} (v : S ⊢ s) →
      v ⋯-MT id ⦃ K = K ⦄ ≡ v
    ⋯-id' ⦃ K ⦄ {S} {s} v =
      ⋯-↑ ⦃ 𝕊 = 𝕊 ⦄ {S₁ = S} (id ∷[ (_ , K) ] [])
          []
          (λ {S} x →
            ` x ⋯-MT id ⦃ K = K ⦄ ↑*' S     ≡⟨ ⋯-var-MT ⦃ 𝕊 = 𝕊 ⦄ x (id ↑*' S) ⟩
            `/id (x & (id ⦃ K = K ⦄ ↑*' S)) ≡⟨ use-~ (↑*'~↑* ⦃ 𝕊 = 𝕊 ⦄ S) _ x ⟩
            `/id (x & (id ⦃ K = K ⦄ ↑* S))  ≡⟨ use-~ (id↑*~id S _) _ x ⟩
            `/id (x & (id ⦃ K = K ⦄))       ≡⟨ cong `/id (&-id x) ⟩
            `/id (id/` x)                    ≡⟨ id/`/id x ⟩
            ` x                              ∎)
          v

  kit-traversal : Traversal 𝕊
  kit-traversal = record
    { _⋯_   = _⋯-MT_
    ; ⋯-var = ⋯-var-MT ⦃ 𝕊 = 𝕊 ⦄
    ; ⋯-id  = ⋯-id'
    }

  open Traversal 𝕊 kit-traversal public

  open import Kitty.Term.KitT kit-traversal public
  open KitT ⦃ … ⦄ public

  instance Kᵣ' = Kᵣ; Kₛ' = Kₛ; Wᵣ = kittᵣ; Wₛ = kittₛ

  open import Kitty.Term.KitHomotopy kit-traversal public

  ~-cong-↑*''' :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
      {S₁} {S₂} {S} {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂}
    → ϕ ~ ϕ'
    → (ϕ ↑*' S) ~ (ϕ' ↑*' S)
  ~-cong-↑*''' {S = []}    ϕ~ϕ' = ϕ~ϕ'
  ~-cong-↑*''' {S = S ▷ s} ϕ~ϕ' = ~-cong-↑ (~-cong-↑*''' ϕ~ϕ')

  ~-cong-⋯ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
      {S₁ S₂ st} {s : Sort st}
      {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} (t : S₁ ⊢ s)
    → f ~ g
    → t ⋯ f ≡ t ⋯ g
  ~-cong-⋯ ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S₁} {S₂} {st} {s} {f} {g} t f~g =
    ⋯-↑ ⦃ 𝕊 = 𝕊 ⦄
        (f ∷ [])
        (g ∷ [])
        (λ {S} x →
          (` x) ⋯ f ↑*' S      ≡⟨ ⋯-var x (f ↑*' S) ⟩
          `/id (x & (f ↑*' S)) ≡⟨ use-~ (~-cong-↑*''' f~g) _ x ⟩
          `/id (x & (g ↑*' S)) ≡⟨ sym (⋯-var x (g ↑*' S)) ⟩
          (` x) ⋯ g ↑*' S      ∎
        )
        t

  kit-homotopy : KitHomotopy
  kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

  open KitHomotopy kit-homotopy public hiding (~-cong-⋯)

  open import Kitty.Term.ComposeKit kit-homotopy public
  open import Kitty.Term.SubCompose kit-homotopy public

  module WithSubCompose (SC : SubCompose) where
    -- instance 𝕊C = SC
    open import Kitty.Term.ComposeTraversal SC

    open ComposeKit ⦃ … ⦄ public
    open SubCompose SC public

    private
      ⋯-assoc :
        ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
          {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
          {_∋/⊢_ : VarScoped} ⦃ K  : Kit _∋/⊢_ ⦄
          ⦃ W₁ : KitT K₁ ⦄
          ⦃ W₂ : KitT K₂ ⦄
          ⦃ W : KitT K ⦄
          ⦃ C : ComposeKit K₁ K₂ K ⦄
          {S₁ S₂ S₃ st} {s : Sort st}
          (t : S₁ ⊢ s) (f : S₁ –[ K₁ ]→ S₂) (g : S₂ –[ K₂ ]→ S₃)
        → t ⋯ f ⋯ g ≡ t ⋯ (f ·ₖ g)
      ⋯-assoc {{K₁}} {{K₂}} {{K}} v f g =
        v ⋯ f ⋯ g                            ≡⟨ refl ⟩
        v ⋯* (g ∷[ (_ , K₂) ] f ∷[ (_ , K₁) ] [])
          ≡⟨ ⋯-↑ ⦃ 𝕊 = 𝕊 ⦄
                (g ∷[ _ , K₂ ] f ∷[ _ , K₁ ] [])
                ((g ∘ₖ f) ∷[ _ , K ] [])
                (λ {S} x →
                  ` x ⋯ f ↑*' S ⋯ g ↑*' S            ≡⟨ ~-cong-⋯ (` x ⋯ f ↑*' S) (↑*'~↑* ⦃ 𝕊 = 𝕊 ⦄ S) ⟩
                  ` x ⋯ f ↑*' S ⋯ g ↑* S             ≡⟨ cong (_⋯ (g ↑* S)) (~-cong-⋯ (` x)  (↑*'~↑* ⦃ 𝕊 = 𝕊 ⦄ S)) ⟩
                  ` x ⋯ f ↑* S ⋯ g ↑* S              ≡⟨ cong (_⋯ g ↑* S) (⋯-var x (f ↑* S)) ⟩
                  (`/id (x & (f ↑* S))) ⋯ g ↑* S     ≡⟨ tm-⋯-· (f ↑* S) (g ↑* S) x ⟩
                  `/id (x & ((f ↑* S) ·ₖ (g ↑* S)))  ≡⟨ sym (use-~ (dist-↑*-· S f g) _ x) ⟩
                  `/id (x & ((f ·ₖ g) ↑* S))         ≡⟨ sym (⋯-var x ((g ∘ₖ f) ↑* S)) ⟩
                  ` x ⋯ (f ·ₖ g) ↑* S                ≡⟨ sym (~-cong-⋯ (` x) (↑*'~↑* ⦃ 𝕊 = 𝕊 ⦄ S)) ⟩
                  ` x ⋯ (f ·ₖ g) ↑*' S               ∎)
                v
          ⟩
        v ⋯* (_∷_ {b = _ , K} (g ∘ₖ f) [])       ≡⟨ refl ⟩
        v ⋯ (g ∘ₖ f)       ∎

    compose-traversal : ComposeTraversal
    compose-traversal = record { ⋯-assoc = ⋯-assoc }

    open ComposeTraversal compose-traversal public

    instance Cᵣ' = Cᵣ; Cₛ' = Cₛ

module Functional where
  open import Kitty.Term.Sub.Functional 𝕋 hiding (Sub-→; SubWithLaws-→)
  open import Kitty.Term.Sub.Functional 𝕋 using  (Sub-→; SubWithLaws-→) public
  open WithSub SubWithLaws-→ public

  open Fun-SubCompose kit-homotopy hiding (SubCompose-→)
  open Fun-SubCompose kit-homotopy using  (SubCompose-→) public
  open WithSubCompose SubCompose-→ public

module Instance where
  open WithSub ⦃ … ⦄ public renaming (module WithSubCompose to WithSubCompose')
  open WithSubCompose' ⦃ … ⦄ public

  -- instance
  --   Kᵣ'  = Kᵣ
  --   Kₛ'  : ∀ ⦃ 𝕊 : SubWithLaws ⦄ → Kit
  --   Kₛ' ⦃ 𝕊 ⦄ = Traversal.Kₛ 𝕊 kit-traversal
  --   Kᵣᵣ = Cᵣ
  --   Kₛᵣ = Cₛᵣ
  --   Kₛₛ = Cₛₛ
  --   wk-Kᵣ = kittᵣ
  --   wk-Kₛ = kittₛ

-- module StarAttempt where
--   open import Kitty.Util.Star
--   open import Kitty.Term.MultiSub 𝕋

--   ↑**-▷ : ∀ {Ks : List Kit} {S₁} {S₂} {S} {s} (fs : S₁ –[ Ks ]→* S₂) {mx} (x : S₁ ▷▷ (S ▷ s) ∋ mx)
--         → (` x) ⋯* fs ↑** (S ▷ s) ≡ (` x) ⋯* fs ↑** S ↑** ([] ▷ s)
--   ↑**-▷ {[]}     {S₁} {S₂} {S} {s} []       x = refl
--   ↑**-▷ {K ∷ Ks} {S₁} {S₂} {S} {s} (f ∷ fs) x =
--     let instance _ = K in
--     (` x) ⋯* (f ∷ fs) ↑** (S ▷ s)                             ≡⟨⟩
--     (` x) ⋯* ((f ↑* (S ▷ s)) ∷ (fs ↑** (S ▷ s)))              ≡⟨⟩
--     ((` x) ⋯* (fs ↑** (S ▷ s)))        ⋯ (f ↑* (S ▷ s))       ≡⟨ ~-cong-⋯ ((` x) ⋯* (fs ↑** (S ▷ s))) (↑*-▷ S s f) ⟩
--     ((` x) ⋯* (fs ↑** (S ▷ s)))        ⋯ (f ↑* S ↑ s)         ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (S ▷ s)) (~-cong-↑ (~-sym (↑*-[] (f ↑* S)))) ⟩
--     ((` x) ⋯* (fs ↑** (S ▷ s)))        ⋯ (f ↑* S ↑* [] ↑ s)   ≡⟨ ~-cong-⋯ ((` x) ⋯* fs ↑** (S ▷ s)) (~-sym (↑*-▷ [] s (f ↑* S))) ⟩
--     ((` x) ⋯* (fs ↑** (S ▷ s)))        ⋯ (f ↑* S ↑* ([] ▷ s)) ≡⟨ cong (_⋯ f ↑* S ↑* ([] ▷ s)) (↑**-▷ fs x) ⟩
--     ((` x) ⋯* (fs ↑** S ↑** ([] ▷ s))) ⋯ (f ↑* S ↑* ([] ▷ s)) ≡⟨⟩
--     (` x) ⋯* ((f ↑* S ↑* ([] ▷ s)) ∷ (fs ↑** S ↑** ([] ▷ s))) ≡⟨⟩
--     (` x) ⋯* (f ∷ fs) ↑** S ↑** ([] ▷ s)                      ∎

--   ↑**-here : ∀ {Ks : List Kit} {S₁} {S₂} (fs : S₁ –[ Ks ]→* S₂) {S₁'} {s} →
--     (` here refl) ⋯* fs ↑** (S₁' ▷ s) ≡ ` here refl
--   ↑**-here {[]} {S₁} {.S₁} [] {S₁'} {s} = refl
--   ↑**-here {Ks ▷ K} {S₁} {S₂} (f ∷ fs) {S₁'} {s} =
--     let instance _ = K in
--     ` here refl ⋯* (f ∷ fs) ↑** (S₁' ▷ s)              ≡⟨⟩
--     ` here refl ⋯* (fs ↑** (S₁' ▷ s)) ⋯ f ↑* (S₁' ▷ s) ≡⟨ cong (_⋯ f ↑* (S₁' ▷ s)) (↑**-here fs) ⟩
--     ` here refl ⋯ f ↑* (S₁' ▷ s)                       ≡⟨ ~-cong-⋯ (` here refl) (↑*-▷ S₁' s f) ⟩
--     ` here refl ⋯ f ↑* S₁' ↑ s                         ≡⟨ ⋯-var (here refl) (f ↑* S₁' ↑ s) ⟩
--     `/id (here refl & f ↑* S₁' ↑ s)                    ≡⟨ cong `/id (&-↑-here (f ↑* S₁')) ⟩
--     `/id (id/` ⦃ K ⦄ (here refl))                      ≡⟨ id/`/id (here refl) ⟩
--     ` here refl                                        ∎

--   wk-↑-dist-⋯'' : ∀ {Ks} {S₁ S₂ S s'} {s} (x : (S₁ ▷▷ S) ∋ s) (fs : S₁ –[ Ks ]→* S₂) →
--     wk _ (` x) ⋯* fs ↑** (S ▷ s')  ≡
--     wk _ (` x ⋯* fs ↑** S)
--   wk-↑-dist-⋯'' {[]} {S₁} {.S₁} {S} {s'} {s} x [] =
--     wk _ (` x) ⋯* [] ↑** (S ▷ s')  ≡⟨⟩
--     wk _ (` x ⋯* [] ↑** S)         ∎
--   wk-↑-dist-⋯'' {Ks ▷ K} {S₁} {S₂} {S} {s'} {s} x (f ∷ fs) =
--     let instance _ = K in
--     wk _ (` x) ⋯* (f ∷ fs) ↑** (S ▷ s')           ≡⟨⟩
--     wk _ (` x) ⋯* fs ↑** (S ▷ s') ⋯ f ↑* (S ▷ s') ≡⟨ cong (_⋯ f ↑* (S ▷ s')) (wk-↑-dist-⋯'' x fs) ⟩
--     wk _ (` x ⋯* fs ↑** S) ⋯ f ↑* (S ▷ s')        ≡⟨ {!!} ⟩
--     wk _ (` x ⋯* fs ↑** S ⋯ f ↑* S)               ≡⟨⟩
--     wk _ (` x ⋯* (f ∷ fs) ↑** S)                  ∎

--   -- wk-↑-dist-⋯''' : ∀ {Ks} {S₁ S₂ S s'} {s} (t : (S₁ ▷▷ S) ⊢ s) (fs : S₁ –[ Ks ]→* S₂) →
--   --   wk _ t ⋯* fs ↑** (S ▷ s')  ≡
--   --   wk _ (t ⋯* fs ↑** S)
--   -- wk-↑-dist-⋯''' {[]} {S₁} {.S₁} {S} {s'} {s} t [] = refl
--   -- wk-↑-dist-⋯''' {Ks ▷ K} {S₁} {S₂} {S} {s'} {s} t (f ∷ fs) =
--   --   let instance _ = K in
--   --   wk _ t ⋯* (f ∷ fs) ↑** (S ▷ s')           ≡⟨⟩
--   --   wk _ t ⋯* fs ↑** (S ▷ s') ⋯ f ↑* (S ▷ s') ≡⟨ cong (_⋯ f ↑* (S ▷ s')) (wk-↑-dist-⋯''' t fs) ⟩
--   --   wk _ (t ⋯* fs ↑** S) ⋯ f ↑* (S ▷ s')      ≡⟨ wk-↑-dist-⋯''' (t ⋯* fs ↑** S) (f ∷ []) ⟩
--   --   wk _ (t ⋯* fs ↑** S ⋯ f ↑* S)             ≡⟨⟩
--   --   wk _ (t ⋯* (f ∷ fs) ↑** S)                ∎

--   open import Data.Nat using (ℕ; zero; suc; _+_)
--   open import Data.Nat using (_<′_; _≤′_; ≤′-step; ≤′-refl)
--   open import Data.Nat.Properties using (suc-injective)
--   open import Data.Nat.Induction
--   open import Induction.WellFounded

--   0≤′n : ∀ {n} → 0 ≤′ n
--   0≤′n {zero} = ≤′-refl
--   0≤′n {suc n} = ≤′-step 0≤′n

--   suc-≤′ : ∀ {s n} → s ≤′ n → suc s ≤′ suc n
--   suc-≤′ {s} {.s} ≤′-refl = ≤′-refl
--   suc-≤′ {s} {.(suc _)} (≤′-step s<n) = ≤′-step (suc-≤′ s<n)

--   wk-↑-dist-⋯''' : ∀ n {Ks} (eq : n ≡ length Ks) {S₁ S₂ S s'} {s} (t : (S₁ ▷▷ S) ⊢ s) (fs : S₁ –[ Ks ]→* S₂) →
--     wk _ t ⋯* fs ↑** (S ▷ s')  ≡
--     wk _ (t ⋯* fs ↑** S)
--   wk-↑-dist-⋯''' = <′-rec
--     (λ n → ∀ {Ks} (eq : n ≡ length Ks) {S₁ S₂ S s'} {s} (t : (S₁ ▷▷ S) ⊢ s) (fs : S₁ –[ Ks ]→* S₂)
--         → wk _ t ⋯* fs ↑** (S ▷ s')  ≡ wk _ (t ⋯* fs ↑** S))
--     λ where
--       zero IH {[]} eq {S₁} {.S₁} {S} {s'} {s} t [] → refl
--       (suc zero) IH {[] ▷ K} eq {S₁} {S₂} {S} {s'} {s} t (f ∷ []) →
--         let instance _ = K in
--         wk _ t ⋯ f ↑* (S ▷ s')           ≡⟨ {!!} ⟩
--         wk _ (t ⋯ f ↑* S)                ∎
--       (suc (suc n)) IH {Ks ▷ K} eq {S₁} {S₂} {S} {s'} {s} t (f ∷ fs) →
--         let instance _ = K in
--         wk _ t ⋯* (f ∷ fs) ↑** (S ▷ s')           ≡⟨⟩
--         wk _ t ⋯* fs ↑** (S ▷ s') ⋯ f ↑* (S ▷ s') ≡⟨ cong (_⋯ f ↑* (S ▷ s')) (IH (suc n) ≤′-refl (suc-injective eq) t fs) ⟩
--         wk _ (t ⋯* fs ↑** S) ⋯ f ↑* (S ▷ s')      ≡⟨ IH 1 (suc-≤′ (suc-≤′ 0≤′n) ) refl (t ⋯* fs ↑** S) (f ∷ []) ⟩
--         wk _ (t ⋯* fs ↑** S ⋯ f ↑* S)             ≡⟨⟩
--         wk _ (t ⋯* (f ∷ fs) ↑** S)                ∎
--   -- wk-↑-dist-⋯''' {.[]} {zero} {eq} {S₁} {.S₁} {S} {s'} {s} t [] = refl
--   -- wk-↑-dist-⋯''' {.(_ ▷ _)} {suc n} {eq} {S₁} {S₂} {S} {s'} {s} t (_∷_ {b = K} {bs = Ks} f fs) =
--   --   let instance _ = K in
--   --   wk _ t ⋯* (f ∷ fs) ↑** (S ▷ s')           ≡⟨⟩
--   --   wk _ t ⋯* fs ↑** (S ▷ s') ⋯ f ↑* (S ▷ s') ≡⟨ cong (_⋯ f ↑* (S ▷ s')) (wk-↑-dist-⋯''' t fs) ⟩
--   --   wk _ (t ⋯* fs ↑** S) ⋯ f ↑* (S ▷ s')      ≡⟨ wk-↑-dist-⋯''' {n = {!!}} {eq = {!!}} (t ⋯* fs ↑** S) (f ∷ []) ⟩
--   --   wk _ (t ⋯* fs ↑** S ⋯ f ↑* S)             ≡⟨⟩
--   --   wk _ (t ⋯* (f ∷ fs) ↑** S)                ∎

--   wk-↑-dist-⋯' : ∀ ⦃ K ⦄ {S₁ S₁' S₂ s'} {s} (x : (S₁ ▷▷ S₁') ∋ s') (f : S₁ –[ K ]→ S₂) →
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ⋯ f ↑ s ↑* S₁' ≡
--     ` x ⋯ f ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁'     
--   wk-↑-dist-⋯' ⦃ K ⦄ {S₁} {[]} {S₂} {s'} {s} x f =
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* [] ⋯ f ↑ s ↑* [] ≡⟨ {!!} ⟩
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ⋯ f ↑ s             ≡⟨ cong (_⋯ f ↑ s) (⋯-var x (wkₖ ⦃ K = Kᵣ ⦄ s id)) ⟩
--     `/id (x & wkₖ ⦃ K = Kᵣ ⦄ s id) ⋯ f ↑ s        ≡⟨ cong (_⋯ f ↑ s) {!!} ⟩
--     ` there x ⋯ f ↑ s                               ≡⟨ ⋯-var (there x) (f ↑ s) ⟩
--     `/id (there x & f ↑ s)                          ≡⟨ cong `/id (&-↑-there f x) ⟩
--     `/id (wk s (x & f))                             ≡⟨ sym (⋯-x/t-wk'' (x & f)) ⟩
--     `/id (x & f) ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id            ≡⟨ cong (_⋯ wkₖ ⦃ K = Kᵣ ⦄ s id) (sym (⋯-var x f)) ⟩
--     ` x ⋯ f ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id                 ≡⟨ {!!} ⟩
--     ` x ⋯ f ↑* [] ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* []     ∎
--   wk-↑-dist-⋯' ⦃ K ⦄ {S₁} {S₁' ▷ s₁'} {S₂} {s'} {s} x@(here refl) f =
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* (S₁' ▷ s₁') ⋯ f ↑ s ↑* (S₁' ▷ s₁') ≡⟨ {!!} ⟩
--     ` x ⋯ f ↑* (S₁' ▷ s₁') ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* (S₁' ▷ s₁')     ∎
--   wk-↑-dist-⋯' ⦃ K ⦄ {S₁} {S₁' ▷ s₁'} {S₂} {s'} {s} x@(there y) f =
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* (S₁' ▷ s₁') ⋯ f ↑ s ↑* (S₁' ▷ s₁')                ≡⟨ {!!} ⟩
--     ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ↑ s₁' ⋯ f ↑ s ↑* S₁' ↑ s₁'                    ≡⟨ {!!} ⟩
--     `/id (x & wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ↑ s₁') ⋯ f ↑ s ↑* S₁' ↑ s₁'               ≡⟨ {!!} ⟩
--     `/id (wk s₁' (y & wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁')) ⋯ f ↑ s ↑* S₁' ↑ s₁'            ≡⟨ {!!} ⟩
--     ` y ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ⋯ f ↑ s ↑* S₁' ↑ s₁'  ≡⟨ {!!} ⟩
--     ` y ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ⋯ f ↑ s ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id        ≡⟨⟩
--     wk _ (` y ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ⋯ f ↑ s ↑* S₁')                         ≡⟨ cong (wk _) (wk-↑-dist-⋯' y f) ⟩
--     wk _ (` y ⋯ f ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁')                             ≡⟨ {!!} ⟩
--     ` x ⋯ f ↑* S₁' ↑ s₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ↑ s₁'                        ≡⟨ {!!} ⟩
--     ` x ⋯ f ↑* (S₁' ▷ s₁') ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* (S₁' ▷ s₁')                    ∎

--   -- wk-↑-dist-⋯ : ∀ ⦃ K ⦄ {S₁ S₂ s} {s} (t : S₁ ⊢ s) (f : S₁ –[ K ]→ S₂) →
--   --   t ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ⋯ f ↑ s ≡
--   --   t ⋯ f ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id
--   -- wk-↑-dist-⋯ ⦃ K ⦄ {S₁} {S₂} {s} {s} t f =
--   --   let xx = ⋯-↑ ((f ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ s id ∷ [])
--   --                (wkₖ ⦃ K = Kᵣ ⦄ s id ∷ f ∷ [])
--   --                (λ {S₁'} x →
--   --                  ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁' ⋯ f ↑ s ↑* S₁' ≡⟨ wk-↑-dist-⋯' x f ⟩
--   --                  ` x ⋯ f ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ↑* S₁'     ∎
--   --                ) t in
--   --   t ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ⋯ f ↑ s                  ≡⟨⟩
--   --   t ⋯* ((f ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ s id ∷ [])        ≡⟨ sym (↑**-[] ((f ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ s id ∷ []) t) ⟩
--   --   t ⋯* ((f ↑ s) ∷ wkₖ ⦃ K = Kᵣ ⦄ s id ∷ []) ↑** [] ≡⟨ xx ⟩
--   --   t ⋯* (wkₖ ⦃ K = Kᵣ ⦄ s id ∷ f ∷ []) ↑** []       ≡⟨ ↑**-[] (wkₖ ⦃ K = Kᵣ ⦄ s id ∷ f ∷ []) t ⟩
--   --   t ⋯* (wkₖ ⦃ K = Kᵣ ⦄ s id ∷ f ∷ [])              ≡⟨⟩
--   --   t ⋯ f ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id                      ∎

--   ↑**-there : ∀ {Ks : List Kit} {S₁} {S₂} (fs : S₁ –[ Ks ]→* S₂) {S₁'} {s} {mx} (x : (S₁ ▷▷ S₁') ∋ mx) →
--     ` there x ⋯* fs ↑** (S₁' ▷ s) ≡ wkₛ s (` x ⋯* fs ↑** S₁')
--   ↑**-there {[]} {S₁} {.S₁} [] {S₁'} {s} {mx} x =
--     (` there x) ≡⟨ sym (⋯-x/t-wk'' x) ⟩
--     wkₛ s (` x) ∎
--   ↑**-there {Ks ▷ K} {S₁} {S₂} (f ∷ fs) {S₁'} {s} {mx} x =
--     -- let instance _ = K in
--     -- (` there x) ⋯* (f ∷ fs) ↑** (S₁' ▷ s)              ≡⟨⟩
--     -- (` there x) ⋯* (fs ↑** (S₁' ▷ s)) ⋯ f ↑* (S₁' ▷ s) ≡⟨ cong (_⋯ f ↑* (S₁' ▷ s)) (↑**-there fs x) ⟩
--     -- wkₛ s ((` x) ⋯* fs ↑** S₁') ⋯ f ↑* (S₁' ▷ s)       ≡⟨ ~-cong-⋯ _ (↑*-▷ S₁' s f) ⟩
--     -- wkₛ s ((` x) ⋯* fs ↑** S₁') ⋯ f ↑* S₁' ↑ s         ≡⟨⟩
--     -- (` x) ⋯* fs ↑** S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ⋯ f ↑* S₁' ↑ s ≡⟨ wk-↑-dist-⋯ ((` x) ⋯* fs ↑** S₁') (f ↑* S₁') ⟩
--     -- (` x) ⋯* fs ↑** S₁' ⋯ f ↑* S₁' ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ≡⟨⟩
--     -- wkₛ s ((` x) ⋯* fs ↑** S₁' ⋯ f ↑* S₁')             ≡⟨⟩
--     -- wkₛ s ((` x) ⋯* (f ∷ fs) ↑** S₁')                  ∎

--     let instance _ = K in
--     (` there x) ⋯* (f ∷ fs) ↑** (S₁' ▷ s)              ≡⟨⟩
--     (` there x) ⋯* (fs ↑** (S₁' ▷ s)) ⋯ f ↑* (S₁' ▷ s) ≡⟨ cong (_⋯ f ↑* (S₁' ▷ s)) (↑**-there fs x) ⟩
--     wkₛ s ((` x) ⋯* fs ↑** S₁') ⋯ f ↑* (S₁' ▷ s)       ≡⟨ ~-cong-⋯ _ (↑*-▷ S₁' s f) ⟩
--     wkₛ s ((` x) ⋯* fs ↑** S₁') ⋯ f ↑* S₁' ↑ s         ≡⟨ {!!} ⟩
--     `/id (wk s ((` x) ⋯* fs ↑** S₁')) ⋯ f ↑* S₁' ↑ s   ≡⟨ {!!} ⟩
--     wkₛ s ((` x) ⋯* fs ↑** S₁' ⋯ f ↑* S₁')             ≡⟨⟩
--     wkₛ s ((` x) ⋯* (f ∷ fs) ↑** S₁')                  ∎

--   ⋯-↑' : ∀ {Ks₁ Ks₂ : List Kit} {S₁} {S₂} (f : S₁ –[ Ks₁ ]→* S₂) (g : S₁ –[ Ks₂ ]→* S₂)
--         → (∀ {s} (x : S₁ ∋ s) → (` x) ⋯* f ≡ (` x) ⋯* g)
--         → (∀ {S₁'} {s} (x : (S₁ ▷▷ S₁') ∋ s) → (` x) ⋯* (f ↑** S₁') ≡ (` x) ⋯* (g ↑** S₁'))
--   ⋯-↑' fs gs fs~gs {[]} x =
--     (` x) ⋯* fs ↑** [] ≡⟨ ↑**-[] fs (` x) ⟩
--     (` x) ⋯* fs        ≡⟨ fs~gs x ⟩
--     (` x) ⋯* gs        ≡⟨ sym (↑**-[] gs (` x)) ⟩
--     (` x) ⋯* gs ↑** [] ∎
--   ⋯-↑' fs gs fs~gs {S₁' ▷ s'} x@(here refl) =
--     (` x) ⋯* fs ↑** (S₁' ▷ s') ≡⟨ ↑**-here fs ⟩
--     ` here refl                ≡⟨ sym (↑**-here gs) ⟩
--     (` x) ⋯* gs ↑** (S₁' ▷ s') ∎
--   ⋯-↑' fs gs fs~gs {S₁' ▷ s'} {s} x@(there y) =
--     (` x) ⋯* fs ↑** (S₁' ▷ s')  ≡⟨ ↑**-there fs y ⟩
--     wk s' ((` y) ⋯* fs ↑** S₁') ≡⟨ cong (wk s') (⋯-↑' fs gs fs~gs y) ⟩
--     wk s' ((` y) ⋯* gs ↑** S₁') ≡⟨ sym (↑**-there gs y) ⟩
--     (` x) ⋯* gs ↑** (S₁' ▷ s')  ∎

--   -- ⋯-↑'' : ∀ {Ks₁ Ks₂ : List Kit} {S₁} {S₂} (f : S₁ –[ Ks₁ ]→* S₂) (g : S₁ –[ Ks₂ ]→* S₂)
--   --        → (∀ {s} (x : S₁ ∋ s) → (` x) ⋯*' f ≡ (` x) ⋯*' g)
--   --        → (∀ {S₁'} {s} (x : (S₁ ▷▷ S₁') ∋ s) → (` x) ⋯*' (f ↑** S₁') ≡ (` x) ⋯*' (g ↑** S₁'))
--   -- ⋯-↑'' fs gs fs~gs {[]} x =
--   --   (` x) ⋯*' fs ↑** [] ≡⟨ {!↑**-[] fs x!} ⟩
--   --   (` x) ⋯*' fs        ≡⟨ fs~gs x ⟩
--   --   (` x) ⋯*' gs        ≡⟨ {!sym (↑**-[] gs x)!} ⟩
--   --   (` x) ⋯*' gs ↑** [] ∎
--   -- ⋯-↑'' fs gs fs~gs {S₁' ▷ s'} x@(here refl) =
--   --   (` x) ⋯*' fs ↑** (S₁' ▷ s')        ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' fs ↑** S₁' ↑** ([] ▷ s') ≡⟨ {!!} ⟩
--   --   ` here refl                       ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' gs ↑** S₁' ↑** ([] ▷ s') ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' gs ↑** (S₁' ▷ s') ∎
--   -- ⋯-↑'' fs gs fs~gs {S₁' ▷ s'} {s} x@(there y) =
--   --   (` x) ⋯*' fs ↑** (S₁' ▷ s')        ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' fs ↑** S₁' ↑** ([] ▷ s') ≡⟨ {!!} ⟩
--   --   wk s' ((` y) ⋯*' fs ↑** S₁')       ≡⟨ cong (wk s') (⋯-↑'' fs gs fs~gs y) ⟩
--   --   wk s' ((` y) ⋯*' gs ↑** S₁')       ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' gs ↑** S₁' ↑** ([] ▷ s') ≡⟨ {!!} ⟩
--   --   (` x) ⋯*' gs ↑** (S₁' ▷ s') ∎
