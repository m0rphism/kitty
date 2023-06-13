open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
import Kitty.Term.Sub
import Kitty.Term.SubCompose

module Kitty.Term.ComposeTraversal
    {𝕋 : Terms}
    {ℓ} {𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ}
    {T : Traversal 𝕋 𝕊}
    {H : KitHomotopy T}
    (𝕊C : Kitty.Term.SubCompose.SubCompose H)
  where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT T
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Term.ComposeKit H
open import Kitty.Term.SubCompose H
open import Kitty.Util.SubstProperties

open Terms 𝕋
open Traversal T
open KitHomotopy H
open Kit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open SubCompose 𝕊C
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄
open ComposeKit ⦃ … ⦄

private instance
  _ = kitᵣ
  _ = kitₛ
  _ = ckitᵣ
  _ = kittᵣ
  _ = kittₛ

private variable
  st                        : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx

-- ComposeTraversal ------------------------------------------------------------

-- If the client provides a `ComposeTraversal` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeTraversal : Set (lsuc ℓ) where
  field
    ⋯-assoc :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        ⦃ W₁ : KitT 𝕂₁ ⦄
        ⦃ W₂ : KitT 𝕂₂ ⦄
        ⦃ W₁₂ : KitT 𝕂 ⦄
        ⦃ 𝔸 : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
        (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂) (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
      → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)

  -- Example:
  --
  --   instance kit-assoc : ComposeTraversal {{traversal}}
  --   ComposeTraversal.⋯-assoc kit-assoc (` x) f g =
  --     tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  --     tm' ((g ∘ₖ f) _ x) ∎
  --   ComposeTraversal.⋯-assoc kit-assoc (λ→ e) f g = cong λ→_
  --     (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  --      e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  --      e ⋯ (g ∘ₖ f) ↑ _         ∎)
  --   ComposeTraversal.⋯-assoc kit-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

  wk*-wkₖ* : 
      ∀ (t : S ⊢ s) S' →
      wk* S' t ≡ t ⋯ᵣ wkₖ* S' id
  wk*-wkₖ* {S} {s} t [] =
    wk* [] t        ≡⟨⟩
    t               ≡⟨ sym (⋯-id t) ⟩
    t ⋯ᵣ id         ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-[] id)) ⟩
    t ⋯ᵣ wkₖ* [] id ∎
  wk*-wkₖ* {S} {s} t (S' ▷ s') =
    wk* (S' ▷ s') t                ≡⟨⟩
    wk s' (wk* S' t)               ≡⟨ cong (wk s') (wk*-wkₖ* t S') ⟩
    wk s' (t ⋯ᵣ wkₖ* S' id)        ≡⟨⟩
    t ⋯ᵣ wkₖ* S' id ⋯ᵣ wkₖ s' id   ≡⟨ ⋯-assoc t (wkₖ* S' id) (wkₖ s' id) ⟩
    t ⋯ᵣ (wkₖ* S' id ·ₖ wkₖ s' id) ≡⟨ ~-cong-⋯ t (~-sym (wk-ϕ-id (wkₖ* S' id))) ⟩
    t ⋯ᵣ wkₖ s' (wkₖ* S' id)       ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-▷ S' s' id)) ⟩
    t ⋯ᵣ wkₖ* (S' ▷ s') id         ∎

  dist-↑-f :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W₁₂ : KitT 𝕂 ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ 𝕂₁ ]→ S₂)
    → t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id ⋯ (ϕ ↑ s) ≡ t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id
  dist-↑-f ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t ϕ =
    (t ⋯ wkₖ _ id) ⋯ (ϕ ↑ _)       ≡⟨ ⋯-assoc t (wkₖ _ id) (ϕ ↑ _)  ⟩
    t ⋯ (wkₖ _ id ·[ C₂ ] (ϕ ↑ _)) ≡⟨ ~-cong-⋯ t (~-sym (↑-wk ϕ _)) ⟩
    t ⋯ (ϕ ·[ C₁ ] wkₖ _ id)       ≡⟨ sym (⋯-assoc t ϕ (wkₖ _ id)) ⟩
    (t ⋯ ϕ) ⋯ wkₖ _ id             ∎

  -- &/⋯-assoc' :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ 𝕂₁₂ 𝕂₂₃ 𝕂₁₂,₃ 𝕂₁,₂₃ ⦄
  --     ⦃ C₁₂ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁₂ ⦄
  --     ⦃ C₁₂,₃ : ComposeKit 𝕂₁₂ 𝕂₃ 𝕂₁₂,₃ ⦄
  --     ⦃ C₂₃ : ComposeKit 𝕂₂ 𝕂₃ 𝕂₂₃ ⦄
  --     ⦃ C₁,₂₃ : ComposeKit 𝕂₁ 𝕂₂₃ 𝕂₁,₂₃ ⦄
  --     {S₁ S₂ S₃} {s} 
  --     (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ₁ : S₁ –[ 𝕂₂ ]→ S₂) (ϕ₂ : S₂ –[ 𝕂₃ ]→ S₃) →
  --   `/id ((x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂) ≡ `/id (x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂))
  -- &/⋯-assoc' = ?

  -- &/⋯-assoc :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ 𝕂₁₂ 𝕂₂₃ 𝕂₁₂₃ ⦄
  --     ⦃ C₁₂ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁₂ ⦄
  --     ⦃ C₁₂,₃ : ComposeKit 𝕂₁₂ 𝕂₃ 𝕂₁₂₃ ⦄
  --     ⦃ C₂₃ : ComposeKit 𝕂₂ 𝕂₃ 𝕂₂₃ ⦄
  --     ⦃ C₁,₂₃ : ComposeKit 𝕂₁ 𝕂₂₃ 𝕂₁₂₃ ⦄
  --     {S₁ S₂ S₃} {s} 
  --     (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ₁ : S₁ –[ 𝕂₂ ]→ S₂) (ϕ₂ : S₂ –[ 𝕂₃ ]→ S₃) →
  --   (x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂ ≡ x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂)
  -- &/⋯-assoc = ?

  ·-assoc :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢₃_ : VarScoped} ⦃ 𝕂₃ : Kit _∋/⊢₃_ ⦄
      {_∋/⊢₁₂_ : VarScoped} ⦃ 𝕂₁₂ : Kit _∋/⊢₁₂_ ⦄
      {_∋/⊢₂₃_ : VarScoped} ⦃ 𝕂₂₃ : Kit _∋/⊢₂₃_ ⦄
      {_∋/⊢₁₂,₃_ : VarScoped} ⦃ 𝕂₁₂,₃ : Kit _∋/⊢₁₂,₃_ ⦄
      {_∋/⊢₁,₂₃_ : VarScoped} ⦃ 𝕂₁,₂₃ : Kit _∋/⊢₁,₂₃_ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W₃ : KitT 𝕂₃ ⦄
      ⦃ W₁₂ : KitT 𝕂₁₂ ⦄
      ⦃ W₂₃ : KitT 𝕂₂₃ ⦄
      ⦃ W₁₂,₃ : KitT 𝕂₁₂,₃ ⦄
      ⦃ W₁,₂₃ : KitT 𝕂₁,₂₃ ⦄
      ⦃ C₁₂ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁₂ ⦄
      ⦃ C₁₂,₃ : ComposeKit 𝕂₁₂ 𝕂₃ 𝕂₁₂,₃ ⦄
      ⦃ C₂₃ : ComposeKit 𝕂₂ 𝕂₃ 𝕂₂₃ ⦄
      ⦃ C₁,₂₃ : ComposeKit 𝕂₁ 𝕂₂₃ 𝕂₁,₂₃ ⦄
      {S₁} {S₂} {S₃} {S₄}
      (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
      (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
      (ϕ₃ : S₃ –[ 𝕂₃ ]→ S₄)
    → ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃) ~ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))
  ·-assoc ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ ⦃ 𝕂₁₂ ⦄ ⦃ 𝕂₂₃ ⦄ ⦃ 𝕂₁₂,₃ ⦄ ⦃ 𝕂₁,₂₃ ⦄ ⦃ C₁₂ ⦄ ⦃ C₁₂,₃ ⦄ ⦃ C₂₃ ⦄ ⦃ C₁,₂₃ ⦄
          {S₁} {S₂} {S₃} {S₄} ϕ₁ ϕ₂ ϕ₃ = mk-~ λ s x →
    `/id (x & ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃))                     ≡⟨ sym (⋯-var x ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)) ⟩
    ` x ⋯ ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)                          ≡⟨ sym (⋯-assoc (` x) (ϕ₁ ·ₖ ϕ₂) ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ ϕ₂) ⋯ ϕ₃                             ≡⟨ sym (cong (_⋯ ϕ₃) (⋯-assoc (` x) ϕ₁ ϕ₂)) ⟩
    ` x ⋯ ϕ₁ ⋯ ϕ₂ ⋯ ϕ₃                                ≡⟨ ⋯-assoc (` x ⋯ ϕ₁) ϕ₂ ϕ₃ ⟩
    ` x ⋯ ϕ₁ ⋯ (ϕ₂ ·ₖ ϕ₃)                             ≡⟨ ⋯-assoc (` x) ϕ₁ (ϕ₂ ·ₖ ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))                          ≡⟨ ⋯-var x (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)) ⟩
    `/id (x & (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)))                     ∎

  ↑*-wk* :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      ⦃ C₁₁ : ComposeKit 𝕂₁ 𝕂₁ 𝕂₁ ⦄
      ⦃ C₂₂ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      ⦃ C₃₃ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      ⦃ Cx₁ : ComposeKit 𝕂 𝕂₂ 𝕂 ⦄
      ⦃ Cx₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W  : KitT 𝕂 ⦄
      {S₁} {S₂} (ϕ : S₁ –[ 𝕂₁ ]→ S₂) S
    → (ϕ ·[ C₁ ] wkₖ* S id) ~ (wkₖ* S id ·[ C₂ ] (ϕ ↑* S))
  ↑*-wk* ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {S₁ = S₁} {S₂} ϕ [] =
    (ϕ ·[ C₁ ] wkₖ* [] id)         ~⟨ ~-cong-· ~-refl (wkₖ*-[] id) ⟩
    (ϕ ·[ C₁ ] id)                 ~⟨ ·-idʳ ϕ ⟩
    ϕ                              ~⟨ ~-sym (·-idˡ ϕ) ⟩
    (id ·[ C₂ ] ϕ)                 ~⟨ ~-sym (~-cong-· (wkₖ*-[] id) (↑*-[] ϕ)) ⟩
    (wkₖ* [] id ·[ C₂ ] (ϕ ↑* [])) ~∎
  ↑*-wk* ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₁₁ ⦄ ⦃ C₂₂ ⦄ ⦃ C₃₃ ⦄ ⦃ Cx₁ ⦄ ⦃ Cx₂ ⦄ {S₁ = S₁} {S₂} ϕ (S ▷ s) =
    (ϕ ·[ C₁ ] wkₖ* (S ▷ s) id)                          ~⟨ ~-cong-· ~-refl (wkₖ*-▷ S s id) ⟩
    (ϕ ·[ C₁ ] wkₖ s (wkₖ* S id))                        ~⟨ ~-cong-· ~-refl (wk-ϕ-id (wkₖ* S id)) ⟩
    (ϕ ·[ C₁ ] (wkₖ* S id ·[ C₂₂ ] wkₖ s id))            ~⟨ ~-sym (·-assoc ϕ (wkₖ* S id) (wkₖ s id)) ⟩
    ((ϕ ·[ C₁ ] wkₖ* S id) ·[ Cx₁ ] wkₖ s id)            ~⟨ ~-cong-· (↑*-wk* ϕ S) ~-refl ⟩
    ((wkₖ* S id ·[ C₂ ] (ϕ ↑* S)) ·[ Cx₁ ] wkₖ s id)     ~⟨ ·-assoc (wkₖ* S id) (ϕ ↑* S) (wkₖ s id)  ⟩
    (wkₖ* S id ·[ Cx₂ ] ((ϕ ↑* S) ·[ C₁ ] wkₖ s id))     ~⟨ ~-cong-· ~-refl (↑-wk (ϕ ↑* S) s) ⟩
    (wkₖ* S id ·[ Cx₂ ] (wkₖ s id ·[ C₂ ] (ϕ ↑* S) ↑ s)) ~⟨ ~-sym (·-assoc (wkₖ* S id) (wkₖ s id) ((ϕ ↑* S) ↑ s)) ⟩
    ((wkₖ* S id ·[ C₂₂ ] wkₖ s id) ·[ C₂ ] (ϕ ↑* S) ↑ s) ~⟨ ~-cong-· (~-sym (wk-ϕ-id (wkₖ* S id))) ~-refl ⟩
    (wkₖ s (wkₖ* S id) ·[ C₂ ] ((ϕ ↑* S) ↑ s))           ~⟨ ~-sym (~-cong-· (wkₖ*-▷ S s id) (↑*-▷ S s ϕ)) ⟩
    (wkₖ* (S ▷ s) id ·[ C₂ ] (ϕ ↑* (S ▷ s)))             ~∎

  dist-↑*-f :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂₁⊔𝕂₂ : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₁₁ : ComposeKit 𝕂₁ 𝕂₁ 𝕂₁ ⦄
      ⦃ C₂₂ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      ⦃ C₃₃ : ComposeKit 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ Cx₁ : ComposeKit 𝕂₁⊔𝕂₂ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ Cx₂ : ComposeKit 𝕂₂ 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W₁₂ : KitT 𝕂₁⊔𝕂₂ ⦄
      (t : S₁ ⊢ s) (ϕ : S₁ –[ 𝕂₁ ]→ S₂)
    → t ⋯ wkₖ* ⦃ 𝕂 = 𝕂₂ ⦄ S id ⋯ (ϕ ↑* S) ≡ t ⋯ ϕ ⋯ wkₖ* ⦃ 𝕂 = 𝕂₂ ⦄ S id
  dist-↑*-f {S = S} ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t ϕ =
    (t ⋯ wkₖ* S id) ⋯ (ϕ ↑* S)       ≡⟨ ⋯-assoc t (wkₖ* S id) (ϕ ↑* S)  ⟩
    t ⋯ (wkₖ* S id ·[ C₂ ] (ϕ ↑* S)) ≡⟨ ~-cong-⋯ t (~-sym (↑*-wk* ϕ S)) ⟩
    t ⋯ (ϕ ·[ C₁ ] wkₖ* S id)        ≡⟨ sym (⋯-assoc t ϕ (wkₖ* S id)) ⟩
    (t ⋯ ϕ) ⋯ wkₖ* S id              ∎

  dist-↑-⦅⦆-· :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ C₃ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      {S₁ S₂ s} (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂) →
    (⦅ x/t ⦆ ·[ C₁ ] ϕ) ~ ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)
  dist-↑-⦅⦆-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {S₁} {S₂} {s} x/t ϕ = mk-~ λ where
    sx x@(here refl) →
      `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                        ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
      `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                              ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (use-~-hom (⦅⦆-,ₖ x/t) _ x) ⟩
      `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                          ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (&-,ₖ-here id x/t) ⟩
      `/id (x/t &/⋯ ϕ)                                      ≡⟨ ι-`/id (x/t &/⋯ ϕ) ⟩
      `/id (ι-∋/⊢ (x/t &/⋯ ϕ))                              ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (sym (&-,ₖ-here id (x/t &/⋯[ C₁ ] ϕ))) ⟩
      `/id (ι-∋/⊢ (here refl & (id ⦃ 𝕂 = 𝕂 ⦄ ,ₖ (x/t &/⋯[ C₁ ] ϕ))))
                                                            ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■))
                                                                    (sym (use-~-hom (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ)) _ (here refl))) ⟩
      `/id (ι-∋/⊢ (here refl & ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))        ≡⟨ cong `/id (sym (&/⋯-& ⦃ C₂ ⦄ (here refl) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) ⟩
      `/id ⦃ 𝕂 ⦄ (id/` (here refl) &/⋯[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) (sym (&-↑-here ϕ)) ⟩ 
      `/id (x & (ϕ ↑ s) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)            ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ ↑ s) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ x)) ⟩
      `/id (x & ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))      ∎
    sx x@(there y) →
      `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                                ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
      `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                                      ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (use-~-hom (⦅⦆-,ₖ x/t) _ x) ⟩
      `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                                  ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-,ₖ-there id x/t y) ⟩
      `/id (y & id &/⋯[ C₁ ] ϕ)                                     ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-id y) ⟩
      `/id ⦃ 𝕂 ⦄ (id/` y &/⋯ ϕ)                                     ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (&/⋯-& y ϕ) ⟩
      `/id (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ (y & ϕ))                      ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (sym (&-ι-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ ϕ y)) ⟩
      `/id (y & (ι-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ ϕ))                ≡⟨ use-~ (~-ι-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ ϕ) _ y ⟩

      `/id (y & ϕ)                                                  ≡⟨ sym (use-~ (·-idʳ ϕ) _ y) ⟩
      `/id (y & (ϕ ·[ C₂ ] id))                                     ≡⟨ use-~ (~-cong-· ~-refl
                                                                        (~-sym (wk-cancels-,ₖ-· id (x/t &/⋯[ C₁ ] ϕ)))) _ y ⟩
      `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] (id ,ₖ (x/t &/⋯[ C₁ ] ϕ))))) ≡⟨ use-~ (~-cong-· ⦃ 𝕂₁ = 𝕂₂ ⦄ ⦃ 𝕂₂ = 𝕂 ⦄ ⦃ 𝕂 = 𝕂 ⦄ ~-refl
                                                                            (~-cong-· ⦃ 𝕂₁ = 𝕂₂ ⦄ ⦃ 𝕂₂ = 𝕂 ⦄ ⦃ 𝕂 = 𝕂 ⦄ ~-refl (~-sym (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ))))) _ y ⟩
      `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))) ≡⟨ sym (use-~ (·-assoc ϕ (wkₖ _ id) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) _ y) ⟩
      `/id (y & ((ϕ ·[ C₃ ] wkₖ _ id) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) ≡⟨ use-~ (~-cong-· (~-sym (wk-ϕ-id ϕ)) ~-refl) _ y ⟩
      `/id (y & (wkₖ _ ϕ ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))              ≡⟨ cong `/id
                                                                            (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (wkₖ _ ϕ) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ y) ⟩
      `/id (y & (wkₖ _ ϕ) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                  ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))
                                                                                        (&-wkₖ-wk ϕ y) ⟩
      `/id (wk _ (y & ϕ) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                   ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))
                                                                                        (sym (&-↑-there ϕ y)) ⟩ 
      `/id (x & (ϕ ↑ s) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                    ≡⟨ cong `/id
                                                                        (sym (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (ϕ ↑ s) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ x)) ⟩
      `/id (x & ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))              ∎

  -- ComposeKit for Substitutions ------------------------------------------------

  -- TODO: generalize with ≡ₜ
  ~-cong-&/⋯ₛ :
    ∀ {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ W : KitT 𝕂 ⦄ {st} {s : Sort st} {t₁ t₂ : S₁ ⊢ s}
      {ϕ₁ ϕ₂ : S₁ –[ 𝕂 ]→ S₂}
    → t₁ ≡ t₂
    → ϕ₁ ~ ϕ₂
    → t₁ ⋯ ϕ₁ ≡ t₂ ⋯ ϕ₂
  ~-cong-&/⋯ₛ refl ϕ₁~ϕ₂ = ~-cong-⋯ _ ϕ₁~ϕ₂

  &/⋯-wk-↑ₛ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K kitᵣ K ⦄
      {S₁} {S₂} {st} {s} {sx : Sort st}
      (t : S₁ ⊢ sx)
      (ϕ : S₁ –[ K ]→ S₂)
    → t ⋯ ϕ ⋯ wknᵣ ≡ t ⋯ wknᵣ ⋯ (ϕ ↑ s)
  &/⋯-wk-↑ₛ {_} {S₁} {S₂} {st} {s} {sx} t ϕ =
    t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id          ≡⟨ ⋯-assoc t ϕ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) ⟩
    t ⋯ (ϕ ·ₖ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id)       ≡⟨ ~-cong-⋯ t (↑-wk ϕ _) ⟩
    t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ·ₖ (ϕ ↑ s)) ≡⟨ sym (⋯-assoc t (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) (ϕ ↑ s)) ⟩
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ s)    ∎

  ckitₛ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K kitᵣ K ⦄ → ComposeKit kitₛ K kitₛ
  ckitₛ ⦃ K ⦄ ⦃ C ⦄ = record
    { 𝕂₁⊑𝕂₁⊔𝕂₂  = ⊑ₖ-refl ⦃ kitₛ ⦄
    ; 𝕂₂⊑𝕂₁⊔𝕂₂  = ⊑ₖ-⊤ ⦃ K ⦄
    ; _&/⋯_      = _⋯_
    ; &/⋯-⋯      = λ x/t ϕ → refl
    ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ ⦃ K ⦄ ⦃ C ⦄
    ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
    }

  private instance _ = ckitₛ

  ckitₛᵣ : ComposeKit kitₛ kitᵣ kitₛ
  ckitₛᵣ = ckitₛ

  ckitₛₛ : ComposeKit kitₛ kitₛ kitₛ
  ckitₛₛ = ckitₛ

  -- infixl  9  _ₛ·_  _ₛ·ᵣ_  _ₛ·ₛ_
  -- infixr  9  _∘ₛ_  _ᵣ∘ₛ_  _ₛ∘ₛ_
  infixl  9  _ₛ·ᵣ_  _ₛ·ₛ_
  infixr  9  _ᵣ∘ₛ_  _ₛ∘ₛ_

  _ₛ·_ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K kitᵣ K ⦄
           {S₁} {S₂} {S₃} → S₁ –[ kitₛ ]→ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ kitₛ ]→ S₃
  σ ₛ· ϕ = σ ·ₖ ϕ

  _∘ₛ_ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K kitᵣ K ⦄
           {S₁} {S₂} {S₃} → S₂ –[ K ]→ S₃ → S₁ –[ kitₛ ]→ S₂ → S₁ –[ kitₛ ]→ S₃
  ϕ₂ ∘ₛ ϕ₁ = ϕ₁ ₛ· ϕ₂

  _ₛ·ᵣ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ kitₛ ]→ S₂ → S₂ –[ kitᵣ ]→ S₃ → S₁ –[ kitₛ ]→ S₃
  _ₛ·ₛ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ kitₛ ]→ S₂ → S₂ –[ kitₛ ]→ S₃ → S₁ –[ kitₛ ]→ S₃
  _ᵣ∘ₛ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ kitᵣ ]→ S₃ → S₁ –[ kitₛ ]→ S₂ → S₁ –[ kitₛ ]→ S₃
  _ₛ∘ₛ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ kitₛ ]→ S₃ → S₁ –[ kitₛ ]→ S₂ → S₁ –[ kitₛ ]→ S₃
  _ₛ·ᵣ_ = _·ₖ_
  _ₛ·ₛ_ = _·ₖ_
  _ᵣ∘ₛ_ = _∘ₖ_
  _ₛ∘ₛ_ = _∘ₖ_

--   ∘~∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
--               {{𝔸  : ComposeKit 𝕂₁  𝕂₂  𝕂}}
--               {{𝔸' : ComposeKit 𝕂₁' 𝕂₂' 𝕂}}
--               {ϕ₁  : S₁ –[ 𝕂₁  ]→ S₂ } {ϕ₂  : S₂  –[ 𝕂₂  ]→ S₃}
--               {ϕ₁' : S₁ –[ 𝕂₁' ]→ S₂'} {ϕ₂' : S₂' –[ 𝕂₂' ]→ S₃} →
--     (ϕ₁ ·[ 𝔸 ] ϕ₂) ~ (ϕ₁' ·[ 𝔸' ] ϕ₂') →
--     ∀ {s} (t : S₁ ⊢ s) →
--     t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
--   ∘~∘→⋯≡⋯ ⦃ 𝔸 = 𝔸 ⦄ ⦃ 𝔸' ⦄ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
--     t ⋯ ϕ₁ ⋯ ϕ₂         ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
--     t ⋯ ϕ₁  ·[ 𝔸  ] ϕ₂  ≡⟨ ~-cong-⋯ t eq ⟩
--     t ⋯ ϕ₁' ·[ 𝔸' ] ϕ₂' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
--     t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

  wk-cancels-,ₖ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ ⦃ W : KitT 𝕂 ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ 𝕂₂ ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂₂ ] s)
    → t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wk-cancels-,ₖ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C = C ⦄ t ϕ x/t =
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (ϕ ,ₖ x/t)        ≡⟨ ⋯-assoc ⦃ 𝔸 = C ⦄ t (wkₖ _ id) (ϕ ,ₖ x/t) ⟩
    t ⋯ (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ·[ C ] (ϕ ,ₖ x/t)) ≡⟨ ~-cong-⋯ _ (wk-cancels-,ₖ-· ⦃ C = C ⦄ ϕ x/t) ⟩
    t ⋯ ϕ                                       ∎

  wkᵣ-cancels-,ₖ :
    ∀ {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ 𝕂₂ ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂₂ ] s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₖ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkᵣ-cancels-,ᵣ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ᵣ S₂) (x : S₂ ∋ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ᵣ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkᵣ-cancels-,ₛ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ₛ S₂) (t' : S₂ ⊢ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₛ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkₛ-cancels-,ᵣ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ᵣ S₂) (x : S₂ ∋ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkₛ-cancels-,ᵣ t ϕ x = wk-cancels-,ₖ ⦃ C = ckitₛᵣ ⦄ t ϕ x

  wkₛ-cancels-,ₛ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ₛ S₂) (t' : S₂ ⊢ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkₛ-cancels-,ₛ t ϕ t' = wk-cancels-,ₖ ⦃ C = ckitₛₛ ⦄ t ϕ t'

  --------------------------------------------------------------------------------

  dist-ᵣ·ᵣ-⦅⦆ :
    ∀ {S₁ S₂ s} (x : S₁ ∋ s) (ρ : S₁ →ᵣ S₂) →
    (⦅ x ⦆ ᵣ·ᵣ ρ) ~ ((ρ ↑ s) ᵣ·ᵣ ⦅ x & ρ ⦆)
  dist-ᵣ·ᵣ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ₛ·ᵣ-⦅⦆ :
    ∀ {S₁ S₂ s} (t : S₁ ⊢ s) (ρ : S₁ →ᵣ S₂) →
    (⦅ t ⦆ ₛ·ᵣ ρ) ~ ((ρ ↑ s) ᵣ·ₛ ⦅ t ⋯ ρ ⦆)
  dist-ₛ·ᵣ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ᵣ·ₛ-⦅⦆ :
    ∀ {S₁ S₂ s} (x : S₁ ∋ s) (σ : S₁ →ₛ S₂) →
    (⦅ x ⦆ ᵣ·ₛ σ) ~ ((σ ↑ s) ₛ·ₛ ⦅ x & σ ⦆)
  dist-ᵣ·ₛ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ₛ·ₛ-⦅⦆ :
    ∀ {S₁ S₂ s} (t : S₁ ⊢ s) (σ : S₁ →ₛ S₂) →
    (⦅ t ⦆ ₛ·ₛ σ) ~ ((σ ↑ s) ₛ·ₛ ⦅ t ⋯ σ ⦆)
  dist-ₛ·ₛ-⦅⦆ = dist-↑-⦅⦆-·

  --------------------------------------------------------------------------------

  dist-⦅⦆-⋯ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ ⦃ W : KitT 𝕂 ⦄ 
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      {S₁ S₂ s} {st} {s' : Sort st}
      (t : (s ∷ S₁) ⊢ s') (x/t : S₁ ∋/⊢[ 𝕂₁ ] s) (ϕ : S₁ –[ 𝕂₂ ]→ S₂) →
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆
  dist-⦅⦆-⋯ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {S₁} {S₂} {s} {st} {s'} t x/t ϕ =
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ                           ≡⟨ ⋯-assoc t ⦅ x/t ⦆ ϕ ⟩
    t ⋯ (⦅ x/t ⦆ ·[ C₁ ] ϕ)                   ≡⟨ ~-cong-⋯ t (dist-↑-⦅⦆-· x/t ϕ) ⟩
    t ⋯ ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ≡⟨ sym (⋯-assoc t (ϕ ↑ s) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ⟩
    t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆         ∎

  dist-⦅⦆ᵣ-⋯ᵣ : ∀ {S₁ S₂ s} {st} {s' : Sort st} (t : (s ∷ S₁) ⊢ s') (x : S₁ ∋ s) (ρ : S₁ →ᵣ S₂) →
    t ⋯ ⦅ x ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ s) ⋯ ⦅ x & ρ ⦆
  dist-⦅⦆ᵣ-⋯ᵣ = dist-⦅⦆-⋯

  dist-⦅⦆ₛ-⋯ᵣ : ∀ {S₁ S₂ s} {st} {s' : Sort st} (t : (s ∷ S₁) ⊢ s') (t' : S₁ ⊢ s) (ρ : S₁ →ᵣ S₂) →
    t ⋯ ⦅ t' ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ s) ⋯ ⦅ t' ⋯ ρ ⦆
  dist-⦅⦆ₛ-⋯ᵣ = dist-⦅⦆-⋯

  dist-⦅⦆ᵣ-⋯ₛ : ∀ {S₁ S₂ s} {st} {s' : Sort st} (t : (s ∷ S₁) ⊢ s') (x : S₁ ∋ s) (σ : S₁ →ₛ S₂) →
    t ⋯ ⦅ x ⦆ ⋯ σ ≡ t ⋯ (σ ↑ s) ⋯ ⦅ x & σ ⦆
  dist-⦅⦆ᵣ-⋯ₛ = dist-⦅⦆-⋯

  dist-⦅⦆ₛ-⋯ₛ : ∀ {S₁ S₂ s} {st} {s' : Sort st} (t : (s ∷ S₁) ⊢ s') (t' : S₁ ⊢ s) (σ : S₁ →ₛ S₂) →
    t ⋯ ⦅ t' ⦆ ⋯ σ ≡ t ⋯ (σ ↑ s) ⋯ ⦅ t' ⋯ σ ⦆
  dist-⦅⦆ₛ-⋯ₛ = dist-⦅⦆-⋯

  -- For ITraversal implementations
  dist-⦅⦆ₛ-⋯ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ W : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₂ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      ⦃ C₃ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      {S₁ S₂ s} {st} {s' : Sort st} 
      (t : (S₁ ▷ s) ⊢ s') (t' : S₁ ⊢ s) (ϕ : S₁ –[ 𝕂 ]→ S₂) →
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ
  dist-⦅⦆ₛ-⋯ ⦃ 𝕂 ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {S₁} {S₂} {s} {st} {s'} t t' ϕ =
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ                   ≡⟨ dist-⦅⦆-⋯ ⦃ C₁ = C₁ ⦄ t t' ϕ ⟩
    t ⋯ (ϕ ↑ s) ⋯ ⦅ t' &/⋯[ C₁ ] ϕ ⦆ₛ ≡⟨ cong (λ ■ → t ⋯ ϕ ↑ s ⋯ ⦅ ■ ⦆ₛ) (&/⋯-⋯ ⦃ C₁ ⦄ t' ϕ) ⟩
    t ⋯ (ϕ ↑ s) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ         ∎

--   record ComposeTraversalLemmas : Set₁ where

  ⋯-idₛ : ∀ {S st} {s : Sort st} (t : S ⊢ s) → t ⋯ id ⦃ 𝕂 = kitₛ ⦄ ≡ t
  ⋯-idᵣ : ∀ {S st} {s : Sort st} (t : S ⊢ s) → t ⋯ id ⦃ 𝕂 = kitᵣ ⦄ ≡ t
  ⋯-idₛ = ⋯-id
  ⋯-idᵣ = ⋯-id

  -- -- TODO OLD: We can transfer this from ⋯-id if we extend ComposeKit with a lemma,
  -- -- that operations on terms determine operations on &/⋯
  -- -- We could go even further and say operations on &/⋯ and ⋯ are determined by
  -- -- operations on ap. Note that this is precisely what KitAltSimple does!!!!
  -- &/⋯-id :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
  --     ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
  --     {S} {s/s} (x/t : S ∋/⊢[ 𝕂₁ ] s/s)
  --   → x/t &/⋯ id ⦃ 𝕂 = 𝕂₂ ⦄ ≡ ι-∋/⊢ x/t
  -- &/⋯-id ⦃ 𝕂 ⦄ {S} {s} x/t = {!!}

  wk-cancels-⦅⦆ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄ ⦃ KT : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      {S st} {s' : Sort st}
      (t : S ⊢ s') (x/t : S ∋/⊢[ 𝕂₂ ] s) →
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ ⦅ x/t ⦆ ≡ t
  wk-cancels-⦅⦆ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t x/t =
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ ⦅ x/t ⦆     ≡⟨ ~-cong-⋯ (t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id) (⦅⦆-,ₖ x/t) ⟩
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (id ,ₖ x/t) ≡⟨ wk-cancels-,ₖ t id x/t ⟩
    t ⋯ id                                ≡⟨ ⋯-id t ⟩
    t                                     ∎

  wkᵣ-cancels-⦅⦆ᵣ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (x : S ∋ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ ⦅ x ⦆ᵣ ≡ t
  wkᵣ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkᵣ-cancels-⦅⦆ₛ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (t' : S ⊢ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ ⦅ t' ⦆ₛ ≡ t
  wkᵣ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ᵣ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (x : S ∋ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ ⦅ x ⦆ᵣ ≡ t
  wkₛ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ₛ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (t' : S ⊢ s) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ ⦅ t' ⦆ₛ ≡ t
  wkₛ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  -- -- special case of 
  -- --   dist-,ₖ-·ʳ : ∀ {s}
  -- --                  (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
  -- --                  (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
  -- --                  (x/t : S₃ ∋/⊢[ 𝕂₂ ] s)
  -- --                → ((ϕ₁ ·ₖ ϕ₂) ,ₖ' x/t) ~ ((ϕ₁ ↑ s) ·ₖ (ϕ₂ ,ₖ x/t))
  -- ↑∘⦅⦆-is-,ₖ :
  --   ∀ ⦃ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂 𝕂 𝕂 ⦄ {S₁ S₂ s}
  --     (x/t : S₂ ∋/⊢[ 𝕂 ] s)
  --     (ϕ : S₁ –[ 𝕂 ]→ S₂)
  --   → ((ϕ ↑ s) ·ₖ ⦅ x/t ⦆) ~ (ϕ ,ₖ x/t)
  -- ↑∘⦅⦆-is-,ₖ ⦃ 𝕂 ⦄ ⦃ C ⦄ {S₁} {S₂} {s} x/t ϕ =
  --     ((ϕ ↑ s) ·ₖ ⦅ x/t ⦆)     ~⟨ {!!} ⟩
  --     ((ϕ ↑ s) ·ₖ (id ,ₖ x/t)) ~⟨ {!!} ⟩
  --     (ϕ ,ₖ x/t)               ~∎

  -- -- ↑∘⦅⦆-is-,ₛ : ∀ {S₁ S₂ s} (t : S₂ ⊢ s) (σ : S₁ →ₛ S₂) →
  -- --   ⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ s) ~ σ ,ₛ t
  -- -- ↑∘⦅⦆-is-,ₛ t σ _ (here refl) = ⋯-var (here refl) ⦅ t ⦆
  -- -- ↑∘⦅⦆-is-,ₛ t σ _ (there x)   = wk-cancels-⦅⦆ₛ (σ _ x) t

  -- ↑∘⦅⦆-is-,ₛ :
  --   ∀ {S₁ S₂ s}
  --     (t : S₂ ⊢ s)
  --     (ϕ : S₁ →ₛ S₂)
  --   → ((ϕ ↑ s) ·ₖ ⦅ t ⦆) ~ (ϕ ,ₖ t)
  -- ↑∘⦅⦆-is-,ₛ = ↑∘⦅⦆-is-,ₖ

  -- ⋯↑⋯⦅⦆-is-⋯,ₖ :
  --   ∀ ⦃ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂 𝕂 𝕂 ⦄ {S₁ S₂ s}
  --     (t : (S₁ ▷ s) ⊢ s)
  --     (x/t : S₂ ∋/⊢[ 𝕂 ] s)
  --     (ϕ : S₁ –[ 𝕂 ]→ S₂)
  --   → t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t ⦆ ≡ t ⋯ (ϕ ,ₖ x/t)
  -- ⋯↑⋯⦅⦆-is-⋯,ₖ {s = s} t x/t ϕ =
  --   t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t ⦆    ≡⟨ ⋯-assoc t (ϕ ↑ s) ⦅ x/t ⦆ ⟩
  --   t ⋯ ((ϕ ↑ s) ·ₖ ⦅ x/t ⦆) ≡⟨ ~-cong-⋯ t (↑∘⦅⦆-is-,ₖ x/t ϕ) ⟩
  --   t ⋯ (ϕ ,ₖ x/t)           ∎

  -- ⋯↑⋯⦅⦆-is-⋯,ₛ :
  --   ∀ {S₁ S₂ s}
  --     (t : (S₁ ▷ s) ⊢ s)
  --     (t' : S₂ ⊢ s)
  --     (ϕ : S₁ →ₛ S₂)
  --   → t ⋯ (ϕ ↑ s) ⋯ ⦅ t' ⦆ ≡ t ⋯ (ϕ ,ₖ t')
  -- ⋯↑⋯⦅⦆-is-⋯,ₛ = ⋯↑⋯⦅⦆-is-⋯,ₖ
