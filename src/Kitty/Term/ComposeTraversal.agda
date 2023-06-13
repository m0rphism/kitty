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
  _ = Kᵣ
  _ = Kₛ
  _ = Cᵣ
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
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
        ⦃ W₁ : KitT K₁ ⦄
        ⦃ W₂ : KitT K₂ ⦄
        ⦃ W₁₂ : KitT K ⦄
        ⦃ 𝔸 : ComposeKit K₁ K₂ K ⦄
        (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
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
    wk* [] t     ≡⟨⟩
    t            ≡⟨ sym (⋯-id t) ⟩
    t ⋯ᵣ id      ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-[] id)) ⟩
    t ⋯ᵣ wkn* [] ∎
  wk*-wkₖ* {S} {s} t (S' ▷ s') =
    wk* (S' ▷ s') t                ≡⟨⟩
    wk s' (wk* S' t)               ≡⟨ cong (wk s') (wk*-wkₖ* t S') ⟩
    wk s' (t ⋯ᵣ wkₖ* S' id)        ≡⟨⟩
    t ⋯ᵣ wkₖ* S' id ⋯ᵣ wkₖ s' id   ≡⟨ ⋯-assoc t (wkₖ* S' id) (wkₖ s' id) ⟩
    t ⋯ᵣ (wkₖ* S' id ·ₖ wkₖ s' id) ≡⟨ ~-cong-⋯ t (~-sym (wk-ϕ-id (wkₖ* S' id))) ⟩
    t ⋯ᵣ wkₖ s' (wkₖ* S' id)       ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-▷ S' s' id)) ⟩
    t ⋯ᵣ wkₖ* (S' ▷ s') id         ∎

  dist-↑-f :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit K₁ K₂ K ⦄
      ⦃ C₂ : ComposeKit K₂ K₁ K ⦄
      ⦃ W₁ : KitT K₁ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      ⦃ W₁₂ : KitT K ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ K₁ ]→ S₂)
    → t ⋯ wkn ⦃ K = K₂ ⦄ ⋯ (ϕ ↑ s) ≡ t ⋯ ϕ ⋯ wkn ⦃ K = K₂ ⦄
  dist-↑-f ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₁⊔K₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t ϕ =
    (t ⋯ wkn) ⋯ (ϕ ↑ _)       ≡⟨ ⋯-assoc t wkn (ϕ ↑ _)  ⟩
    t ⋯ (wkn ·[ C₂ ] (ϕ ↑ _)) ≡⟨ ~-cong-⋯ t (~-sym (↑-wk ϕ _)) ⟩
    t ⋯ (ϕ ·[ C₁ ] wkn)       ≡⟨ sym (⋯-assoc t ϕ wkn) ⟩
    (t ⋯ ϕ) ⋯ wkn             ∎

  -- &/⋯-assoc' :
  --   ∀ ⦃ K₁ K₂ K₃ K₁₂ K₂₃ K₁₂,₃ K₁,₂₃ ⦄
  --     ⦃ C₁₂ : ComposeKit K₁ K₂ K₁₂ ⦄
  --     ⦃ C₁₂,₃ : ComposeKit K₁₂ K₃ K₁₂,₃ ⦄
  --     ⦃ C₂₃ : ComposeKit K₂ K₃ K₂₃ ⦄
  --     ⦃ C₁,₂₃ : ComposeKit K₁ K₂₃ K₁,₂₃ ⦄
  --     {S₁ S₂ S₃} {s} 
  --     (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₃ ]→ S₃) →
  --   `/id ((x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂) ≡ `/id (x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂))
  -- &/⋯-assoc' = ?

  -- &/⋯-assoc :
  --   ∀ ⦃ K₁ K₂ K₃ K₁₂ K₂₃ K₁₂₃ ⦄
  --     ⦃ C₁₂ : ComposeKit K₁ K₂ K₁₂ ⦄
  --     ⦃ C₁₂,₃ : ComposeKit K₁₂ K₃ K₁₂₃ ⦄
  --     ⦃ C₂₃ : ComposeKit K₂ K₃ K₂₃ ⦄
  --     ⦃ C₁,₂₃ : ComposeKit K₁ K₂₃ K₁₂₃ ⦄
  --     {S₁ S₂ S₃} {s} 
  --     (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₃ ]→ S₃) →
  --   (x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂ ≡ x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂)
  -- &/⋯-assoc = ?

  ·-assoc :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢₃_ : VarScoped} ⦃ K₃ : Kit _∋/⊢₃_ ⦄
      {_∋/⊢₁₂_ : VarScoped} ⦃ K₁₂ : Kit _∋/⊢₁₂_ ⦄
      {_∋/⊢₂₃_ : VarScoped} ⦃ K₂₃ : Kit _∋/⊢₂₃_ ⦄
      {_∋/⊢₁₂,₃_ : VarScoped} ⦃ K₁₂,₃ : Kit _∋/⊢₁₂,₃_ ⦄
      {_∋/⊢₁,₂₃_ : VarScoped} ⦃ K₁,₂₃ : Kit _∋/⊢₁,₂₃_ ⦄
      ⦃ W₁ : KitT K₁ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      ⦃ W₃ : KitT K₃ ⦄
      ⦃ W₁₂ : KitT K₁₂ ⦄
      ⦃ W₂₃ : KitT K₂₃ ⦄
      ⦃ W₁₂,₃ : KitT K₁₂,₃ ⦄
      ⦃ W₁,₂₃ : KitT K₁,₂₃ ⦄
      ⦃ C₁₂ : ComposeKit K₁ K₂ K₁₂ ⦄
      ⦃ C₁₂,₃ : ComposeKit K₁₂ K₃ K₁₂,₃ ⦄
      ⦃ C₂₃ : ComposeKit K₂ K₃ K₂₃ ⦄
      ⦃ C₁,₂₃ : ComposeKit K₁ K₂₃ K₁,₂₃ ⦄
      {S₁} {S₂} {S₃} {S₄}
      (ϕ₁ : S₁ –[ K₁ ]→ S₂)
      (ϕ₂ : S₂ –[ K₂ ]→ S₃)
      (ϕ₃ : S₃ –[ K₃ ]→ S₄)
    → ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃) ~ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))
  ·-assoc ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₃ ⦄ ⦃ K₁₂ ⦄ ⦃ K₂₃ ⦄ ⦃ K₁₂,₃ ⦄ ⦃ K₁,₂₃ ⦄ ⦃ C₁₂ ⦄ ⦃ C₁₂,₃ ⦄ ⦃ C₂₃ ⦄ ⦃ C₁,₂₃ ⦄
          {S₁} {S₂} {S₃} {S₄} ϕ₁ ϕ₂ ϕ₃ = mk-~ λ s x →
    `/id (x & ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃))                     ≡⟨ sym (⋯-var x ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)) ⟩
    ` x ⋯ ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)                          ≡⟨ sym (⋯-assoc (` x) (ϕ₁ ·ₖ ϕ₂) ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ ϕ₂) ⋯ ϕ₃                             ≡⟨ sym (cong (_⋯ ϕ₃) (⋯-assoc (` x) ϕ₁ ϕ₂)) ⟩
    ` x ⋯ ϕ₁ ⋯ ϕ₂ ⋯ ϕ₃                                ≡⟨ ⋯-assoc (` x ⋯ ϕ₁) ϕ₂ ϕ₃ ⟩
    ` x ⋯ ϕ₁ ⋯ (ϕ₂ ·ₖ ϕ₃)                             ≡⟨ ⋯-assoc (` x) ϕ₁ (ϕ₂ ·ₖ ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))                          ≡⟨ ⋯-var x (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)) ⟩
    `/id (x & (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)))                     ∎

  ↑*-wk* :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit K₁ K₂ K ⦄
      ⦃ C₂ : ComposeKit K₂ K₁ K ⦄
      ⦃ C₁₁ : ComposeKit K₁ K₁ K₁ ⦄
      ⦃ C₂₂ : ComposeKit K₂ K₂ K₂ ⦄
      ⦃ C₃₃ : ComposeKit K K K ⦄
      ⦃ Cx₁ : ComposeKit K K₂ K ⦄
      ⦃ Cx₂ : ComposeKit K₂ K K ⦄
      ⦃ W₁ : KitT K₁ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      ⦃ W  : KitT K ⦄
      {S₁} {S₂} (ϕ : S₁ –[ K₁ ]→ S₂) S
    → (ϕ ·[ C₁ ] wkn* S) ~ (wkn* S ·[ C₂ ] (ϕ ↑* S))
  ↑*-wk* ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₁⊔K₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {S₁ = S₁} {S₂} ϕ [] =
    (ϕ ·[ C₁ ] wkn* [])         ~⟨ ~-cong-· ~-refl (wkₖ*-[] id) ⟩
    (ϕ ·[ C₁ ] id)              ~⟨ ·-idʳ ϕ ⟩
    ϕ                           ~⟨ ~-sym (·-idˡ ϕ) ⟩
    (id ·[ C₂ ] ϕ)              ~⟨ ~-sym (~-cong-· (wkₖ*-[] id) (↑*-[] ϕ)) ⟩
    (wkn* [] ·[ C₂ ] (ϕ ↑* [])) ~∎
  ↑*-wk* ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₁⊔K₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₁₁ ⦄ ⦃ C₂₂ ⦄ ⦃ C₃₃ ⦄ ⦃ Cx₁ ⦄ ⦃ Cx₂ ⦄ {S₁ = S₁} {S₂} ϕ (S ▷ s) =
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
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K₁⊔K₂ : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit K₁ K₂ K₁⊔K₂ ⦄
      ⦃ C₂ : ComposeKit K₂ K₁ K₁⊔K₂ ⦄
      ⦃ C₁₁ : ComposeKit K₁ K₁ K₁ ⦄
      ⦃ C₂₂ : ComposeKit K₂ K₂ K₂ ⦄
      ⦃ C₃₃ : ComposeKit K₁⊔K₂ K₁⊔K₂ K₁⊔K₂ ⦄
      ⦃ Cx₁ : ComposeKit K₁⊔K₂ K₂ K₁⊔K₂ ⦄
      ⦃ Cx₂ : ComposeKit K₂ K₁⊔K₂ K₁⊔K₂ ⦄
      ⦃ W₁ : KitT K₁ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      ⦃ W₁₂ : KitT K₁⊔K₂ ⦄
      (t : S₁ ⊢ s) (ϕ : S₁ –[ K₁ ]→ S₂)
    → t ⋯ wkₖ* ⦃ K = K₂ ⦄ S id ⋯ (ϕ ↑* S) ≡ t ⋯ ϕ ⋯ wkₖ* ⦃ K = K₂ ⦄ S id
  dist-↑*-f {S = S} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K₁⊔K₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t ϕ =
    (t ⋯ wkₖ* S id) ⋯ (ϕ ↑* S)       ≡⟨ ⋯-assoc t (wkₖ* S id) (ϕ ↑* S)  ⟩
    t ⋯ (wkₖ* S id ·[ C₂ ] (ϕ ↑* S)) ≡⟨ ~-cong-⋯ t (~-sym (↑*-wk* ϕ S)) ⟩
    t ⋯ (ϕ ·[ C₁ ] wkₖ* S id)        ≡⟨ sym (⋯-assoc t ϕ (wkₖ* S id)) ⟩
    (t ⋯ ϕ) ⋯ wkₖ* S id              ∎

  dist-↑-⦅⦆-· :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄ 
      ⦃ W₁ : KitT K₁ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      ⦃ W : KitT K ⦄
      ⦃ C₁ : ComposeKit K₁ K₂ K ⦄
      ⦃ C₂ : ComposeKit K₂ K K ⦄
      ⦃ C₃ : ComposeKit K₂ K₂ K₂ ⦄
      {S₁ S₂ s} (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
    (⦅ x/t ⦆ ·[ C₁ ] ϕ) ~ ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)
  dist-↑-⦅⦆-· ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {S₁} {S₂} {s} x/t ϕ = mk-~ λ where
    sx x@(here refl) →
      `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                        ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
      `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                              ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (use-~-hom (⦅⦆-,ₖ x/t) _ x) ⟩
      `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                          ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (&-,ₖ-here id x/t) ⟩
      `/id (x/t &/⋯ ϕ)                                      ≡⟨ ι-`/id (x/t &/⋯ ϕ) ⟩
      `/id (ι-∋/⊢ (x/t &/⋯ ϕ))                              ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (sym (&-,ₖ-here id (x/t &/⋯[ C₁ ] ϕ))) ⟩
      `/id (ι-∋/⊢ (here refl & (id ⦃ K = K ⦄ ,ₖ (x/t &/⋯[ C₁ ] ϕ))))
                                                            ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■))
                                                                    (sym (use-~-hom (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ)) _ (here refl))) ⟩
      `/id (ι-∋/⊢ (here refl & ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))        ≡⟨ cong `/id (sym (&/⋯-& ⦃ C₂ ⦄ (here refl) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) ⟩
      `/id ⦃ K ⦄ (id/` (here refl) &/⋯[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) (sym (&-↑-here ϕ)) ⟩ 
      `/id (x & (ϕ ↑ s) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)            ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ ↑ s) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ x)) ⟩
      `/id (x & ((ϕ ↑ s) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))      ∎
    sx x@(there y) →
      `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                                ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
      `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                                      ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (use-~-hom (⦅⦆-,ₖ x/t) _ x) ⟩
      `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                                  ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-,ₖ-there id x/t y) ⟩
      `/id (y & id &/⋯[ C₁ ] ϕ)                                     ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-id y) ⟩
      `/id ⦃ K ⦄ (id/` y &/⋯ ϕ)                                     ≡⟨ cong (`/id ⦃ K ⦄) (&/⋯-& y ϕ) ⟩
      `/id (ι-∋/⊢ ⦃ K₂⊑K₁⊔K₂ ⦃ C₁ ⦄ ⦄ (y & ϕ))                      ≡⟨ cong (`/id ⦃ K ⦄) (sym (&-ι-→ ⦃ K₁⊑K₂ = K₂⊑K₁⊔K₂ ⦃ C₁ ⦄ ⦄ ϕ y)) ⟩
      `/id (y & (ι-→ ⦃ K₁⊑K₂ = K₂⊑K₁⊔K₂ ⦃ C₁ ⦄ ⦄ ϕ))                ≡⟨ use-~ (~-ι-→ ⦃ K₁⊑K₂ = K₂⊑K₁⊔K₂ ⦃ C₁ ⦄ ⦄ ϕ) _ y ⟩

      `/id (y & ϕ)                                                  ≡⟨ sym (use-~ (·-idʳ ϕ) _ y) ⟩
      `/id (y & (ϕ ·[ C₂ ] id))                                     ≡⟨ use-~ (~-cong-· ~-refl
                                                                        (~-sym (wk-cancels-,ₖ-· id (x/t &/⋯[ C₁ ] ϕ)))) _ y ⟩
      `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] (id ,ₖ (x/t &/⋯[ C₁ ] ϕ))))) ≡⟨ use-~ (~-cong-· ⦃ K₁ = K₂ ⦄ ⦃ K₂ = K ⦄ ⦃ K = K ⦄ ~-refl
                                                                            (~-cong-· ⦃ K₁ = K₂ ⦄ ⦃ K₂ = K ⦄ ⦃ K = K ⦄ ~-refl (~-sym (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ))))) _ y ⟩
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
    ∀ {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W : KitT K ⦄ {st} {s : Sort st} {t₁ t₂ : S₁ ⊢ s}
      {ϕ₁ ϕ₂ : S₁ –[ K ]→ S₂}
    → t₁ ≡ t₂
    → ϕ₁ ~ ϕ₂
    → t₁ ⋯ ϕ₁ ≡ t₂ ⋯ ϕ₂
  ~-cong-&/⋯ₛ refl ϕ₁~ϕ₂ = ~-cong-⋯ _ ϕ₁~ϕ₂

  &/⋯-wk-↑ₛ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K Kᵣ K ⦄
      {S₁} {S₂} {st} {s} {sx : Sort st}
      (t : S₁ ⊢ sx)
      (ϕ : S₁ –[ K ]→ S₂)
    → t ⋯ ϕ ⋯ wknᵣ ≡ t ⋯ wknᵣ ⋯ (ϕ ↑ s)
  &/⋯-wk-↑ₛ {_} {S₁} {S₂} {st} {s} {sx} t ϕ =
    t ⋯ ϕ ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id          ≡⟨ ⋯-assoc t ϕ (wkₖ ⦃ K = Kᵣ ⦄ _ id) ⟩
    t ⋯ (ϕ ·ₖ wkₖ ⦃ K = Kᵣ ⦄ _ id)       ≡⟨ ~-cong-⋯ t (↑-wk ϕ _) ⟩
    t ⋯ (wkₖ ⦃ K = Kᵣ ⦄ _ id ·ₖ (ϕ ↑ s)) ≡⟨ sym (⋯-assoc t (wkₖ ⦃ K = Kᵣ ⦄ _ id) (ϕ ↑ s)) ⟩
    t ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id ⋯ (ϕ ↑ s)    ∎

  Cₛ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K Kᵣ K ⦄ → ComposeKit Kₛ K Kₛ
  Cₛ ⦃ K ⦄ ⦃ C ⦄ = record
    { K₁⊑K₁⊔K₂  = ⊑ₖ-refl ⦃ Kₛ ⦄
    ; K₂⊑K₁⊔K₂  = ⊑ₖ-⊤ ⦃ K ⦄
    ; _&/⋯_      = _⋯_
    ; &/⋯-⋯      = λ x/t ϕ → refl
    ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ ⦃ K ⦄ ⦃ C ⦄
    ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
    }

  private instance _ = Cₛ

  Cₛᵣ : ComposeKit Kₛ Kᵣ Kₛ
  Cₛᵣ = Cₛ

  Cₛₛ : ComposeKit Kₛ Kₛ Kₛ
  Cₛₛ = Cₛ

  -- infixl  9  _ₛ·_  _ₛ·ᵣ_  _ₛ·ₛ_
  -- infixr  9  _∘ₛ_  _ᵣ∘ₛ_  _ₛ∘ₛ_
  infixl  9  _ₛ·ᵣ_  _ₛ·ₛ_
  infixr  9  _ᵣ∘ₛ_  _ₛ∘ₛ_

  _ₛ·_ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K Kᵣ K ⦄
           {S₁} {S₂} {S₃} → S₁ –[ Kₛ ]→ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ Kₛ ]→ S₃
  σ ₛ· ϕ = σ ·ₖ ϕ

  _∘ₛ_ : ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ ⦃ C : ComposeKit K Kᵣ K ⦄
           {S₁} {S₂} {S₃} → S₂ –[ K ]→ S₃ → S₁ –[ Kₛ ]→ S₂ → S₁ –[ Kₛ ]→ S₃
  ϕ₂ ∘ₛ ϕ₁ = ϕ₁ ₛ· ϕ₂

  _ₛ·ᵣ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ Kₛ ]→ S₂ → S₂ –[ Kᵣ ]→ S₃ → S₁ –[ Kₛ ]→ S₃
  _ₛ·ₛ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ Kₛ ]→ S₂ → S₂ –[ Kₛ ]→ S₃ → S₁ –[ Kₛ ]→ S₃
  _ᵣ∘ₛ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ Kᵣ ]→ S₃ → S₁ –[ Kₛ ]→ S₂ → S₁ –[ Kₛ ]→ S₃
  _ₛ∘ₛ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ Kₛ ]→ S₃ → S₁ –[ Kₛ ]→ S₂ → S₁ –[ Kₛ ]→ S₃
  _ₛ·ᵣ_ = _·ₖ_
  _ₛ·ₛ_ = _·ₖ_
  _ᵣ∘ₛ_ = _∘ₖ_
  _ₛ∘ₛ_ = _∘ₖ_

--   ∘~∘→⋯≡⋯ : ∀ {{K₁ K₂ K₁' K₂' K : Kit}}
--               {{𝔸  : ComposeKit K₁  K₂  K}}
--               {{𝔸' : ComposeKit K₁' K₂' K}}
--               {ϕ₁  : S₁ –[ K₁  ]→ S₂ } {ϕ₂  : S₂  –[ K₂  ]→ S₃}
--               {ϕ₁' : S₁ –[ K₁' ]→ S₂'} {ϕ₂' : S₂' –[ K₂' ]→ S₃} →
--     (ϕ₁ ·[ 𝔸 ] ϕ₂) ~ (ϕ₁' ·[ 𝔸' ] ϕ₂') →
--     ∀ {s} (t : S₁ ⊢ s) →
--     t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
--   ∘~∘→⋯≡⋯ ⦃ 𝔸 = 𝔸 ⦄ ⦃ 𝔸' ⦄ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
--     t ⋯ ϕ₁ ⋯ ϕ₂         ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
--     t ⋯ ϕ₁  ·[ 𝔸  ] ϕ₂  ≡⟨ ~-cong-⋯ t eq ⟩
--     t ⋯ ϕ₁' ·[ 𝔸' ] ϕ₂' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
--     t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

  wk-cancels-,ₖ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄ ⦃ W : KitT K ⦄
      ⦃ C : ComposeKit K₁ K₂ K ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ K₂ ]→ S₂) (x/t : S₂ ∋/⊢[ K₂ ] s)
    → t ⋯ wkn ⦃ K = K₁ ⦄ ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wk-cancels-,ₖ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ C = C ⦄ t ϕ x/t =
    t ⋯ wkn ⦃ K = K₁ ⦄ ⋯ (ϕ ,ₖ x/t)        ≡⟨ ⋯-assoc ⦃ 𝔸 = C ⦄ t (wkₖ _ id) (ϕ ,ₖ x/t) ⟩
    t ⋯ (wkn ⦃ K = K₁ ⦄ ·[ C ] (ϕ ,ₖ x/t)) ≡⟨ ~-cong-⋯ _ (wk-cancels-,ₖ-· ⦃ C = C ⦄ ϕ x/t) ⟩
    t ⋯ ϕ                                  ∎

  wkᵣ-cancels-,ₖ :
    ∀ {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ W₂ : KitT K₂ ⦄
      (t : S₁ ⊢ s') (ϕ : S₁ –[ K₂ ]→ S₂) (x/t : S₂ ∋/⊢[ K₂ ] s) →
    t ⋯ wknᵣ ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₖ = wk-cancels-,ₖ ⦃ C = Cᵣ ⦄

  wkᵣ-cancels-,ᵣ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ᵣ S₂) (x : S₂ ∋ s) →
    t ⋯ wknᵣ ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ᵣ = wk-cancels-,ₖ ⦃ C = Cᵣ ⦄

  wkᵣ-cancels-,ₛ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ₛ S₂) (t' : S₂ ⊢ s) →
    t ⋯ wknᵣ ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₛ = wk-cancels-,ₖ ⦃ C = Cᵣ ⦄

  wkₛ-cancels-,ᵣ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ᵣ S₂) (x : S₂ ∋ s) →
    t ⋯ wknₛ ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkₛ-cancels-,ᵣ = wk-cancels-,ₖ ⦃ C = Cₛᵣ ⦄

  wkₛ-cancels-,ₛ :
    ∀ (t : S₁ ⊢ s') (ϕ : S₁ →ₛ S₂) (t' : S₂ ⊢ s) →
    t ⋯ wknₛ ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkₛ-cancels-,ₛ = wk-cancels-,ₖ ⦃ C = Cₛₛ ⦄

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
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄ ⦃ W : KitT K ⦄ 
      ⦃ C₁ : ComposeKit K₁ K₂ K ⦄
      ⦃ C₂ : ComposeKit K₂ K K ⦄
      ⦃ C₂ : ComposeKit K₂ K₂ K₂ ⦄
      {S₁ S₂ s} {st} {s' : Sort st}
      (t : (s ∷ S₁) ⊢ s') (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆
  dist-⦅⦆-⋯ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {S₁} {S₂} {s} {st} {s'} t x/t ϕ =
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
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W : KitT K ⦄
      ⦃ C₁ : ComposeKit Kₛ K Kₛ ⦄
      ⦃ C₂ : ComposeKit K Kₛ Kₛ ⦄
      ⦃ C₃ : ComposeKit K K K ⦄
      {S₁ S₂ s} {st} {s' : Sort st} 
      (t : (S₁ ▷ s) ⊢ s') (t' : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) →
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ
  dist-⦅⦆ₛ-⋯ ⦃ K ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {S₁} {S₂} {s} {st} {s'} t t' ϕ =
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ                   ≡⟨ dist-⦅⦆-⋯ ⦃ C₁ = C₁ ⦄ t t' ϕ ⟩
    t ⋯ (ϕ ↑ s) ⋯ ⦅ t' &/⋯[ C₁ ] ϕ ⦆ₛ ≡⟨ cong (λ ■ → t ⋯ ϕ ↑ s ⋯ ⦅ ■ ⦆ₛ) (&/⋯-⋯ ⦃ C₁ ⦄ t' ϕ) ⟩
    t ⋯ (ϕ ↑ s) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ         ∎

--   record ComposeTraversalLemmas : Set₁ where

  ⋯-idₛ : ∀ {S st} {s : Sort st} (t : S ⊢ s) → t ⋯ id ⦃ K = Kₛ ⦄ ≡ t
  ⋯-idᵣ : ∀ {S st} {s : Sort st} (t : S ⊢ s) → t ⋯ id ⦃ K = Kᵣ ⦄ ≡ t
  ⋯-idₛ = ⋯-id
  ⋯-idᵣ = ⋯-id

  -- -- TODO OLD: We can transfer this from ⋯-id if we extend ComposeKit with a lemma,
  -- -- that operations on terms determine operations on &/⋯
  -- -- We could go even further and say operations on &/⋯ and ⋯ are determined by
  -- -- operations on ap. Note that this is precisely what KitAltSimple does!!!!
  -- &/⋯-id :
  --   ∀ ⦃ K₁ K₂ K : Kit ⦄
  --     ⦃ C : ComposeKit K₁ K₂ K ⦄
  --     {S} {s/s} (x/t : S ∋/⊢[ K₁ ] s/s)
  --   → x/t &/⋯ id ⦃ K = K₂ ⦄ ≡ ι-∋/⊢ x/t
  -- &/⋯-id ⦃ K ⦄ {S} {s} x/t = {!!}

  wk-cancels-⦅⦆ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄ ⦃ KT : KitT K ⦄
      ⦃ C₁ : ComposeKit K₁ K₂ K ⦄
      ⦃ C₂ : ComposeKit K₂ K₁ K ⦄
      {S st} {s' : Sort st}
      (t : S ⊢ s') (x/t : S ∋/⊢[ K₂ ] s) →
    t ⋯ wkn ⦃ K = K₁ ⦄ ⋯ ⦅ x/t ⦆ ≡ t
  wk-cancels-⦅⦆ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t x/t =
    t ⋯ wkn ⦃ K = K₁ ⦄ ⋯ ⦅ x/t ⦆     ≡⟨ ~-cong-⋯ (t ⋯ wkn ⦃ K = K₁ ⦄) (⦅⦆-,ₖ x/t) ⟩
    t ⋯ wkn ⦃ K = K₁ ⦄ ⋯ (id ,ₖ x/t) ≡⟨ wk-cancels-,ₖ t id x/t ⟩
    t ⋯ id                           ≡⟨ ⋯-id t ⟩
    t                                ∎

  wkᵣ-cancels-⦅⦆ᵣ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (x : S ∋ s) →
    t ⋯ wknᵣ ⋯ ⦅ x ⦆ᵣ ≡ t
  wkᵣ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkᵣ-cancels-⦅⦆ₛ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (t' : S ⊢ s) →
    t ⋯ wknᵣ ⋯ ⦅ t' ⦆ₛ ≡ t
  wkᵣ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ᵣ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (x : S ∋ s) →
    t ⋯ wknₛ ⋯ ⦅ x ⦆ᵣ ≡ t
  wkₛ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ₛ : ∀ {S s} {st} {s' : Sort st} (t : S ⊢ s') (t' : S ⊢ s) →
    t ⋯ wknₛ ⋯ ⦅ t' ⦆ₛ ≡ t
  wkₛ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  -- -- special case of 
  -- --   dist-,ₖ-·ʳ : ∀ {s}
  -- --                  (ϕ₁ : S₁ –[ K₁ ]→ S₂)
  -- --                  (ϕ₂ : S₂ –[ K₂ ]→ S₃)
  -- --                  (x/t : S₃ ∋/⊢[ K₂ ] s)
  -- --                → ((ϕ₁ ·ₖ ϕ₂) ,ₖ' x/t) ~ ((ϕ₁ ↑ s) ·ₖ (ϕ₂ ,ₖ x/t))
  -- ↑∘⦅⦆-is-,ₖ :
  --   ∀ ⦃ K ⦄ ⦃ C : ComposeKit K K K ⦄ {S₁ S₂ s}
  --     (x/t : S₂ ∋/⊢[ K ] s)
  --     (ϕ : S₁ –[ K ]→ S₂)
  --   → ((ϕ ↑ s) ·ₖ ⦅ x/t ⦆) ~ (ϕ ,ₖ x/t)
  -- ↑∘⦅⦆-is-,ₖ ⦃ K ⦄ ⦃ C ⦄ {S₁} {S₂} {s} x/t ϕ =
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
  --   ∀ ⦃ K ⦄ ⦃ C : ComposeKit K K K ⦄ {S₁ S₂ s}
  --     (t : (S₁ ▷ s) ⊢ s)
  --     (x/t : S₂ ∋/⊢[ K ] s)
  --     (ϕ : S₁ –[ K ]→ S₂)
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
