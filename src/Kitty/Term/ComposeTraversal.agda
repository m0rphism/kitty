open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
import Kitty.Term.Sub
import Kitty.Term.SubCompose

module Kitty.Term.ComposeTraversal
    {𝕄 : Modes}
    {𝕋 : Terms 𝕄}
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

open Modes 𝕄
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
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- ComposeTraversal ------------------------------------------------------------

-- If the client provides a `ComposeTraversal` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeTraversal : Set (lsuc ℓ) where
  field
    ⋯-assoc :
      ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ : Kit ⦄
        ⦃ W₁ : KitT 𝕂₁ ⦄
        ⦃ W₂ : KitT 𝕂₂ ⦄
        ⦃ W₁₂ : KitT 𝕂₁⊔𝕂₂ ⦄
        ⦃ 𝔸 : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
        (t : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
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
      ∀ (t : µ ⊢ M) µ' →
      wk* µ' t ≡ t ⋯ᵣ wkₖ* µ' id
  wk*-wkₖ* {µ} {M} t [] =
    wk* [] t        ≡⟨⟩
    t               ≡⟨ sym (⋯-id t) ⟩
    t ⋯ᵣ id         ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-[] id)) ⟩
    t ⋯ᵣ wkₖ* [] id ∎
  wk*-wkₖ* {µ} {M} t (µ' ▷ m') =
    wk* (µ' ▷ m') t                ≡⟨⟩
    wk m' (wk* µ' t)               ≡⟨ cong (wk m') (wk*-wkₖ* t µ') ⟩
    wk m' (t ⋯ᵣ wkₖ* µ' id)        ≡⟨⟩
    t ⋯ᵣ wkₖ* µ' id ⋯ᵣ wkₖ m' id   ≡⟨ ⋯-assoc t (wkₖ* µ' id) (wkₖ m' id) ⟩
    t ⋯ᵣ (wkₖ* µ' id ·ₖ wkₖ m' id) ≡⟨ ~-cong-⋯ t (~-sym (wk-ϕ-id (wkₖ* µ' id))) ⟩
    t ⋯ᵣ wkₖ m' (wkₖ* µ' id)       ≡⟨ ~-cong-⋯ t (~-sym (wkₖ*-▷ µ' m' id)) ⟩
    t ⋯ᵣ wkₖ* (µ' ▷ m') id         ∎

  dist-↑-f :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂₁⊔𝕂₂ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W₁₂ : KitT 𝕂₁⊔𝕂₂ ⦄
      (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → t ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id ⋯ (ϕ ↑ m) ≡ t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ _ id
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
  --     {µ₁ µ₂ µ₃} {M} 
  --     (x/t : µ₁ ∋/⊢[ 𝕂₁ ] M) (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₃ ]→ µ₃) →
  --   `/id ((x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂) ≡ `/id (x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂))
  -- &/⋯-assoc' = ?

  -- &/⋯-assoc :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ 𝕂₁₂ 𝕂₂₃ 𝕂₁₂₃ ⦄
  --     ⦃ C₁₂ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁₂ ⦄
  --     ⦃ C₁₂,₃ : ComposeKit 𝕂₁₂ 𝕂₃ 𝕂₁₂₃ ⦄
  --     ⦃ C₂₃ : ComposeKit 𝕂₂ 𝕂₃ 𝕂₂₃ ⦄
  --     ⦃ C₁,₂₃ : ComposeKit 𝕂₁ 𝕂₂₃ 𝕂₁₂₃ ⦄
  --     {µ₁ µ₂ µ₃} {M} 
  --     (x/t : µ₁ ∋/⊢[ 𝕂₁ ] M) (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₃ ]→ µ₃) →
  --   (x/t &/⋯[ C₁₂ ] ϕ₁) &/⋯[ C₁₂,₃ ] ϕ₂ ≡ x/t &/⋯[ C₁,₂₃ ] (ϕ₁ ·[ C₂₃ ] ϕ₂)
  -- &/⋯-assoc = ?

  ·-assoc :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₃ 𝕂₁₂ 𝕂₂₃ 𝕂₁₂,₃ 𝕂₁,₂₃ ⦄
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
      {µ₁} {µ₂} {µ₃} {µ₄}
      (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
      (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
      (ϕ₃ : µ₃ –[ 𝕂₃ ]→ µ₄)
    → ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃) ~ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))
  ·-assoc ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₃ ⦄ ⦃ 𝕂₁₂ ⦄ ⦃ 𝕂₂₃ ⦄ ⦃ 𝕂₁₂,₃ ⦄ ⦃ 𝕂₁,₂₃ ⦄ ⦃ C₁₂ ⦄ ⦃ C₁₂,₃ ⦄ ⦃ C₂₃ ⦄ ⦃ C₁,₂₃ ⦄
          {µ₁} {µ₂} {µ₃} {µ₄} ϕ₁ ϕ₂ ϕ₃ m x =
    `/id (x & ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃))                     ≡⟨ sym (⋯-var x ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)) ⟩
    ` x ⋯ ((ϕ₁ ·ₖ ϕ₂) ·ₖ ϕ₃)                          ≡⟨ sym (⋯-assoc (` x) (ϕ₁ ·ₖ ϕ₂) ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ ϕ₂) ⋯ ϕ₃                             ≡⟨ sym (cong (_⋯ ϕ₃) (⋯-assoc (` x) ϕ₁ ϕ₂)) ⟩
    ` x ⋯ ϕ₁ ⋯ ϕ₂ ⋯ ϕ₃                                ≡⟨ ⋯-assoc (` x ⋯ ϕ₁) ϕ₂ ϕ₃ ⟩
    ` x ⋯ ϕ₁ ⋯ (ϕ₂ ·ₖ ϕ₃)                             ≡⟨ ⋯-assoc (` x) ϕ₁ (ϕ₂ ·ₖ ϕ₃) ⟩
    ` x ⋯ (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃))                          ≡⟨ ⋯-var x (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)) ⟩
    `/id (x & (ϕ₁ ·ₖ (ϕ₂ ·ₖ ϕ₃)))                     ∎

  ↑*-wk* :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂₁⊔𝕂₂ ⦄
      ⦃ C₁₁ : ComposeKit 𝕂₁ 𝕂₁ 𝕂₁ ⦄
      ⦃ C₂₂ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      ⦃ C₃₃ : ComposeKit 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ Cx₁ : ComposeKit 𝕂₁⊔𝕂₂ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ Cx₂ : ComposeKit 𝕂₂ 𝕂₁⊔𝕂₂ 𝕂₁⊔𝕂₂ ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W  : KitT 𝕂₁⊔𝕂₂ ⦄
      {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) µ
    → (ϕ ·[ C₁ ] wkₖ* µ id) ~ (wkₖ* µ id ·[ C₂ ] (ϕ ↑* µ))
  ↑*-wk* ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁ = µ₁} {µ₂} ϕ [] =
    (ϕ ·[ C₁ ] wkₖ* [] id)         ~⟨ ~-cong-· ~-refl (wkₖ*-[] id) ⟩
    (ϕ ·[ C₁ ] id)                 ~⟨ ·-idʳ ϕ ⟩
    ϕ                              ~⟨ ~-sym (·-idˡ ϕ) ⟩
    (id ·[ C₂ ] ϕ)                 ~⟨ ~-sym (~-cong-· (wkₖ*-[] id) (↑*-[] ϕ)) ⟩
    (wkₖ* [] id ·[ C₂ ] (ϕ ↑* [])) ~∎
  ↑*-wk* ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₁₁ ⦄ ⦃ C₂₂ ⦄ ⦃ C₃₃ ⦄ ⦃ Cx₁ ⦄ ⦃ Cx₂ ⦄ {µ₁ = µ₁} {µ₂} ϕ (µ ▷ m) =
    (ϕ ·[ C₁ ] wkₖ* (µ ▷ m) id)                          ~⟨ ~-cong-· ~-refl (wkₖ*-▷ µ m id) ⟩
    (ϕ ·[ C₁ ] wkₖ m (wkₖ* µ id))                        ~⟨ ~-cong-· ~-refl (wk-ϕ-id (wkₖ* µ id)) ⟩
    (ϕ ·[ C₁ ] (wkₖ* µ id ·[ C₂₂ ] wkₖ m id))            ~⟨ ~-sym (·-assoc ϕ (wkₖ* µ id) (wkₖ m id)) ⟩
    ((ϕ ·[ C₁ ] wkₖ* µ id) ·[ Cx₁ ] wkₖ m id)            ~⟨ ~-cong-· (↑*-wk* ϕ µ) ~-refl ⟩
    ((wkₖ* µ id ·[ C₂ ] (ϕ ↑* µ)) ·[ Cx₁ ] wkₖ m id)     ~⟨ ·-assoc (wkₖ* µ id) (ϕ ↑* µ) (wkₖ m id)  ⟩
    (wkₖ* µ id ·[ Cx₂ ] ((ϕ ↑* µ) ·[ C₁ ] wkₖ m id))     ~⟨ ~-cong-· ~-refl (↑-wk (ϕ ↑* µ) m) ⟩
    (wkₖ* µ id ·[ Cx₂ ] (wkₖ m id ·[ C₂ ] (ϕ ↑* µ) ↑ m)) ~⟨ ~-sym (·-assoc (wkₖ* µ id) (wkₖ m id) ((ϕ ↑* µ) ↑ m)) ⟩
    ((wkₖ* µ id ·[ C₂₂ ] wkₖ m id) ·[ C₂ ] (ϕ ↑* µ) ↑ m) ~⟨ ~-cong-· (~-sym (wk-ϕ-id (wkₖ* µ id))) ~-refl ⟩
    (wkₖ m (wkₖ* µ id) ·[ C₂ ] ((ϕ ↑* µ) ↑ m))           ~⟨ ~-sym (~-cong-· (wkₖ*-▷ µ m id) (↑*-▷ µ m ϕ)) ⟩
    (wkₖ* (µ ▷ m) id ·[ C₂ ] (ϕ ↑* (µ ▷ m)))             ~∎

  dist-↑*-f :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂₁⊔𝕂₂ ⦄
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
      (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → t ⋯ wkₖ* ⦃ 𝕂 = 𝕂₂ ⦄ µ id ⋯ (ϕ ↑* µ) ≡ t ⋯ ϕ ⋯ wkₖ* ⦃ 𝕂 = 𝕂₂ ⦄ µ id
  dist-↑*-f {µ = µ} ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁⊔𝕂₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t ϕ =
    (t ⋯ wkₖ* µ id) ⋯ (ϕ ↑* µ)       ≡⟨ ⋯-assoc t (wkₖ* µ id) (ϕ ↑* µ)  ⟩
    t ⋯ (wkₖ* µ id ·[ C₂ ] (ϕ ↑* µ)) ≡⟨ ~-cong-⋯ t (~-sym (↑*-wk* ϕ µ)) ⟩
    t ⋯ (ϕ ·[ C₁ ] wkₖ* µ id)        ≡⟨ sym (⋯-assoc t ϕ (wkₖ* µ id)) ⟩
    (t ⋯ ϕ) ⋯ wkₖ* µ id              ∎

  dist-↑-⦅⦆-· :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ C₃ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      {µ₁ µ₂ m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    (⦅ x/t ⦆ ·[ C₁ ] ϕ) ~ ((ϕ ↑ m) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)
  dist-↑-⦅⦆-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@(here refl) =
    `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                        ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
    `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                              ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (~→~' (⦅⦆-,ₖ x/t) _ x) ⟩
    `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                          ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (&-,ₖ-here id x/t) ⟩
    `/id (x/t &/⋯ ϕ)                                      ≡⟨ ι-`/id (x/t &/⋯ ϕ) ⟩
    `/id (ι-∋/⊢ (x/t &/⋯ ϕ))                              ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (sym (&-,ₖ-here id (x/t &/⋯[ C₁ ] ϕ))) ⟩
    `/id (ι-∋/⊢ (here refl & (id ⦃ 𝕂 = 𝕂 ⦄ ,ₖ (x/t &/⋯[ C₁ ] ϕ))))
                                                          ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■))
                                                                  (sym (~→~' (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ)) _ (here refl))) ⟩
    `/id (ι-∋/⊢ (here refl & ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))        ≡⟨ cong `/id (sym (&/⋯-& ⦃ C₂ ⦄ (here refl) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) ⟩
    `/id ⦃ 𝕂 ⦄ (id/` (here refl) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) (sym (&-↑-here ϕ)) ⟩ 
    `/id (x & (ϕ ↑ m) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)            ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ ↑ m) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ x)) ⟩
    `/id (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))      ∎
  dist-↑-⦅⦆-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@(there y) =
    `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                                ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
    `/id (x & ⦅ x/t ⦆ &/⋯ ϕ)                                      ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (~→~' (⦅⦆-,ₖ x/t) _ x) ⟩
    `/id (x & (id ,ₖ x/t) &/⋯ ϕ)                                  ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-,ₖ-there id x/t y) ⟩
    `/id (y & id &/⋯[ C₁ ] ϕ)                                     ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C₁ ] ϕ)) (&-id y) ⟩
    `/id ⦃ 𝕂 ⦄ (id/` y &/⋯ ϕ)                                     ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (&/⋯-& y ϕ) ⟩
    `/id (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ (y & ϕ))                      ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (sym (&-ι-→ ϕ y)) ⟩
    `/id (y & (ι-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ ϕ))                ≡⟨ ~-ι-→ ϕ _ y ⟩
    `/id (y & ϕ)                                                  ≡⟨ sym (·-idʳ ϕ _ y) ⟩
    `/id (y & (ϕ ·[ C₂ ] id))                                     ≡⟨ ~-cong-· ~-refl
                                                                      (~-sym (wk-cancels-,ₖ-· id (x/t &/⋯[ C₁ ] ϕ))) _ y ⟩
    `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] (id ,ₖ (x/t &/⋯[ C₁ ] ϕ))))) ≡⟨ ~-cong-· ~-refl
                                                                           (~-cong-· ~-refl (~-sym (⦅⦆-,ₖ (x/t &/⋯[ C₁ ] ϕ)))) _ y ⟩
    `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))) ≡⟨ sym (·-assoc ϕ (wkₖ _ id) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ _ y) ⟩
    `/id (y & ((ϕ ·[ C₃ ] wkₖ _ id) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)) ≡⟨ ~-cong-· (~-sym (wk-ϕ-id ϕ)) ~-refl _ y ⟩
    `/id (y & (wkₖ _ ϕ ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))              ≡⟨ cong `/id
                                                                          (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (wkₖ _ ϕ) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ y) ⟩
    `/id (y & (wkₖ _ ϕ) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                  ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))
                                                                                       (&-wkₖ-wk ϕ y) ⟩
    `/id (wk _ (y & ϕ) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                   ≡⟨ cong (λ ■ → `/id (■ &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))
                                                                                       (sym (&-↑-there ϕ y)) ⟩ 
    `/id (x & (ϕ ↑ m) &/⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆)                    ≡⟨ cong `/id
                                                                       (sym (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (ϕ ↑ m) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆ x)) ⟩
    `/id (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆))              ∎

  -- ComposeKit for Substitutions ------------------------------------------------

  -- &/⋯-wk-↑ₛ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx}
  --               (t : µ₁ ⊢ mx)
  --               (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  --             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
  -- &/⋯-wk-↑ₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} t ϕ =
  --   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
  --   t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
  --   t ⋯ (ϕ ↑* []) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* [])       ≡⟨⟩
  --   t ⋯* (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ []) ↑** []        ≡⟨
  --     ⋯-↑ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ ϕ ∷ [])
  --         ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ [])
  --         (λ {µ'} x →
  --           ` x ⋯ (ϕ ↑* µ') ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')           ≡⟨ cong (_⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) (⋯-var x (ϕ ↑* µ')) ⟩
  --           `/id (x & (ϕ ↑* µ')) ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')       ≡⟨ {!!} ⟩
  --           `/id (x & (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ')) ⋯ ((ϕ ↑ m) ↑* µ') ≡⟨ cong (_⋯ ϕ ↑ m ↑* µ') (sym (⋯-var x (wkₖ _ id ↑* µ'))) ⟩
  --           ` x ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* µ') ⋯ ((ϕ ↑ m) ↑* µ')      ∎
  --         )
  --         t ⟩
  --   t ⋯* ((ϕ ↑ m) ∷ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ∷ []) ↑** []  ≡⟨⟩
  --   t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ↑* []) ⋯ ((ϕ ↑ m) ↑* []) ≡⟨ {!!} ⟩
  --   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)                 ≡⟨ {!!} ⟩
  --   wk _ t ⋯ (ϕ ↑ m)                                    ∎

  -- &/⋯-wk-↑ₛ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx}
  --               (t : µ₁ ⊢ mx)
  --               (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  --             → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
  -- &/⋯-wk-↑ₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} {mx} t ϕ =
  --   wk _ (t ⋯ ϕ)                                        ≡⟨ {!!} ⟩
  --   t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id                       ≡⟨ {!!} ⟩
  --   t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)                 ≡⟨ {!!} ⟩
  --   wk _ t ⋯ (ϕ ↑ m)                                    ∎

  -- ckitₛ : ∀ ⦃ 𝕂 ⦄ → ComposeKit kitₛ 𝕂 kitₛ
  -- ckitₛ ⦃ 𝕂 ⦄ = record
  --   { 𝕂₁⊑𝕂₁⊔𝕂₂  = ⊑ₖ-refl ⦃ kitₛ ⦄
  --   ; 𝕂₂⊑𝕂₁⊔𝕂₂  = ⊑ₖ-⊤ ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄
  --   ; _&/⋯_      = _⋯_
  --   ; &/⋯-⋯      = λ x/t ϕ → refl
  --   ; &/⋯-&      = &/⋯-&ₛ
  --   ; &/⋯-wk-↑   = &/⋯-wk-↑ₛ
  --   ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
  --   }

  -- TODO: generalize with ≡ₜ
  ~-cong-&/⋯ₛ :
    ∀ ⦃ 𝕂 ⦄ ⦃ W : KitT 𝕂 ⦄ {m} {t₁ t₂ : µ₁ ⊢ m→M m}
      {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂}
    → t₁ ≡ t₂
    → ϕ₁ ~ ϕ₂
    → t₁ ⋯ ϕ₁ ≡ t₂ ⋯ ϕ₂
  ~-cong-&/⋯ₛ refl ϕ₁~ϕ₂ = ~-cong-⋯ _ ϕ₁~ϕ₂

  &/⋯-wk-↑ₛᵣ :
    ∀ {µ₁} {µ₂} {m} {mx}
      (t : µ₁ ⊢ mx)
      (ϕ : µ₁ –[ kitᵣ ]→ µ₂)
    → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
  &/⋯-wk-↑ₛᵣ {µ₁} {µ₂} {m} {mx} t ϕ =
    wk _ (t ⋯ ϕ)                           ≡⟨ refl ⟩
    t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id          ≡⟨ ⋯-assoc t ϕ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) ⟩
    t ⋯ (ϕ ·ₖ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id)       ≡⟨ ~-cong-⋯ t (↑-wk ϕ _) ⟩
    t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ·ₖ (ϕ ↑ m)) ≡⟨ sym (⋯-assoc t (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) (ϕ ↑ m)) ⟩
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)    ≡⟨ refl ⟩
    wk _ t ⋯ (ϕ ↑ m)                       ∎

  ckitₛᵣ : ComposeKit kitₛ kitᵣ kitₛ
  ckitₛᵣ = record
    { 𝕂₁⊑𝕂₁⊔𝕂₂  = ⊑ₖ-refl ⦃ kitₛ ⦄
    ; 𝕂₂⊑𝕂₁⊔𝕂₂  = ⊑ₖ-⊤ ⦃ kitᵣ ⦄
    ; _&/⋯_      = _⋯_
    ; &/⋯-⋯      = λ x/t ϕ → refl
    ; &/⋯-wk-↑   = &/⋯-wk-↑ₛᵣ
    ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
    }

  private instance _ = ckitₛᵣ

  &/⋯-wk-↑ₛₛ :
    ∀ {µ₁} {µ₂} {m} {mx}
      (t : µ₁ ⊢ mx)
      (ϕ : µ₁ –[ kitₛ ]→ µ₂)
    → wk _ (t ⋯ ϕ) ≡ wk _ t ⋯ (ϕ ↑ m)
  &/⋯-wk-↑ₛₛ {µ₁} {µ₂} {m} {mx} t ϕ =
    wk _ (t ⋯ ϕ)                           ≡⟨ refl ⟩
    t ⋯ ϕ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id          ≡⟨ ⋯-assoc t ϕ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) ⟩
    t ⋯ (ϕ ·ₖ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id)       ≡⟨ ~-cong-⋯ t (↑-wk ϕ _) ⟩
    t ⋯ (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ·ₖ (ϕ ↑ m)) ≡⟨ sym (⋯-assoc t (wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id) (ϕ ↑ m)) ⟩
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ↑ m)    ≡⟨ refl ⟩
    wk _ t ⋯ (ϕ ↑ m)                       ∎

  ckitₛₛ : ComposeKit kitₛ kitₛ kitₛ
  ckitₛₛ = record
    { 𝕂₁⊑𝕂₁⊔𝕂₂  = ⊑ₖ-refl ⦃ kitₛ ⦄
    ; 𝕂₂⊑𝕂₁⊔𝕂₂  = ⊑ₖ-⊤ ⦃ kitₛ ⦄
    ; _&/⋯_      = _⋯_
    ; &/⋯-⋯      = λ x/t ϕ → refl
    ; &/⋯-wk-↑   = &/⋯-wk-↑ₛₛ
    ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
    }

  private instance _ = ckitₛₛ

  -- infixl  9  _ₛ·_  _ₛ·ᵣ_  _ₛ·ₛ_
  -- infixr  9  _∘ₛ_  _ᵣ∘ₛ_  _ₛ∘ₛ_
  infixl  9  _ₛ·ᵣ_  _ₛ·ₛ_
  infixr  9  _ᵣ∘ₛ_  _ₛ∘ₛ_

  -- _ₛ·_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃}
  --       → µ₁ –[ kitₛ ]→ µ₂
  --       → µ₂ –[ 𝕂₂ ]→ µ₃
  --       → µ₁ –[ kitₛ ]→ µ₃
  -- σ ₛ· ϕ = σ ·ₖ ϕ

  -- _∘ₛ_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  -- ϕ₂ ∘ₛ ϕ₁ = ϕ₁ ₛ· ϕ₂

  _ₛ·ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitₛ ]→ µ₂ → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ·ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitₛ ]→ µ₂ → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  _ᵣ∘ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ∘ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  _ₛ·ᵣ_ = _·ₖ_
  _ₛ·ₛ_ = _·ₖ_
  _ᵣ∘ₛ_ = _∘ₖ_
  _ₛ∘ₛ_ = _∘ₖ_

--   ∘~∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
--               {{𝔸  : ComposeKit 𝕂₁  𝕂₂  𝕂}}
--               {{𝔸' : ComposeKit 𝕂₁' 𝕂₂' 𝕂}}
--               {ϕ₁  : µ₁ –[ 𝕂₁  ]→ µ₂ } {ϕ₂  : µ₂  –[ 𝕂₂  ]→ µ₃}
--               {ϕ₁' : µ₁ –[ 𝕂₁' ]→ µ₂'} {ϕ₂' : µ₂' –[ 𝕂₂' ]→ µ₃} →
--     (ϕ₁ ·[ 𝔸 ] ϕ₂) ~ (ϕ₁' ·[ 𝔸' ] ϕ₂') →
--     ∀ {M} (t : µ₁ ⊢ M) →
--     t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
--   ∘~∘→⋯≡⋯ ⦃ 𝔸 = 𝔸 ⦄ ⦃ 𝔸' ⦄ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
--     t ⋯ ϕ₁ ⋯ ϕ₂         ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
--     t ⋯ ϕ₁  ·[ 𝔸  ] ϕ₂  ≡⟨ ~-cong-⋯ t eq ⟩
--     t ⋯ ϕ₁' ·[ 𝔸' ] ϕ₂' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
--     t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

  wk-cancels-,ₖ :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ ⦃ W : KitT 𝕂 ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m)
    → t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wk-cancels-,ₖ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C = C ⦄ t ϕ x/t =
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (ϕ ,ₖ x/t)        ≡⟨ ⋯-assoc ⦃ 𝔸 = C ⦄ t (wkₖ _ id) (ϕ ,ₖ x/t) ⟩
    t ⋯ (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ·[ C ] (ϕ ,ₖ x/t)) ≡⟨ ~-cong-⋯ _ (wk-cancels-,ₖ-· ⦃ C = C ⦄ ϕ x/t) ⟩
    t ⋯ ϕ                                       ∎

  wkᵣ-cancels-,ₖ : ∀ ⦃ 𝕂₂ : Kit ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄
                     (t : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ x/t) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₖ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkᵣ-cancels-,ᵣ : ∀ (t : µ₁ ⊢ M) (ϕ : µ₁ →ᵣ µ₂) (x : µ₂ ∋ m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkᵣ-cancels-,ᵣ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkᵣ-cancels-,ₛ : ∀ (t : µ₁ ⊢ M) (ϕ : µ₁ →ₛ µ₂) (t' : µ₂ ⊢ m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkᵣ-cancels-,ₛ = wk-cancels-,ₖ ⦃ C = ckitᵣ ⦄

  wkₛ-cancels-,ᵣ : ∀ (t : µ₁ ⊢ M) (ϕ : µ₁ →ᵣ µ₂) (x : µ₂ ∋ m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ (ϕ ,ₖ x) ≡ t ⋯ ϕ
  wkₛ-cancels-,ᵣ t ϕ x = wk-cancels-,ₖ ⦃ C = ckitₛᵣ ⦄ t ϕ x

  wkₛ-cancels-,ₛ : ∀ (t : µ₁ ⊢ M) (ϕ : µ₁ →ₛ µ₂) (t' : µ₂ ⊢ m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ (ϕ ,ₖ t') ≡ t ⋯ ϕ
  wkₛ-cancels-,ₛ t ϕ t' = wk-cancels-,ₖ ⦃ C = ckitₛₛ ⦄ t ϕ t'

  --------------------------------------------------------------------------------

  dist-ᵣ·ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
    (⦅ x ⦆ ᵣ·ᵣ ρ) ~ ((ρ ↑ m) ᵣ·ᵣ ⦅ x & ρ ⦆)
  dist-ᵣ·ᵣ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ₛ·ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
    (⦅ t ⦆ ₛ·ᵣ ρ) ~ ((ρ ↑ m) ᵣ·ₛ ⦅ t ⋯ ρ ⦆)
  dist-ₛ·ᵣ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ᵣ·ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
    (⦅ x ⦆ ᵣ·ₛ σ) ~ ((σ ↑ m) ₛ·ₛ ⦅ x & σ ⦆)
  dist-ᵣ·ₛ-⦅⦆ = dist-↑-⦅⦆-·

  dist-ₛ·ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
    (⦅ t ⦆ ₛ·ₛ σ) ~ ((σ ↑ m) ₛ·ₛ ⦅ t ⋯ σ ⦆)
  dist-ₛ·ₛ-⦅⦆ = dist-↑-⦅⦆-·

  --------------------------------------------------------------------------------

  dist-⦅⦆-⋯ :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄ ⦃ W₂ : KitT 𝕂₂ ⦄ ⦃ W : KitT 𝕂 ⦄ 
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      {µ₁ µ₂ m M}
      (t : (m ∷ µ₁) ⊢ M) (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆
  dist-⦅⦆-⋯ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} {m} {M} t x/t ϕ =
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ                           ≡⟨ ⋯-assoc t ⦅ x/t ⦆ ϕ ⟩
    t ⋯ (⦅ x/t ⦆ ·[ C₁ ] ϕ)                   ≡⟨ ~-cong-⋯ t (dist-↑-⦅⦆-· x/t ϕ) ⟩
    t ⋯ ((ϕ ↑ m) ·[ C₂ ] ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ≡⟨ sym (⋯-assoc t (ϕ ↑ m) ⦅ x/t &/⋯[ C₁ ] ϕ ⦆) ⟩
    t ⋯ (ϕ ↑ m) ⋯ ⦅ x/t &/⋯[ C₁ ] ϕ ⦆         ∎

  dist-⦅⦆ᵣ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
    t ⋯ ⦅ x ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ x & ρ ⦆
  dist-⦅⦆ᵣ-⋯ᵣ = dist-⦅⦆-⋯

  dist-⦅⦆ₛ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
    t ⋯ ⦅ t' ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ t' ⋯ ρ ⦆
  dist-⦅⦆ₛ-⋯ᵣ = dist-⦅⦆-⋯

  dist-⦅⦆ᵣ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
    t ⋯ ⦅ x ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ x & σ ⦆
  dist-⦅⦆ᵣ-⋯ₛ = dist-⦅⦆-⋯

  dist-⦅⦆ₛ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
    t ⋯ ⦅ t' ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ t' ⋯ σ ⦆
  dist-⦅⦆ₛ-⋯ₛ = dist-⦅⦆-⋯

  -- For ITraversal implementations
  dist-⦅⦆ₛ-⋯ :
    ∀ ⦃ 𝕂 ⦄
      ⦃ W : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit kitₛ 𝕂 kitₛ ⦄
      ⦃ C₂ : ComposeKit 𝕂 kitₛ kitₛ ⦄
      ⦃ C₃ : ComposeKit 𝕂 𝕂 𝕂 ⦄
      {µ₁ µ₂ m M}
      (t : (µ₁ ▷ m) ⊢ M) (t' : µ₁ ⊢ m→M m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ
  dist-⦅⦆ₛ-⋯ ⦃ 𝕂 ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {µ₁} {µ₂} {m} {M} t t' ϕ =
    t ⋯ ⦅ t' ⦆ₛ ⋯ ϕ                   ≡⟨ dist-⦅⦆-⋯ ⦃ C₁ = C₁ ⦄ t t' ϕ ⟩
    t ⋯ (ϕ ↑ m) ⋯ ⦅ t' &/⋯[ C₁ ] ϕ ⦆ₛ ≡⟨ cong (λ ■ → t ⋯ ϕ ↑ m ⋯ ⦅ ■ ⦆ₛ) (&/⋯-⋯ t' ϕ) ⟩
    t ⋯ (ϕ ↑ m) ⋯ ⦅ t' ⋯ ϕ ⦆ₛ         ∎

--   record ComposeTraversalLemmas : Set₁ where

  ⋯-idₛ : ∀ {µ M} (t : µ ⊢ M) → t ⋯ id ⦃ 𝕂 = kitₛ ⦄ ≡ t
  ⋯-idᵣ : ∀ {µ M} (t : µ ⊢ M) → t ⋯ id ⦃ 𝕂 = kitᵣ ⦄ ≡ t
  ⋯-idₛ = ⋯-id
  ⋯-idᵣ = ⋯-id

  -- -- TODO OLD: We can transfer this from ⋯-id if we extend ComposeKit with a lemma,
  -- -- that operations on terms determine operations on &/⋯
  -- -- We could go even further and say operations on &/⋯ and ⋯ are determined by
  -- -- operations on ap. Note that this is precisely what KitAltSimple does!!!!
  -- &/⋯-id :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
  --     ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
  --     {µ} {m/M} (x/t : µ ∋/⊢[ 𝕂₁ ] m/M)
  --   → x/t &/⋯ id ⦃ 𝕂 = 𝕂₂ ⦄ ≡ ι-∋/⊢ x/t
  -- &/⋯-id ⦃ 𝕂 ⦄ {µ} {M} x/t = {!!}

  wk-cancels-⦅⦆ :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
      ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄ ⦃ KT : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      (t : µ ⊢ M) (x/t : µ ∋/⊢[ 𝕂₂ ] id/m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ ⦅ x/t ⦆ ≡ t
  wk-cancels-⦅⦆ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ t x/t =
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ ⦅ x/t ⦆     ≡⟨ ~-cong-⋯ (t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id) (⦅⦆-,ₖ x/t) ⟩
    t ⋯ wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ _ id ⋯ (id ,ₖ x/t) ≡⟨ wk-cancels-,ₖ t id x/t ⟩
    t ⋯ id                                ≡⟨ ⋯-id t ⟩
    t                                     ∎

  wkᵣ-cancels-⦅⦆ᵣ : ∀ {µ M m} (t : µ ⊢ M) (x : µ ∋ m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ ⦅ x ⦆ᵣ ≡ t
  wkᵣ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkᵣ-cancels-⦅⦆ₛ : ∀ {µ M m} (t : µ ⊢ M) (t' : µ ⊢ m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ _ id ⋯ ⦅ t' ⦆ₛ ≡ t
  wkᵣ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ᵣ : ∀ {µ M m} (t : µ ⊢ M) (x : µ ∋ m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ ⦅ x ⦆ᵣ ≡ t
  wkₛ-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

  wkₛ-cancels-⦅⦆ₛ : ∀ {µ M m} (t : µ ⊢ M) (t' : µ ⊢ m→M m) →
    t ⋯ wkₖ ⦃ 𝕂 = kitₛ ⦄ _ id ⋯ ⦅ t' ⦆ₛ ≡ t
  wkₛ-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

  -- -- special case of 
  -- --   dist-,ₖ-·ʳ : ∀ {m}
  -- --                  (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  -- --                  (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  -- --                  (x/t : µ₃ ∋/⊢[ 𝕂₂ ] id/m→M m)
  -- --                → ((ϕ₁ ·ₖ ϕ₂) ,ₖ' x/t) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ,ₖ x/t))
  -- ↑∘⦅⦆-is-,ₖ :
  --   ∀ ⦃ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂 𝕂 𝕂 ⦄ {µ₁ µ₂ m}
  --     (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
  --     (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  --   → ((ϕ ↑ m) ·ₖ ⦅ x/t ⦆) ~ (ϕ ,ₖ x/t)
  -- ↑∘⦅⦆-is-,ₖ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {m} x/t ϕ =
  --     ((ϕ ↑ m) ·ₖ ⦅ x/t ⦆)     ~⟨ {!!} ⟩
  --     ((ϕ ↑ m) ·ₖ (id ,ₖ x/t)) ~⟨ {!!} ⟩
  --     (ϕ ,ₖ x/t)               ~∎

  -- -- ↑∘⦅⦆-is-,ₛ : ∀ {µ₁ µ₂ m} (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
  -- --   ⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m) ~ σ ,ₛ t
  -- -- ↑∘⦅⦆-is-,ₛ t σ _ (here refl) = ⋯-var (here refl) ⦅ t ⦆
  -- -- ↑∘⦅⦆-is-,ₛ t σ _ (there x)   = wk-cancels-⦅⦆ₛ (σ _ x) t

  -- ↑∘⦅⦆-is-,ₛ :
  --   ∀ {µ₁ µ₂ m}
  --     (t : µ₂ ⊢ m→M m)
  --     (ϕ : µ₁ →ₛ µ₂)
  --   → ((ϕ ↑ m) ·ₖ ⦅ t ⦆) ~ (ϕ ,ₖ t)
  -- ↑∘⦅⦆-is-,ₛ = ↑∘⦅⦆-is-,ₖ

  -- ⋯↑⋯⦅⦆-is-⋯,ₖ :
  --   ∀ ⦃ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂 𝕂 𝕂 ⦄ {µ₁ µ₂ m}
  --     (t : (µ₁ ▷ m) ⊢ M)
  --     (x/t : µ₂ ∋/⊢[ 𝕂 ] id/m→M m)
  --     (ϕ : µ₁ –[ 𝕂 ]→ µ₂)
  --   → t ⋯ (ϕ ↑ m) ⋯ ⦅ x/t ⦆ ≡ t ⋯ (ϕ ,ₖ x/t)
  -- ⋯↑⋯⦅⦆-is-⋯,ₖ {m = m} t x/t ϕ =
  --   t ⋯ (ϕ ↑ m) ⋯ ⦅ x/t ⦆    ≡⟨ ⋯-assoc t (ϕ ↑ m) ⦅ x/t ⦆ ⟩
  --   t ⋯ ((ϕ ↑ m) ·ₖ ⦅ x/t ⦆) ≡⟨ ~-cong-⋯ t (↑∘⦅⦆-is-,ₖ x/t ϕ) ⟩
  --   t ⋯ (ϕ ,ₖ x/t)           ∎

  -- ⋯↑⋯⦅⦆-is-⋯,ₛ :
  --   ∀ {µ₁ µ₂ m}
  --     (t : (µ₁ ▷ m) ⊢ M)
  --     (t' : µ₂ ⊢ m→M m)
  --     (ϕ : µ₁ →ₛ µ₂)
  --   → t ⋯ (ϕ ↑ m) ⋯ ⦅ t' ⦆ ≡ t ⋯ (ϕ ,ₖ t')
  -- ⋯↑⋯⦅⦆-is-⋯,ₛ = ⋯↑⋯⦅⦆-is-⋯,ₖ
