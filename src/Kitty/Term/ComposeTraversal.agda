open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
import Kitty.Term.Sub
import Kitty.Term.SubCompose

module Kitty.Term.ComposeTraversal {𝕄 : Modes} (𝕋 : Terms 𝕄) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) (T : Traversal 𝕋 𝕊)
                                   (H : KitHomotopy 𝕋 𝕊 T) (𝕊C : Kitty.Term.SubCompose.SubCompose 𝕋 𝕊 T H) where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT 𝕋 𝕊 T
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Term.ComposeKit 𝕋 𝕊 T H
open import Kitty.Term.SubCompose 𝕋 𝕊 T H
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open KitHomotopy H
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws 𝕊
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

record ComposeTraversal : Set₁ where
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

  dist-↑-⦅⦆-· :
    ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      ⦃ W : KitT 𝕂 ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂 𝕂 ⦄
      ⦃ C₃ : ComposeKit 𝕂₂ 𝕂₂ 𝕂₂ ⦄
      {µ₁ µ₂ m} (x/t : µ₁ ∋/⊢[ 𝕂₁ ] id/m→M m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
      let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    (⦅ x/t ⦆ ·[ C₁ ] ϕ) ~ ((ϕ ↑ m) ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)
  dist-↑-⦅⦆-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@(here refl) =
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    let sub' = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    let sub'' = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    let sub₁ = subst (µ₂ ∋/⊢[ 𝕂 ]_) (sym (ι-id/m→M m)) in
    `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                              ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
    `/id (sub (x & ⦅ x/t ⦆ &/⋯ ϕ))                              ≡⟨ cong (λ ■ → `/id (sub (■ &/⋯ ϕ))) (~→~' (⦅⦆-,ₖ x/t) _ x) ⟩
    `/id (sub (x & (id ,ₖ x/t) &/⋯ ϕ))                          ≡⟨ cong (λ ■ → `/id (sub (■ &/⋯ ϕ))) (&-,ₖ-here id x/t) ⟩
    `/id (sub (x/t &/⋯ ϕ))                                      ≡⟨ cong `/id (sym (cancel-subst' (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) (sub (x/t &/⋯ ϕ)))) ⟩
    `/id (sub'' (sub₁ (sub (x/t &/⋯ ϕ))))                       ≡⟨ cong (λ ■ → `/id (sub'' ■)) (sym (ι-∋/⊢-id refl _)) ⟩
    `/id (sub'' (ι-∋/⊢ (sub (x/t &/⋯ ϕ))))                      ≡⟨ cong (λ ■ → `/id (sub'' (ι-∋/⊢ ■)))
                                                                        (sym (&-,ₖ-here id (sub (x/t &/⋯[ C₁ ] ϕ)))) ⟩
    `/id (sub'' (ι-∋/⊢ (here refl & (id ⦃ 𝕂 = 𝕂 ⦄ ,ₖ sub (x/t &/⋯[ C₁ ] ϕ)))))
                                                                ≡⟨ cong (λ ■ → `/id (sub'' (ι-∋/⊢ ■)))
                                                                        (sym (~→~' (⦅⦆-,ₖ (sub (x/t &/⋯[ C₁ ] ϕ))) _ (here refl))) ⟩
    `/id (sub'' (ι-∋/⊢ (here refl & ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))) ≡⟨ cong `/id (sym (&/⋯-& ⦃ C₂ ⦄ (here refl)
                                                                                                    ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)) ⟩
    `/id (sub' (id/` (here refl) &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))  ≡⟨ cong (λ ■ → `/id (sub' (■ &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)))
                                                                              (sym (&-↑-here ϕ)) ⟩ 
    `/id (sub' (x & (ϕ ↑ m) &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ ↑ m) ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆ x)) ⟩
    `/id (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))       ∎
  dist-↑-⦅⦆-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ ⦃ C₃ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@(there y) =
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ m) in
    let sub' = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ mx) in
    let sub'' = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₁⊑𝕂₁⊔𝕂₂ ⦃ C₂ ⦄ ⦄ mx) in
    let sub₂ = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ mx) in
    `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))                              ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦅ x/t ⦆ ϕ x) ⟩
    `/id (sub' (x & ⦅ x/t ⦆ &/⋯ ϕ))                             ≡⟨ cong (λ ■ → `/id (sub' (■ &/⋯[ C₁ ] ϕ))) (~→~' (⦅⦆-,ₖ x/t) _ x) ⟩
    `/id (sub' (x & (id ,ₖ x/t) &/⋯ ϕ))                         ≡⟨ cong (λ ■ → `/id (sub' (■ &/⋯[ C₁ ] ϕ))) (&-,ₖ-there id x/t y) ⟩
    `/id (sub' (y & id &/⋯ ϕ))                                  ≡⟨ cong (λ ■ → `/id (sub' (■ &/⋯[ C₁ ] ϕ))) (&-id y) ⟩
    `/id (sub' (id/` y &/⋯ ϕ))                                  ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (&/⋯-& y ϕ) ⟩
    `/id (sub₂ (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ (y & ϕ)))             ≡⟨ cong (`/id ⦃ 𝕂 ⦄) (sym (ι-ap-→ ϕ y)) ⟩
    `/id (y & (ι-→ ⦃ 𝕂₁⊑𝕂₂ = 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C₁ ⦄ ⦄ ϕ))              ≡⟨ ι-~-→ ϕ _ y ⟩
    `/id (y & ϕ)                                                             ≡⟨ sym (·-idʳ ϕ _ y) ⟩
    `/id (y & (ϕ ·[ C₂ ] id))                                                ≡⟨ ~-cong-· ~-refl (~-sym (wk-cancels-,ₖ-· id (sub (x/t &/⋯[ C₁ ] ϕ)))) _ y ⟩
    `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] (id ,ₖ sub (x/t &/⋯[ C₁ ] ϕ)))))  ≡⟨ ~-cong-· ~-refl (~-cong-· ~-refl (~-sym (⦅⦆-,ₖ (sub (x/t &/⋯[ C₁ ] ϕ))))) _ y ⟩
    `/id (y & (ϕ ·[ C₂ ] (wkₖ _ id ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)))      ≡⟨ sym (·-assoc ϕ (wkₖ _ id) ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆ _ y) ⟩
    `/id (y & ((ϕ ·[ C₃ ] wkₖ _ id) ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))      ≡⟨ ~-cong-· (~-sym (wk-ϕ-id ϕ)) ~-refl _ y ⟩
    `/id (y & (wkₖ _ ϕ ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))      ≡⟨ cong `/id (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (wkₖ _ ϕ) ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆ y) ⟩
    `/id (sub'' (y & (wkₖ _ ϕ) &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))  ≡⟨ cong (λ ■ → `/id (sub'' (■ &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)))
                                                                              (&-wkₖ-wk ϕ y) ⟩
    `/id (sub'' (wk _ (y & ϕ) &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))   ≡⟨ cong (λ ■ → `/id (sub'' (■ &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆)))
                                                                              (sym (&-↑-there ϕ y)) ⟩ 
    `/id (sub'' (x & (ϕ ↑ m) &/⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))    ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ⦃ C = C₂ ⦄ (ϕ ↑ m) ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆ x)) ⟩
    `/id (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆))      ∎

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

  &/⋯-&ₛ : ∀ ⦃ 𝕂 ⦄ ⦃ W : KitT 𝕂 ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) 
           → let sub₂ = subst (µ₂ ⊢_) (ι-id/m→M ⦃ ⊑ₖ-⊤ ⦃ 𝕂 = 𝕂 ⦄ ⦄ m) in
             ` x ⋯ ϕ ≡ sub₂ (ι-∋/⊢ ⦃ ⊑ₖ-⊤ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (x & ϕ))
  &/⋯-&ₛ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} x ϕ =
    let sub₂ = subst (µ₂ ⊢_) (ι-id/m→M ⦃ ⊑ₖ-⊤ ⦃ 𝕂 = 𝕂 ⦄ ⦄ m) in
    ` x ⋯ ϕ                                 ≡⟨ ⋯-var' x ϕ ⟩
    sub₂ (`/id' (x & ϕ))                    ≡⟨⟩
    sub₂ (ι-∋/⊢ ⦃ ⊑ₖ-⊤ ⦃ 𝕂 = 𝕂 ⦄ ⦄ (x & ϕ)) ∎

  ~-cong-&/⋯ₛ :
    ∀ ⦃ 𝕂 ⦄ ⦃ W : KitT 𝕂 ⦄ {m} {t₁ t₂ : µ₁ ⊢ m→M m}
      {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂}
    → t₁ ≡ t₂
    → ϕ₁ ~ ϕ₂
    → t₁ ⋯ ϕ₁ ≡ t₂ ⋯ ϕ₂
  ~-cong-&/⋯ₛ refl ϕ₁~ϕ₂ = ~-cong-⋯ _ ϕ₁~ϕ₂

  &/⋯-wk-↑ₛᵣ : ∀ {µ₁} {µ₂} {m} {mx}
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
    ; &/⋯-&      = &/⋯-&ₛ
    ; &/⋯-wk-↑   = &/⋯-wk-↑ₛᵣ
    ; ~-cong-&/⋯ = ~-cong-&/⋯ₛ
    }

  private instance _ = ckitₛᵣ

  &/⋯-wk-↑ₛₛ : ∀ {µ₁} {µ₂} {m} {mx}
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
    ; &/⋯-&      = &/⋯-&ₛ
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
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆
  dist-⦅⦆-⋯ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ ⦃ W ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} {m} {M} t x/t ϕ =
    let sub = subst (µ₂ ∋/⊢[ 𝕂 ]_) (ι-id/m→M m) in
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ                                 ≡⟨ ⋯-assoc t ⦅ x/t ⦆ ϕ ⟩
    t ⋯ (⦅ x/t ⦆ ·[ C₁ ] ϕ)                         ≡⟨ ~-cong-⋯ t (dist-↑-⦅⦆-· x/t ϕ) ⟩
    t ⋯ ((ϕ ↑ m) ·[ C₂ ] ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆) ≡⟨ sym (⋯-assoc t (ϕ ↑ m) ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆) ⟩
    t ⋯ (ϕ ↑ m) ⋯ ⦅ sub (x/t &/⋯[ C₁ ] ϕ) ⦆         ∎

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
