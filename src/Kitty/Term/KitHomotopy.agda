open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitHomotopy
    {𝕋 : Terms}
    {ℓ} {𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ}
    (T : Traversal 𝕋 𝕊)
  where

open import Data.List.Relation.Unary.Any using (here; there)
open import Level using () renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitT T
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Terms 𝕋
open Traversal T
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄
open SubWithLaws 𝕊
open _⊑ₖ_ ⦃ … ⦄

private instance _ = Kᵣ; _ = Kₛ
private instance _ = Wᵣ; _ = Wₛ

private variable
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

record KitHomotopy : Set (lsuc ℓ) where
  field
    ~-cong-⋯ :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
        ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄
        {S₁ S₂ st} {s : Sort st}
        {f : S₁ –[ K₁ ]→ S₂} {g : S₁ –[ K₂ ]→ S₂} (t : S₁ ⊢ s)
      → f ~ g
      → t ⋯ f ≡ t ⋯ g

  ⋯-ι-→ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄
      ⦃ K₁⊑K₂ : K₁ ⊑ₖ K₂ ⦄
      {S₁ S₂ st} {s : Sort st}
      (t : S₁ ⊢ s) (ϕ : S₁ –[ K₁ ]→ S₂)
    → t ⋯ ι-→ ϕ ≡ t ⋯ ϕ
  ⋯-ι-→ t ϕ = ~-cong-⋯ t (~-ι-→ ϕ)

  ren→sub :
    ∀ {S₁ S₂ st} {s : Sort st} (t : S₁ ⊢ s) (ρ : S₁ →ᵣ S₂)
    → t ⋯ᵣ ρ ≡ t ⋯ₛ ι-→ ⦃ K₁⊑K₂ = ⊑-ᵣₛ ⦄ ρ
  ren→sub t ρ = sym (⋯-ι-→ ⦃ K₁⊑K₂ = ⊑-ᵣₛ ⦄ t ρ)

  wk~wk :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄
      {s} {S}
    → wkₖ ⦃ K = K₁ ⦄ s id ~ wkₖ ⦃ K = K₂ ⦄ s (id {S = S})
  wk~wk ⦃ K₁ ⦄ ⦃ K₂ ⦄ {s} {S} = mk-~ λ sx x →
    let open ≡-Reasoning in
    `/id ⦃ K₁ ⦄ (x & wkₖ    s id) ≡⟨ cong (`/id ⦃ K₁ ⦄) (&-wkₖ-wk id x) ⟩
    `/id ⦃ K₁ ⦄ (wk _ (x & id))   ≡⟨ cong (λ ■ → `/id ⦃ K₁ ⦄ (wk ⦃ K₁ ⦄ _ ■)) (&-id x) ⟩
    `/id ⦃ K₁ ⦄ (wk _ (id/` x ))  ≡⟨ cong (`/id ⦃ K₁ ⦄) (wk-id/` _ x) ⟩
    `/id ⦃ K₁ ⦄ (id/` (there x))  ≡⟨ id/`/id ⦃ K₁ ⦄ (there x) ⟩
    ` there x                     ≡⟨ sym (id/`/id ⦃ K₂ ⦄ (there x)) ⟩
    `/id ⦃ K₂ ⦄ (id/` (there x))  ≡⟨ cong (`/id ⦃ K₂ ⦄) (sym (wk-id/` _ x)) ⟩
    `/id ⦃ K₂ ⦄ (wk _ (id/` x ))  ≡⟨ cong (λ ■ → `/id ⦃ K₂ ⦄ (wk ⦃ K₂ ⦄ _ ■)) (sym (&-id x)) ⟩
    `/id ⦃ K₂ ⦄ (wk _ (x & id))   ≡⟨ cong (`/id ⦃ K₂ ⦄) (sym (&-wkₖ-wk id x)) ⟩
    `/id ⦃ K₂ ⦄ (x & wkₖ s id)    ∎

  ⋯-x/t-wk :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ K₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ K₂ : Kit _∋/⊢₂_ ⦄
      ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄
      {S} {s'} {s} (x/t : S ∋/⊢[ K₁ ] s)
    → (`/id x/t ⋯ wkₖ ⦃ K = K₂ ⦄ _ id) ≡ `/id (wk s' x/t)
  ⋯-x/t-wk ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S} {s'} {s} x/t =
    let open ≡-Reasoning in
    `/id x/t ⋯ wkₖ ⦃ K = K₂ ⦄ _ id  ≡⟨ ~-cong-⋯ (`/id x/t) wk~wk ⟩
    `/id x/t ⋯ wkₖ ⦃ K = Kᵣ ⦄ _ id  ≡⟨ wk-`/id _ x/t ⟩
    `/id (wk s' x/t)                ∎

  ⊑ₖ-⊤ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ KT : KitT K ⦄
    → K ⊑ₖ Kₛ
  ⊑ₖ-⊤ ⦃ K ⦄ = record
    { ι-∋/⊢    = `/id
    ; ι-id/`   = id/`/id ⦃ K ⦄
    ; ι-`/id   = λ {S} {s} x/t → refl
    ; ι-wk     = λ {s'} {s} {S} x/t →
        let open ≡-Reasoning in
        `/id (wk _ x/t) ≡⟨ sym (⋯-x/t-wk x/t) ⟩
        wk _ (`/id x/t) ∎
    }

  open import Data.List.Properties using (++-assoc)
  ⋯-↑*-▷▷ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ {S₁ S₂ st} {s : Sort st} S S' (t : (S₁ ▷▷ S ▷▷ S') ⊢ s) (ϕ : S₁ –[ K ]→ S₂)  →
    let sub = subst (_⊢ s) (sym (++-assoc S' S S₁)) in
    let sub'⁻¹ = subst (_⊢ s) (++-assoc S' S S₂) in
    t ⋯ ϕ ↑* S ↑* S' ≡ sub'⁻¹ (sub t ⋯ ϕ ↑* (S ▷▷ S'))
  ⋯-↑*-▷▷ ⦃ K ⦄ ⦃ W ⦄ {S₁} {S₂} {st} {s} S S' t ϕ =
    let open ≡-Reasoning in
    let sub₁⁻¹ = subst (_⊢ s) (sym (++-assoc S' S S₁)) in
    let sub₁   = subst (_⊢ s) (++-assoc S' S S₁) in
    let sub₂   = subst (_⊢ s) (++-assoc S' S S₂) in
    let sub₂⁻¹ = subst (_⊢ s) (sym (++-assoc S' S S₂)) in
    let sub₁→  = subst (_–[ K ]→ (S₂ ▷▷ (S ▷▷ S'))) (++-assoc S' S S₁) in
    let sub₁⁻¹→ = subst (_–[ K ]→ (S₂ ▷▷ (S ▷▷ S'))) (sym (++-assoc S' S S₁)) in
    let sub₂→  = subst ((S₁ ▷▷ S ▷▷ S') –[ K ]→_) (++-assoc S' S S₂) in
    let sub₂⁻¹→ = subst ((S₁ ▷▷ S ▷▷ S') –[ K ]→_) (sym (++-assoc S' S S₂)) in
    let sub₁₂→ = subst₂ (_–[ K ]→_) (++-assoc S' S S₁) (++-assoc S' S S₂) in
    t ⋯ ϕ ↑* S ↑* S'                                              ≡⟨ ~-cong-⋯ t (↑*-▷▷ ϕ S S') ⟩
    t ⋯ sub₁₂→ (ϕ ↑* (S ▷▷ S'))                                   ≡⟨ sym (cancel-subst' (_⊢ s) (++-assoc S' S S₂) _) ⟩
    sub₂ (sub₂⁻¹ (t ⋯ sub₁₂→ (ϕ ↑* (S ▷▷ S'))))                   ≡⟨ cong sub₂ (sym (dist-subst (t ⋯_) (sym (++-assoc S' S S₂)) _)) ⟩
    sub₂ (t ⋯ sub₂⁻¹→ (sub₁₂→ (ϕ ↑* (S ▷▷ S'))))                  ≡⟨ cong (λ ■ → sub₂ (■ ⋯ sub₂⁻¹→ (sub₁₂→ (ϕ ↑* (S ▷▷ S'))))) (sym (cancel-subst' (_⊢ s) (++-assoc S' S S₁) _)) ⟩
    sub₂ (sub₁ (sub₁⁻¹ t) ⋯ sub₂⁻¹→ (sub₁₂→ (ϕ ↑* (S ▷▷ S'))))    ≡⟨ cong sub₂ (dist-subst-arg _⋯_ (++-assoc S' S S₁) (sym (++-assoc S' S S₁))
                                                                                                   (sub₁⁻¹ t) (sub₂⁻¹→ (sub₁₂→ (ϕ ↑* (S ▷▷ S'))))) ⟩
    sub₂ (sub₁⁻¹ t ⋯ sub₁⁻¹→ (sub₂⁻¹→ (sub₁₂→ (ϕ ↑* (S ▷▷ S'))))) ≡⟨ cong (λ ■ → sub₂ (sub₁⁻¹ t ⋯ sub₁⁻¹→ (sub₂⁻¹→ ■))) (subst₂₁ _–[ K ]→_ (++-assoc S' S S₁) (++-assoc S' S S₂) _) ⟩
    sub₂ (sub₁⁻¹ t ⋯ sub₁⁻¹→ (sub₂⁻¹→ (sub₂→ (sub₁→ (ϕ ↑* (S ▷▷ S')))))) ≡⟨ cong (λ ■ → sub₂ (sub₁⁻¹ t ⋯ sub₁⁻¹→ ■)) (cancel-subst ((S₁ ▷▷ S ▷▷ S') –[ K ]→_) (++-assoc S' S S₂) _) ⟩
    sub₂ (sub₁⁻¹ t ⋯ sub₁⁻¹→ (sub₁→ (ϕ ↑* (S ▷▷ S')))) ≡⟨ cong (λ ■ → sub₂ (sub₁⁻¹ t ⋯ ■)) (cancel-subst (_–[ K ]→ (S₂ ▷▷ (S ▷▷ S'))) (++-assoc S' S S₁) _) ⟩
    sub₂ (sub₁⁻¹ t ⋯ ϕ ↑* (S ▷▷ S'))                              ∎

-- open import Axios.Extensionality.Propositional using (Extensionality)

-- Extensionality→KitHosotopy : ∀ {T} → Extensionality 0ℓ 0ℓ → KitHosotopy T
-- Extensionality→KitHosotopy {T} fun-ext =
--   let open Traversal T in record
--   { ~-cong-⋯ = λ t f~g → cong (t ⋯_) (fun-ext (λ s → fun-ext (λ x → f~g s x))) }
