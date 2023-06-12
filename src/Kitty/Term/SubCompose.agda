open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)

module Kitty.Term.SubCompose
    {𝕋 : Terms}
    {ℓ} {𝕊 : SubWithLaws 𝕋 ℓ}
    {T : Traversal 𝕋 𝕊}
    (H : KitHomotopy T)
  where

open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Level using () renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.ComposeKit H
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.KitT T
open import Kitty.Term.Prelude
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties
open ComposeKit ⦃ … ⦄
open Kit ⦃ … ⦄
open Kitty.Term.Sub.SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open Terms 𝕋
open Traversal T
open _⊑ₖ_ ⦃ … ⦄
open ~-Reasoning

record SubCompose : Set (lsuc ℓ) where
  infixl  9  _·ₖ_
  infixr  9  _∘ₖ_

  field
    _·ₖ_ :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {S₁ S₂ S₃}
      → S₁ –[ 𝕂₁ ]→ S₂
      → S₂ –[ 𝕂₂ ]→ S₃
      → S₁ –[ 𝕂  ]→ S₃

    &-·ₖ-&/⋯ :
      ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {_∋/⊢_ : VarScoped}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {S₁} {S₂} {S₃} {s}
        (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
        (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
        (x : S₁ ∋ s)
      → x & (ϕ₁ ·ₖ ϕ₂) ≡ (x & ϕ₁) &/⋯ ϕ₂

  _∘ₖ_ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_  : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {S₁} {S₂} {S₃}
    → S₂ –[ 𝕂₂ ]→ S₃
    → S₁ –[ 𝕂₁ ]→ S₂
    → S₁ –[ 𝕂 ]→ S₃
  ϕ₂ ∘ₖ ϕ₁ = ϕ₁ ·ₖ ϕ₂

  infixl  9  _·[_]_
  infixr  9  _∘[_]_

  _·[_]_ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      {S₁} {S₂} {S₃}
    → S₁ –[ 𝕂₁ ]→ S₂
    → ComposeKit 𝕂₁ 𝕂₂ 𝕂
    → S₂ –[ 𝕂₂ ]→ S₃
    → S₁ –[ 𝕂 ]→ S₃
  ϕ₁ ·[ C ] ϕ₂ = _·ₖ_ ⦃ C = C ⦄ ϕ₁ ϕ₂


  _∘[_]_ :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {S₁} {S₂} {S₃}
    → S₂ –[ 𝕂₂ ]→ S₃
    → ComposeKit 𝕂₁ 𝕂₂ 𝕂
    → S₁ –[ 𝕂₁ ]→ S₂
    → S₁ –[ 𝕂 ]→ S₃
  ϕ₂ ∘[ C ] ϕ₁ = _∘ₖ_ ⦃ C = C ⦄ ϕ₂ ϕ₁


  module _ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
           {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
           {_∋/⊢_ : VarScoped}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
           ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ where
        
    -- TODO: This can be more heterogeneous.
    ~-cong-· :
      ∀ {S₁} {S₂} {S₃}
        {ϕ₁ ϕ₁' : S₁ –[ 𝕂₁ ]→ S₂}
        {ϕ₂ ϕ₂' : S₂ –[ 𝕂₂ ]→ S₃}
      → ϕ₁ ~ ϕ₁'
      → ϕ₂ ~ ϕ₂'
      → (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁' ·ₖ ϕ₂')
    ~-cong-· {S₁} {S₂} {S₃} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' = mk-~ λ s x →
      `/id (x & (ϕ₁  ·ₖ ϕ₂ )) ≡⟨ cong `/id (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x) ⟩
      `/id (x & ϕ₁  &/⋯ ϕ₂ )  ≡⟨ cong `/id (~-cong-&/⋯ (use-~-hom ϕ₁~ϕ₁' _ x) ϕ₂~ϕ₂') ⟩
      `/id (x & ϕ₁' &/⋯ ϕ₂')  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ₁' ϕ₂' x)) ⟩
      `/id (x & (ϕ₁' ·ₖ ϕ₂')) ∎

    -- This is used to prove the variable case of ⋯-assoc.
    tm-⋯-· :
      ∀ {S₁} {S₂} {S₃} {s}
        (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
        (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
        (x : S₁ ∋ s)
      → `/id (x & ϕ₁) ⋯ ϕ₂ ≡ `/id (x & (ϕ₁ ·ₖ ϕ₂))
    tm-⋯-· {S₁} {S₂} {S₃} {s} ϕ₁ ϕ₂ x =
      `/id (x & ϕ₁) ⋯ ϕ₂    ≡⟨ sym (&/⋯-⋯ (x & ϕ₁) ϕ₂) ⟩
      `/id (x & ϕ₁ &/⋯ ϕ₂)  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x)) ⟩
      `/id (x & (ϕ₁ ·ₖ ϕ₂)) ∎

    dist-↑-· :
      ∀ {S₁} {S₂} {S₃} s
        (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
        (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
      → ((ϕ₁ ·ₖ ϕ₂) ↑ s) ~ ((ϕ₁ ↑ s) ·ₖ (ϕ₂ ↑ s))
    dist-↑-· {S₁} {S₂} {S₃} s ϕ₁ ϕ₂ = mk-~ λ where
      mx x@(here refl) →
        `/id ⦃ 𝕂 ⦄ (x & ((ϕ₁ ·ₖ ϕ₂) ↑ s))          ≡⟨ cong `/id (&-↑-here (ϕ₁ ·ₖ ϕ₂)) ⟩
        `/id ⦃ 𝕂 ⦄ (id/` (here refl))              ≡⟨ id/`/id ⦃ 𝕂 ⦄ (here refl) ⟩
        ` here refl                                ≡⟨ sym (id/`/id ⦃ 𝕂₂ ⦄ (here refl)) ⟩
        `/id ⦃ 𝕂₂ ⦄ (id/` (here refl))             ≡⟨ ι-`/id (id/` (here refl)) ⟩
        `/id ⦃ 𝕂 ⦄ (ι-∋/⊢ (id/` ⦃ 𝕂₂ ⦄ (here refl)))      ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (sym (&-↑-here ϕ₂)) ⟩
        `/id ⦃ 𝕂 ⦄ (ι-∋/⊢ (here refl & (ϕ₂ ↑ s)))  ≡⟨ cong `/id (sym (&/⋯-& (here refl) (ϕ₂ ↑ s))) ⟩
        `/id ⦃ 𝕂 ⦄ (id/` (here refl) &/⋯ (ϕ₂ ↑ s)) ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ₂ ↑ s)) (sym (&-↑-here ϕ₁)) ⟩
        `/id ⦃ 𝕂 ⦄ (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ s) (ϕ₂ ↑ s) x)) ⟩
        `/id ⦃ 𝕂 ⦄ (x & ((ϕ₁ ↑ s) ·ₖ (ϕ₂ ↑ s)))    ∎
      mx x@(there y) →
        `/id (x & ((ϕ₁ ·ₖ ϕ₂) ↑ s))          ≡⟨ cong `/id (&-↑-there (ϕ₁ ·ₖ ϕ₂) y) ⟩
        `/id (wk _ (y & (ϕ₁ ·ₖ ϕ₂)))         ≡⟨ cong (λ ■ → `/id (wk _ ■)) (&-·ₖ-&/⋯ ϕ₁ ϕ₂ y) ⟩
        `/id (wk _ (y & ϕ₁ &/⋯ ϕ₂))          ≡⟨ cong `/id (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
        `/id (wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ s))    ≡⟨ cong (λ ■ → `/id (■ &/⋯ (ϕ₂ ↑ s))) (sym (&-↑-there ϕ₁ y)) ⟩
        `/id (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ s) (ϕ₂ ↑ s) x)) ⟩
        `/id (x & ((ϕ₁ ↑ s) ·ₖ (ϕ₂ ↑ s)))    ∎

    dist-↑*-· :
      ∀ {S₁ S₂ S₃} S (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂) (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
      → ((ϕ₁ ·ₖ ϕ₂) ↑* S) ~ ((ϕ₁ ↑* S) ·ₖ (ϕ₂ ↑* S))
    dist-↑*-· []      ϕ₁ ϕ₂ =
      ((ϕ₁ ·ₖ ϕ₂) ↑* [])                  ~⟨ ↑*-[] (ϕ₁ ·ₖ ϕ₂) ⟩
      ϕ₁ ·ₖ ϕ₂                            ~⟨ ~-sym (~-cong-· (↑*-[] ϕ₁) (↑*-[] ϕ₂)) ⟩
      ((ϕ₁ ↑* []) ·ₖ (ϕ₂ ↑* []))          ~∎
    dist-↑*-· (S ▷ s) ϕ₁ ϕ₂ =
      (ϕ₁ ·ₖ ϕ₂) ↑* (S ▷ s)               ~⟨ ↑*-▷ S s (ϕ₁ ·ₖ ϕ₂) ⟩
      ((ϕ₁ ·ₖ ϕ₂) ↑* S) ↑ s               ~⟨ ~-cong-↑' (dist-↑*-· S ϕ₁ ϕ₂) ⟩
      ((ϕ₁ ↑* S) ·ₖ (ϕ₂ ↑* S)) ↑ s        ~⟨ dist-↑-· s (ϕ₁ ↑* S) (ϕ₂ ↑* S) ⟩
      ((ϕ₁ ↑* S) ↑ s) ·ₖ ((ϕ₂ ↑* S) ↑ s)  ~⟨ ~-sym (~-cong-· (↑*-▷ S s ϕ₁) (↑*-▷ S s ϕ₂)) ⟩
      (ϕ₁ ↑* (S ▷ s)) ·ₖ (ϕ₂ ↑* (S ▷ s))  ~∎

    -- dist-,ₖ-· : ∀ {s}
    --               (ϕ₁ : S₁ –[ 𝕂₁ ]→ S₂)
    --               (ϕ₂ : S₂ –[ 𝕂₂ ]→ S₃)
    --               (x/t : S₂ ∋/⊢[ 𝕂₁ ] s)
    --             → let sub = subst (S₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-s) in
    --               ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t &/⋯ ϕ₂)) ~ (ϕ₁ ,ₖ x/t ·ₖ ϕ₂)

    ·-idʳ :
      ∀ {S₁} {S₂} (ϕ : S₁ –[ 𝕂₁ ]→ S₂)
      → (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄) ~ ϕ
    ·-idʳ {S₁} {S₂} ϕ = mk-~ λ mx x →
      `/id (x & (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄)) ≡⟨ cong (`/id) (&-·ₖ-&/⋯ ϕ id x) ⟩
      `/id (x & ϕ &/⋯ id ⦃ 𝕂 = 𝕂₂ ⦄)  ≡⟨ &/⋯-⋯ (x & ϕ) id ⟩
      `/id (x & ϕ) ⋯ id ⦃ 𝕂 = 𝕂₂ ⦄    ≡⟨ ⋯-id (`/id (x & ϕ)) ⟩
      `/id (x & ϕ)                    ∎

    ·-idˡ :
      ∀ {S₁} {S₂} (ϕ : S₁ –[ 𝕂₂ ]→ S₂)
      → (id ⦃ 𝕂 = 𝕂₁ ⦄ ·ₖ ϕ) ~ ϕ
    ·-idˡ {S₁} {S₂} ϕ = mk-~ λ mx x →
      `/id (x & (id ⦃ 𝕂 = 𝕂₁ ⦄ ·ₖ ϕ))   ≡⟨ cong (`/id) (&-·ₖ-&/⋯ id ϕ x) ⟩
      `/id (x & id ⦃ 𝕂 = 𝕂₁ ⦄ &/⋯ ϕ)    ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ)) (&-id ⦃ 𝕂 = 𝕂₁ ⦄ x) ⟩
      `/id (id/` x &/⋯ ϕ)               ≡⟨ cong (`/id) (&/⋯-& x ϕ) ⟩
      `/id (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦄ (x & ϕ)) ≡⟨ sym (ι-`/id (x & ϕ)) ⟩
      `/id (x & ϕ)                      ∎

    -- Alternative route:
      -- (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ (wkₖ _ (ϕ ,ₖ x/t)) ~ ϕ
    -- From which then follows:
      -- wkₖ _ ϕ · ⦅ x/t ⦆ ~
      -- wkₖ _ id · ϕ · ⦅ x/t ⦆ ~
      -- ϕ · wkₖ _ id · ⦅ x/t ⦆ ~
      -- ϕ · id ~
      -- ϕ
    wk-cancels-,ₖ-· :
      ∀ {S₁} {S₂} {s}
        (ϕ : S₁ –[ 𝕂₂ ]→ S₂) (x/t : S₂ ∋/⊢[ 𝕂₂ ] s)
      → (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ ϕ
    wk-cancels-,ₖ-· {S₁} {S₂} {s} ϕ x/t = mk-~ λ mx x →
      `/id (x & (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)))  ≡⟨ cong (`/id) (&-·ₖ-&/⋯ (wkₖ _ id) (ϕ ,ₖ x/t) x) ⟩
      `/id (x & wkₖ _ id &/⋯ (ϕ ,ₖ x/t))   ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ ,ₖ x/t))) (&-wkₖ-wk id x) ⟩
      `/id (wk _ (x & id) &/⋯ (ϕ ,ₖ x/t))  ≡⟨ cong (λ ■ → `/id (wk ⦃ 𝕂₁ ⦄ _ ■ &/⋯ (ϕ ,ₖ x/t))) (&-id x) ⟩
      `/id (wk _ (id/` x) &/⋯ (ϕ ,ₖ x/t))  ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ ,ₖ x/t))) (wk-id/` _ x) ⟩
      `/id (id/` (there x) &/⋯ (ϕ ,ₖ x/t)) ≡⟨ cong `/id (&/⋯-& (there x) (ϕ ,ₖ x/t)) ⟩
      `/id (ι-∋/⊢ (there x & (ϕ ,ₖ x/t)))  ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (&-,ₖ-there ϕ x/t x) ⟩
      `/id (ι-∋/⊢ (x & ϕ))                 ≡⟨ cong `/id (sym (&-ι-→ ϕ x)) ⟩
      `/id (x & (ι-→ ϕ))                   ≡⟨ use-~ (~-ι-→ ϕ) _ x ⟩
      `/id (x & ϕ)                         ∎

    wk-ϕ-id :
      ∀ ⦃ W₁ : KitT 𝕂₁ ⦄
        ⦃ W₂ : KitT 𝕂₂ ⦄
        {S₁} {S₂} {s}
        (ϕ : S₁ –[ 𝕂₁ ]→ S₂)
      → wkₖ s ϕ ~ (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s id)
    wk-ϕ-id ⦃ W ⦄ {S₁} {S₂} {s} ϕ = mk-~ λ mx x →
      `/id (x & wkₖ s ϕ)                    ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
      `/id (wk s (x & ϕ))                   ≡⟨ ι-`/id (wk s (x & ϕ)) ⟩
      `/id (ι-∋/⊢ (wk s (x & ϕ)))           ≡⟨ cong `/id (sym (&/⋯-wk (x & ϕ))) ⟩
      `/id (x & ϕ &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s id)  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s id) x)) ⟩
      `/id (x & (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ s id)) ∎

    wk-↓ :
      ∀ {S₁ S₂ m₁} (ϕ : (S₁ ▷ m₁) –[ 𝕂₂ ]→ S₂) →
      wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id ·ₖ ϕ ~ ϕ ↓
    wk-↓ {S₁} {S₂} {m₁} ϕ = mk-~ λ s x →
      Kit.`/id 𝕂 (x & (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id ·ₖ ϕ))            ≡⟨ cong (Kit.`/id 𝕂) (&-·ₖ-&/⋯ (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id) ϕ x) ⟩
      Kit.`/id 𝕂 (x & wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id &/⋯[ C ] ϕ)        ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (■ &/⋯[ C ] ϕ))
                                                                       (&-wkₖ-wk id x) ⟩
      Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ (x & id ⦃ 𝕂 = 𝕂₁ ⦄) &/⋯[ C ] ϕ) ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ ■ &/⋯[ C ] ϕ))
                                                                          (&-id x) ⟩
      Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ (Kit.id/` 𝕂₁ x) &/⋯[ C ] ϕ)     ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (■ &/⋯[ C ] ϕ))
                                                                         (Kit.wk-id/` 𝕂₁ _ x) ⟩
      Kit.`/id 𝕂 (Kit.id/` 𝕂₁ (there x) &/⋯[ C ] ϕ)           ≡⟨ cong (Kit.`/id 𝕂) (&/⋯-& (there x) ϕ) ⟩
      Kit.`/id 𝕂 (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C ⦄ ⦄ (there x & ϕ))     ≡⟨ sym (ι-`/id (there x & ϕ)) ⟩
      Kit.`/id 𝕂₂ (there x & ϕ)                               ≡⟨ sym (cong (Kit.`/id 𝕂₂) (&-↓ ϕ x)) ⟩
      Kit.`/id 𝕂₂ (x & (ϕ ↓))                                 ∎

  ↑-wk :
    ∀ {_∋/⊢₁_ : VarScoped} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {_∋/⊢₂_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {_∋/⊢_ : VarScoped}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      {S₁} {S₂} (ϕ : S₁ –[ 𝕂₁ ]→ S₂) s
    → (ϕ ·[ C₁ ] wkₖ s id) ~ (wkₖ s id ·[ C₂ ] (ϕ ↑ s))
  ↑-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {S₁} {S₂} ϕ s =
      (ϕ ·[ C₁ ] wkₖ s id)                             ~⟨ ~-sym (wk-ϕ-id ϕ) ⟩
      wkₖ s ϕ                                          ~⟨ ~-sym (wk-cancels-,ₖ-· (wkₖ s ϕ) (id/` (here refl))) ⟩
      (wkₖ s id ·[ C₂ ] (wkₖ s ϕ ,ₖ id/` (here refl))) ~⟨ ~-cong-· ~-refl (~-sym (↑-,ₖ ϕ s)) ⟩
      (wkₖ s id ·[ C₂ ] (ϕ ↑ s))                       ~∎

  -- TODO: Move to different file
  module _ where
    private instance _ = kitᵣ; _ = ckitᵣ

    subst-here : ∀ {S₁ S₂ : SortCtx} {s} (p : S₁ ▷ s ≡ S₂ ▷ s) →
      subst (_∋ s) p (here {x = s} {xs = S₁} refl) ≡ here refl
    subst-here refl = refl

    dist-subst-sub :
      ∀ {_∋/⊢_ : VarScoped}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        {S₁ S₁' S₂ S₂' s} →
      (p : S₁ ≡ S₁') →
      (q : S₂ ≡ S₂') →
      (x : S₁' ∋ s) →
      (ϕ : S₁ –[ 𝕂 ]→ S₂) →
      let sub₁₂ = subst₂ (_–[ 𝕂 ]→_) p q in
      let sub₁⁻¹ = subst (_∋ s) (sym p) in
      let sub₂ = subst (_∋/⊢[ 𝕂 ] s) q in
      x & sub₁₂ ϕ ≡ sub₂ (sub₁⁻¹ x & ϕ)
    dist-subst-sub refl refl x ϕ = refl

    dist-subst-sub' :
      ∀ {_∋/⊢_ : VarScoped}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        {S₁ S₁' S₂ S₂' st} {s : Sort st} →
      (p : S₁ ≡ S₁') →
      (q : S₂ ≡ S₂') →
      (t : S₁' ⊢ s) →
      (ϕ : S₁ –[ 𝕂 ]→ S₂) →
      let sub₁₂ = subst₂ (_–[ 𝕂 ]→_) p q in
      let sub₁⁻¹ = subst (_⊢ s) (sym p) in
      let sub₂ = subst (_⊢ s) q in
      t ⋯ sub₁₂ ϕ ≡ sub₂ (sub₁⁻¹ t ⋯ ϕ)
    dist-subst-sub' refl refl x ϕ = refl

    -- FIXME: causes Agda to hang since update to 2.6.4...
    -- -- NOTE: the &/⋯[ C ] can be replaced by &.
    -- wk*-∥₁ :
    --   ∀ ⦃ 𝕂 ⦄ {S₁ S₂ S} (ϕ₁ : S₁ –[ 𝕂 ]→ S) (ϕ₂ : S₂ –[ 𝕂 ]→ S) →
    --   let sub = subst₂ (_→ᵣ_) (++-identityʳ S₂) (cong (_▷▷ S₂) (++-identityʳ S₁)) in
    --   sub (wkₖ* S₁ (id {S = []}) ↑* S₂) ·[ ckitᵣ ] (ϕ₁ ∥ ϕ₂) ~ ϕ₂
    -- wk*-∥₁ ⦃ 𝕂 ⦄ {S₁ = S₁} {S₂} {S} ϕ₁ ϕ₂ = mk-~ λ where
    --   s x@(here {x = m₂} {xs = S₂} refl) →
    --     let C = ckitᵣ in
    --     let sub = subst₂ _→ᵣ_ (cong (_▷ m₂) (++-identityʳ S₂)) (cong (_▷▷ (S₂ ▷ m₂)) (++-identityʳ S₁)) in
    --     let subx = subst (_∋ m₂) (cong (_▷▷ (S₂ ▷ m₂)) (++-identityʳ S₁)) in
    --     let suby = subst (_∋ m₂) (sym (cong (_▷ m₂) (++-identityʳ S₂))) in
    --     `/id (x & sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)) ·[ C ] (ϕ₁ ∥ ϕ₂))             ≡⟨ cong `/id (&-·ₖ-&/⋯ (sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)))
    --                                                                                                 (ϕ₁ ∥ ϕ₂) x) ⟩
    --     `/id (x & sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))           ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                   (dist-subst-sub _ _ x
    --                                                                                     (wkₖ* S₁ id ↑* (S₂ ▷ m₂))) ⟩
    --     `/id (subx (suby x & wkₖ* S₁ idᵣ ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))    ≡⟨ cong
    --                                                                               (λ ■ → `/id (subx (■ & wkₖ* S₁ idᵣ ↑* (S₂ ▷ m₂))
    --                                                                                             &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                             (subst-here _) ⟩
    --     `/id (subx (here refl & wkₖ* S₁ idᵣ ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂)) ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                   (use-~-hom (↑*-▷ S₂ m₂ (wkₖ* S₁ id)) _ (here refl)) ⟩
    --     `/id (subx (here refl & wkₖ* S₁ id ↑* S₂ ↑ m₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))    ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                   (&-↑-here (wkₖ* S₁ id ↑* S₂)) ⟩
    --     `/id (subx (id/` (here refl)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))                     ≡⟨ refl ⟩
    --     `/id (subx (here refl) & (ϕ₁ ∥ ϕ₂))                                   ≡⟨ cong (λ ■ → `/id (■ & (ϕ₁ ∥ ϕ₂))) (subst-here _) ⟩
    --     `/id (here refl & (ϕ₁ ∥ ϕ₂))                                          ≡⟨ cong (λ ■ → `/id ■)
    --                                                                                   (use-~-hom (∥-▷ ϕ₁ ϕ₂) _ (here refl)) ⟩
    --     `/id (here refl & ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂)))                  ≡⟨ cong (λ ■ → `/id  ■)
    --                                                                                   (&-,ₖ-here (ϕ₁ ∥ ϕ₂ ↓) (here refl & ϕ₂)) ⟩
    --     `/id (here refl & ϕ₂)                                                 ≡⟨ refl ⟩
    --     `/id (x & ϕ₂)                                                         ∎
    --   s x@(there {x = m₂} {xs = S₂} y) →
    --     let C = ckitᵣ in
    --     let sub = subst₂ _→ᵣ_ (cong (_▷ m₂) (++-identityʳ S₂)) (cong (_▷▷ (S₂ ▷ m₂)) (++-identityʳ S₁)) in
    --     let sub' = subst₂ _→ᵣ_ (++-identityʳ S₂) (cong (_▷▷ S₂) (++-identityʳ S₁)) in
    --     let subx = subst (_∋ s) (cong (_▷▷ (S₂ ▷ m₂)) (++-identityʳ S₁)) in
    --     let subx' = subst (_∋ s) (cong (_▷▷ S₂) (++-identityʳ S₁)) in
    --     let suby = subst (_∋ s) (sym (cong (_▷ m₂) (++-identityʳ S₂))) in
    --     let suby' = subst (_∋ s) (sym (++-identityʳ S₂)) in
    --     `/id (x & sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)) ·[ C ] (ϕ₁ ∥ ϕ₂))                   ≡⟨ cong `/id
    --                                                                                         (&-·ₖ-&/⋯ (sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)))
    --                                                                                                   (ϕ₁ ∥ ϕ₂) x) ⟩
    --     `/id (x & sub (wkₖ* S₁ id ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))                 ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ₁ ∥ ϕ₂)))
    --                                                                                         (dist-subst-sub _ _ x
    --                                                                                           (wkₖ* S₁ id ↑* (S₂ ▷ m₂))) ⟩
    --     `/id (subx (suby (there y) & wkₖ* S₁ idᵣ ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))  ≡⟨ cong
    --                                                                                     (λ ■ → `/id (subx (■ & wkₖ* S₁ idᵣ ↑*
    --                                                                                                   (S₂ ▷ m₂)) &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                     (sym (dist-subst' (λ S → S ▷ m₂) there
    --                                                                                       (sym (++-identityʳ S₂))
    --                                                                                       (sym (cong (_▷ m₂) (++-identityʳ S₂)))
    --                                                                                       y)) ⟩
    --     `/id (subx (there (suby' y) & wkₖ* S₁ idᵣ ↑* (S₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂)) ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                         (use-~-hom (↑*-▷ S₂ m₂ _) _ (there (suby' y))) ⟩
    --     `/id (subx (there (suby' y) & wkₖ* S₁ idᵣ ↑* S₂ ↑ m₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))   ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
    --                                                                                         (&-↑-there (wkₖ* S₁ idᵣ ↑* S₂) (suby' y)) ⟩
    --     `/id (subx (wk _ (suby' y & wkₖ* S₁ idᵣ ↑* S₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))         ≡⟨ cong (λ ■ → `/id ■)
    --                                                                                   (use-~-hom (∥-▷ ϕ₁ ϕ₂) _ _) ⟩
    --     `/id (subx (wk _ (suby' y & wkₖ* S₁ idᵣ ↑* S₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ refl ⟩
    --     `/id (subx (there (suby' y & wkₖ* S₁ idᵣ ↑* S₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))
    --                                                                                   (sym (dist-subst' (λ S → S ▷ m₂) there
    --                                                                                           (cong (_▷▷ S₂) (++-identityʳ S₁))
    --                                                                                           (cong (_▷▷ (S₂ ▷ m₂)) (++-identityʳ S₁))
    --                                                                                           (suby' y & wkₖ* S₁ idᵣ ↑* S₂))) ⟩
    --     `/id (there (subx' (suby' y & wkₖ* S₁ idᵣ ↑* S₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ cong `/id (&-,ₖ-there (ϕ₁ ∥ ϕ₂ ↓) (here refl & ϕ₂) _) ⟩
    --     `/id (subx' (suby' y & wkₖ* S₁ idᵣ ↑* S₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂ ↓))             ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] ϕ₁ ∥ (ϕ₂ ↓)))
    --                                                                                         (sym (dist-subst-sub _ _ y
    --                                                                                           (wkₖ* S₁ id ↑* S₂))) ⟩
    --     `/id (y & sub' (wkₖ* S₁ id ↑* S₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂ ↓))                     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯
    --                                                                                                     (sub' (wkₖ* S₁ id ↑* S₂))
    --                                                                                                     (ϕ₁ ∥ ϕ₂ ↓) y)) ⟩
    --     `/id (y & sub' (wkₖ* S₁ id ↑* S₂) ·[ C ] (ϕ₁ ∥ ϕ₂ ↓))                       ≡⟨ use-~ (wk*-∥₁ ϕ₁ (ϕ₂ ↓)) _ y ⟩
    --     `/id (y & ϕ₂ ↓)                                                             ≡⟨ cong `/id (&-↓ ϕ₂ y) ⟩
    --     `/id (x & ϕ₂)                                                               ∎

  -- Specializations for Renamings ------------------------------------------------

  infixl  9  _ᵣ·_  _ᵣ·ᵣ_  _ᵣ·ₛ_
  infixr  9  _∘ᵣ_  _ᵣ∘ᵣ_  _ₛ∘ᵣ_

  private instance _ = kitᵣ; _ = kitₛ; _ = ckitᵣ

  _ᵣ·_ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢_ ⦄
      {S₁} {S₂} {S₃} → S₁ –[ kitᵣ ]→ S₂ → S₂ –[ 𝕂₂ ]→ S₃ → S₁ –[ 𝕂₂ ]→ S₃
  ρ ᵣ· ϕ = ρ ·ₖ ϕ

  _∘ᵣ_ :
    ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂₂ : Kit _∋/⊢_ ⦄
      {S₁} {S₂} {S₃} → S₂ –[ 𝕂₂ ]→ S₃ → S₁ –[ kitᵣ ]→ S₂ → S₁ –[ 𝕂₂ ]→ S₃
  ϕ₂ ∘ᵣ ϕ₁ = ϕ₁ ᵣ· ϕ₂

  _ᵣ·ᵣ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ kitᵣ ]→ S₂ → S₂ –[ kitᵣ ]→ S₃ → S₁ –[ kitᵣ ]→ S₃
  _ᵣ·ₛ_ : ∀ {S₁} {S₂} {S₃} → S₁ –[ kitᵣ ]→ S₂ → S₂ –[ kitₛ ]→ S₃ → S₁ –[ kitₛ ]→ S₃
  _ᵣ∘ᵣ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ kitᵣ ]→ S₃ → S₁ –[ kitᵣ ]→ S₂ → S₁ –[ kitᵣ ]→ S₃
  _ₛ∘ᵣ_ : ∀ {S₁} {S₂} {S₃} → S₂ –[ kitₛ ]→ S₃ → S₁ –[ kitᵣ ]→ S₂ → S₁ –[ kitₛ ]→ S₃
  _ᵣ·ᵣ_ = _ᵣ·_
  _ᵣ·ₛ_ = _ᵣ·_
  _ᵣ∘ᵣ_ = _∘ᵣ_
  _ₛ∘ᵣ_ = _∘ᵣ_

