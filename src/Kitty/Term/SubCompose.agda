open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)

module Kitty.Term.SubCompose
    {𝕄 : Modes}
    {𝕋 : Terms 𝕄}
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
open Modes 𝕄
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
      ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {M}  {_∋/⊢_ : Scoped M}  ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ µ₃}
      → µ₁ –[ 𝕂₁ ]→ µ₂
      → µ₂ –[ 𝕂₂ ]→ µ₃
      → µ₁ –[ 𝕂  ]→ µ₃

    &-·ₖ-&/⋯ :
      ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
        {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
        {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
        ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} {m}
        (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
        (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
        (x : µ₁ ∋ m)
      → x & (ϕ₁ ·ₖ ϕ₂) ≡ (x & ϕ₁) &/⋯ ϕ₂

  -- TODO: This can be more heterogeneous.
  ~-cong-· :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃}
      {ϕ₁ ϕ₁' : µ₁ –[ 𝕂₁ ]→ µ₂}
      {ϕ₂ ϕ₂' : µ₂ –[ 𝕂₂ ]→ µ₃}
    → ϕ₁ ~ ϕ₁'
    → ϕ₂ ~ ϕ₂'
    → (ϕ₁ ·ₖ ϕ₂) ~ (ϕ₁' ·ₖ ϕ₂')
  ~-cong-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} {ϕ₁} {ϕ₁'} {ϕ₂} {ϕ₂'} ϕ₁~ϕ₁' ϕ₂~ϕ₂' = mk-~ λ m x →
    `/id (x & (ϕ₁  ·ₖ ϕ₂ )) ≡⟨ cong `/id (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x) ⟩
    `/id (x & ϕ₁  &/⋯ ϕ₂ )  ≡⟨ cong `/id (~-cong-&/⋯ (use-~-hom ϕ₁~ϕ₁' _ x) ϕ₂~ϕ₂') ⟩
    `/id (x & ϕ₁' &/⋯ ϕ₂')  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ₁' ϕ₂' x)) ⟩
    `/id (x & (ϕ₁' ·ₖ ϕ₂')) ∎

  -- This is used to prove the variable case of ⋯-assoc.
  tm-⋯-· :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} {m}
      (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
      (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
      (x : µ₁ ∋ m)
    → `/id (x & ϕ₁) ⋯ ϕ₂ ≡ `/id (x & (ϕ₁ ·ₖ ϕ₂))
  tm-⋯-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {µ₃} {m} ϕ₁ ϕ₂ x =
    `/id (x & ϕ₁) ⋯ ϕ₂    ≡⟨ sym (&/⋯-⋯ (x & ϕ₁) ϕ₂) ⟩
    `/id (x & ϕ₁ &/⋯ ϕ₂)  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ₁ ϕ₂ x)) ⟩
    `/id (x & (ϕ₁ ·ₖ ϕ₂)) ∎

  dist-↑-· :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} m
      (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
      (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    → ((ϕ₁ ·ₖ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m))
  dist-↑-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₃} m ϕ₁ ϕ₂ = mk-~ λ where
    mx x@(here refl) →
      `/id ⦃ 𝕂 ⦄ (x & ((ϕ₁ ·ₖ ϕ₂) ↑ m))          ≡⟨ cong `/id (&-↑-here (ϕ₁ ·ₖ ϕ₂)) ⟩
      `/id ⦃ 𝕂 ⦄ (id/` (here refl))              ≡⟨ id/`/id ⦃ 𝕂 ⦄ (here refl) ⟩
      ` here refl                                ≡⟨ sym (id/`/id ⦃ 𝕂₂ ⦄ (here refl)) ⟩
      `/id ⦃ 𝕂₂ ⦄ (id/` (here refl))             ≡⟨ ι-`/id (id/` (here refl)) ⟩
      `/id ⦃ 𝕂 ⦄ (ι-∋/⊢ (id/` ⦃ 𝕂₂ ⦄ (here refl)))      ≡⟨ cong (λ ■ → `/id (ι-∋/⊢ ■)) (sym (&-↑-here ϕ₂)) ⟩
      `/id ⦃ 𝕂 ⦄ (ι-∋/⊢ (here refl & (ϕ₂ ↑ m)))  ≡⟨ cong `/id (sym (&/⋯-& (here refl) (ϕ₂ ↑ m))) ⟩
      `/id ⦃ 𝕂 ⦄ (id/` (here refl) &/⋯ (ϕ₂ ↑ m)) ≡⟨ cong (λ ■ → `/id (■ &/⋯ ϕ₂ ↑ m)) (sym (&-↑-here ϕ₁)) ⟩
      `/id ⦃ 𝕂 ⦄ (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m))     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ m) (ϕ₂ ↑ m) x)) ⟩
      `/id ⦃ 𝕂 ⦄ (x & ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)))    ∎
    mx x@(there y) →
      `/id (x & ((ϕ₁ ·ₖ ϕ₂) ↑ m))          ≡⟨ cong `/id (&-↑-there (ϕ₁ ·ₖ ϕ₂) y) ⟩
      `/id (wk _ (y & (ϕ₁ ·ₖ ϕ₂)))         ≡⟨ cong (λ ■ → `/id (wk _ ■)) (&-·ₖ-&/⋯ ϕ₁ ϕ₂ y) ⟩
      `/id (wk _ (y & ϕ₁ &/⋯ ϕ₂))          ≡⟨ cong `/id (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
      `/id (wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ m))    ≡⟨ cong (λ ■ → `/id (■ &/⋯ (ϕ₂ ↑ m))) (sym (&-↑-there ϕ₁ y)) ⟩
      `/id (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m))     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ (ϕ₁ ↑ m) (ϕ₂ ↑ m) x)) ⟩
      `/id (x & ((ϕ₁ ↑ m) ·ₖ (ϕ₂ ↑ m)))    ∎

  dist-↑*-· :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ µ₃}
      µ (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
    → ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ~ ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ))
  dist-↑*-· []      ϕ₁ ϕ₂ =
    ((ϕ₁ ·ₖ ϕ₂) ↑* [])                  ~⟨ ↑*-[] (ϕ₁ ·ₖ ϕ₂) ⟩
    ϕ₁ ·ₖ ϕ₂                            ~⟨ ~-sym (~-cong-· (↑*-[] ϕ₁) (↑*-[] ϕ₂)) ⟩
    ((ϕ₁ ↑* []) ·ₖ (ϕ₂ ↑* []))          ~∎
  dist-↑*-· (µ ▷ m) ϕ₁ ϕ₂ =
    (ϕ₁ ·ₖ ϕ₂) ↑* (µ ▷ m)               ~⟨ ↑*-▷ µ m (ϕ₁ ·ₖ ϕ₂) ⟩
    ((ϕ₁ ·ₖ ϕ₂) ↑* µ) ↑ m               ~⟨ ~-cong-↑' (dist-↑*-· µ ϕ₁ ϕ₂) ⟩
    ((ϕ₁ ↑* µ) ·ₖ (ϕ₂ ↑* µ)) ↑ m        ~⟨ dist-↑-· m (ϕ₁ ↑* µ) (ϕ₂ ↑* µ) ⟩
    ((ϕ₁ ↑* µ) ↑ m) ·ₖ ((ϕ₂ ↑* µ) ↑ m)  ~⟨ ~-sym (~-cong-· (↑*-▷ µ m ϕ₁) (↑*-▷ µ m ϕ₂)) ⟩
    (ϕ₁ ↑* (µ ▷ m)) ·ₖ (ϕ₂ ↑* (µ ▷ m))  ~∎

  -- dist-,ₖ-· : ∀ {m}
  --               (ϕ₁ : µ₁ –[ 𝕂₁ ]→ µ₂)
  --               (ϕ₂ : µ₂ –[ 𝕂₂ ]→ µ₃)
  --               (x/t : µ₂ ∋/⊢[ 𝕂₁ ] id/m→M m)
  --             → let sub = subst (µ₃ ∋/⊢[ 𝕂₁⊔ 𝕂₂ ]_) (ι-id/m→M m) in
  --               ((ϕ₁ ·ₖ ϕ₂) ,ₖ sub (x/t &/⋯ ϕ₂)) ~ (ϕ₁ ,ₖ x/t ·ₖ ϕ₂)

  _∘ₖ_ :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃}
    → µ₂ –[ 𝕂₂ ]→ µ₃
    → µ₁ –[ 𝕂₁ ]→ µ₂
    → µ₁ –[ 𝕂 ]→ µ₃
  ϕ₂ ∘ₖ ϕ₁ = ϕ₁ ·ₖ ϕ₂

  infixl  9  _·[_]_
  infixr  9  _∘[_]_

  _·[_]_ :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      {µ₁} {µ₂} {µ₃}
    → µ₁ –[ 𝕂₁ ]→ µ₂
    → ComposeKit 𝕂₁ 𝕂₂ 𝕂
    → µ₂ –[ 𝕂₂ ]→ µ₃
    → µ₁ –[ 𝕂 ]→ µ₃
  ϕ₁ ·[ C ] ϕ₂ = _·ₖ_ ⦃ C = C ⦄ ϕ₁ ϕ₂


  _∘[_]_ :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {µ₃}
    → µ₂ –[ 𝕂₂ ]→ µ₃
    → ComposeKit 𝕂₁ 𝕂₂ 𝕂
    → µ₁ –[ 𝕂₁ ]→ µ₂
    → µ₁ –[ 𝕂 ]→ µ₃
  ϕ₂ ∘[ C ] ϕ₁ = _∘ₖ_ ⦃ C = C ⦄ ϕ₂ ϕ₁

  ·-idʳ :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄) ~ ϕ
  ·-idʳ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} ϕ = mk-~ λ mx x →
    `/id (x & (ϕ ·ₖ id ⦃ 𝕂 = 𝕂₂ ⦄)) ≡⟨ cong (`/id) (&-·ₖ-&/⋯ ϕ id x) ⟩
    `/id (x & ϕ &/⋯ id ⦃ 𝕂 = 𝕂₂ ⦄)  ≡⟨ &/⋯-⋯ (x & ϕ) id ⟩
    `/id (x & ϕ) ⋯ id ⦃ 𝕂 = 𝕂₂ ⦄    ≡⟨ ⋯-id (`/id (x & ϕ)) ⟩
    `/id (x & ϕ)                    ∎

  ·-idˡ :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂)
    → (id ⦃ 𝕂 = 𝕂₁ ⦄ ·ₖ ϕ) ~ ϕ
  ·-idˡ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} ϕ = mk-~ λ mx x →
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
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁} {µ₂} {m}
      (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) (x/t : µ₂ ∋/⊢[ 𝕂₂ ] id/m→M m)
    → (wkₖ _ id ·ₖ (ϕ ,ₖ x/t)) ~ ϕ
  wk-cancels-,ₖ-· ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {m} ϕ x/t = mk-~ λ mx x →
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
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      {µ₁} {µ₂} {m}
      (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂)
    → wkₖ m ϕ ~ (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id)
  wk-ϕ-id ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ ⦃ W ⦄ {µ₁} {µ₂} {m} ϕ = mk-~ λ mx x →
    `/id (x & wkₖ m ϕ)                    ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
    `/id (wk m (x & ϕ))                   ≡⟨ ι-`/id (wk m (x & ϕ)) ⟩
    `/id (ι-∋/⊢ (wk m (x & ϕ)))           ≡⟨ cong `/id (sym (&/⋯-wk (x & ϕ))) ⟩
    `/id (x & ϕ &/⋯ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id)  ≡⟨ cong `/id (sym (&-·ₖ-&/⋯ ϕ (wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id) x)) ⟩
    `/id (x & (ϕ ·ₖ wkₖ ⦃ 𝕂 = 𝕂₂ ⦄ m id)) ∎

  ↑-wk :
    ∀ {M₁} {_∋/⊢₁_ : Scoped M₁} ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄
      {M₂} {_∋/⊢₂_ : Scoped M₂} ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
      {M}  {_∋/⊢_ : Scoped M}   ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      ⦃ C₁ : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
      ⦃ C₂ : ComposeKit 𝕂₂ 𝕂₁ 𝕂 ⦄
      ⦃ W₁ : KitT 𝕂₁ ⦄
      ⦃ W₂ : KitT 𝕂₂ ⦄
      {µ₁} {µ₂} (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) m
    → (ϕ ·[ C₁ ] wkₖ m id) ~ (wkₖ m id ·[ C₂ ] (ϕ ↑ m))
  ↑-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} ϕ m =
      (ϕ ·[ C₁ ] wkₖ m id)                             ~⟨ ~-sym (wk-ϕ-id ϕ) ⟩
      wkₖ m ϕ                                          ~⟨ ~-sym (wk-cancels-,ₖ-· (wkₖ m ϕ) (id/` (here refl))) ⟩
      (wkₖ m id ·[ C₂ ] (wkₖ m ϕ ,ₖ id/` (here refl))) ~⟨ ~-cong-· ~-refl (~-sym (↑-,ₖ ϕ m)) ⟩
      (wkₖ m id ·[ C₂ ] (ϕ ↑ m))                       ~∎

  -- wk-↓ :
  --   ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄ {µ₁ µ₂ m₁} (ϕ : (µ₁ ▷ m₁) –[ 𝕂₂ ]→ µ₂) →
  --   wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id ·ₖ ϕ ~ ϕ ↓
  -- wk-↓ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦃ C ⦄ {µ₁} {µ₂} {m₁} ϕ m x =
  --   Kit.`/id 𝕂 (x & (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id ·ₖ ϕ))            ≡⟨ cong (Kit.`/id 𝕂) (&-·ₖ-&/⋯ (wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id) ϕ x) ⟩
  --   Kit.`/id 𝕂 (x & wkₖ ⦃ 𝕂 = 𝕂₁ ⦄ m₁ id &/⋯[ C ] ϕ)        ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (■ &/⋯[ C ] ϕ))
  --                                                                    (&-wkₖ-wk id x) ⟩
  --   Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ (x & id ⦃ 𝕂 = 𝕂₁ ⦄) &/⋯[ C ] ϕ) ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ ■ &/⋯[ C ] ϕ))
  --                                                                       (&-id x) ⟩
  --   Kit.`/id 𝕂 (Kit.wk 𝕂₁ _ (Kit.id/` 𝕂₁ x) &/⋯[ C ] ϕ)     ≡⟨ cong (λ ■ → Kit.`/id 𝕂 (■ &/⋯[ C ] ϕ))
  --                                                                      (Kit.wk-id/` 𝕂₁ _ x) ⟩
  --   Kit.`/id 𝕂 (Kit.id/` 𝕂₁ (there x) &/⋯[ C ] ϕ)           ≡⟨ cong (Kit.`/id 𝕂) (&/⋯-& (there x) ϕ) ⟩
  --   Kit.`/id 𝕂 (ι-∋/⊢ ⦃ 𝕂₂⊑𝕂₁⊔𝕂₂ ⦃ C ⦄ ⦄ (there x & ϕ))     ≡⟨ sym (ι-`/id (there x & ϕ)) ⟩
  --   Kit.`/id 𝕂₂ (there x & ϕ)                               ≡⟨ sym (cong (Kit.`/id 𝕂₂) (&-↓ ϕ x)) ⟩
  --   Kit.`/id 𝕂₂ (x & (ϕ ↓))                                 ∎

  -- -- TODO: Move to different file
  -- module _ where
  --   private instance _ = kitᵣ; _ = ckitᵣ

  --   subst-here : ∀ {µ₁ µ₂ : List VarMode} {m} (p : µ₁ ▷ m ≡ µ₂ ▷ m) →
  --     subst (_∋ m) p (here {x = m} {xs = µ₁} refl) ≡ here refl
  --   subst-here refl = refl

  --   dist-subst-sub : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₁' µ₂ µ₂' m} →
  --     (p : µ₁ ≡ µ₁') →
  --     (q : µ₂ ≡ µ₂') →
  --     (x : µ₁' ∋ m) →
  --     (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
  --     let sub₁₂ = subst₂ (_–[ 𝕂 ]→_) p q in
  --     let sub₁⁻¹ = subst (_∋ m) (sym p) in
  --     let sub₂ = subst (_∋/⊢[ 𝕂 ] id/m→M m) q in
  --     x & sub₁₂ ϕ ≡ sub₂ (sub₁⁻¹ x & ϕ)
  --   dist-subst-sub refl refl x ϕ = refl

  --   dist-subst-sub' : ∀ ⦃ 𝕂 ⦄ {µ₁ µ₁' µ₂ µ₂' M} →
  --     (p : µ₁ ≡ µ₁') →
  --     (q : µ₂ ≡ µ₂') →
  --     (t : µ₁' ⊢ M) →
  --     (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
  --     let sub₁₂ = subst₂ (_–[ 𝕂 ]→_) p q in
  --     let sub₁⁻¹ = subst (_⊢ M) (sym p) in
  --     let sub₂ = subst (_⊢ M) q in
  --     t ⋯ sub₁₂ ϕ ≡ sub₂ (sub₁⁻¹ t ⋯ ϕ)
  --   dist-subst-sub' refl refl x ϕ = refl

  --   -- NOTE: the &/⋯[ C ] can be replaced by &.
  --   wk*-∥₁ :
  --     ∀ ⦃ 𝕂 ⦄ {µ₁ µ₂ µ} (ϕ₁ : µ₁ –[ 𝕂 ]→ µ) (ϕ₂ : µ₂ –[ 𝕂 ]→ µ) →
  --     let sub = subst₂ (_→ᵣ_) (++-identityʳ µ₂) (cong (_▷▷ µ₂) (++-identityʳ µ₁)) in
  --     sub (wkₖ* µ₁ (id {µ = []}) ↑* µ₂) ·[ ckitᵣ ] (ϕ₁ ∥ ϕ₂) ~ ϕ₂
  --   wk*-∥₁ ⦃ 𝕂 ⦄ {µ₁ = µ₁} {µ₂ ▷ m₂} {µ} ϕ₁ ϕ₂ m x@(here refl) =
  --     let C = ckitᵣ in
  --     let sub = subst₂ _→ᵣ_ (cong (_▷ m₂) (++-identityʳ µ₂)) (cong (_▷▷ (µ₂ ▷ m₂)) (++-identityʳ µ₁)) in
  --     let subx = subst (_∋ m₂) (cong (_▷▷ (µ₂ ▷ m₂)) (++-identityʳ µ₁)) in
  --     let suby = subst (_∋ m₂) (sym (cong (_▷ m₂) (++-identityʳ µ₂))) in
  --     `/id (x & sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)) ·[ C ] (ϕ₁ ∥ ϕ₂))             ≡⟨ cong `/id (&-·ₖ-&/⋯ (sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)))
  --                                                                                                  (ϕ₁ ∥ ϕ₂) x) ⟩
  --     `/id (x & sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))           ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                   (dist-subst-sub _ _ x
  --                                                                                     (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂))) ⟩
  --     `/id (subx (suby x & wkₖ* µ₁ idᵣ ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))    ≡⟨ cong
  --                                                                               (λ ■ → `/id (subx (■ & wkₖ* µ₁ idᵣ ↑* (µ₂ ▷ m₂))
  --                                                                                             &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                             (subst-here _) ⟩
  --     `/id (subx (here refl & wkₖ* µ₁ idᵣ ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂)) ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                   (~→~' (↑*-▷ µ₂ m₂ (wkₖ* µ₁ id)) _ (here refl)) ⟩
  --     `/id (subx (here refl & wkₖ* µ₁ id ↑* µ₂ ↑ m₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))    ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                   (&-↑-here (wkₖ* µ₁ id ↑* µ₂)) ⟩
  --     `/id (subx (id/` (here refl)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))                     ≡⟨ refl ⟩
  --     `/id (subx (here refl) & (ϕ₁ ∥ ϕ₂))                                   ≡⟨ cong (λ ■ → `/id (■ & (ϕ₁ ∥ ϕ₂))) (subst-here _) ⟩
  --     `/id (here refl & (ϕ₁ ∥ ϕ₂))                                          ≡⟨ cong (λ ■ → `/id ■)
  --                                                                                   (~→~' (∥-▷ ϕ₁ ϕ₂) _ (here refl)) ⟩
  --     `/id (here refl & ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂)))                  ≡⟨ cong (λ ■ → `/id  ■)
  --                                                                                   (&-,ₖ-here (ϕ₁ ∥ ϕ₂ ↓) (here refl & ϕ₂)) ⟩
  --     `/id (here refl & ϕ₂)                                                 ≡⟨ refl ⟩
  --     `/id (x & ϕ₂)                                                         ∎
  --   wk*-∥₁ {µ₁ = µ₁} {µ₂ ▷ m₂} {µ} ϕ₁ ϕ₂ m x@(there y) =
  --     let C = ckitᵣ in
  --     let sub = subst₂ _→ᵣ_ (cong (_▷ m₂) (++-identityʳ µ₂)) (cong (_▷▷ (µ₂ ▷ m₂)) (++-identityʳ µ₁)) in
  --     let sub' = subst₂ _→ᵣ_ (++-identityʳ µ₂) (cong (_▷▷ µ₂) (++-identityʳ µ₁)) in
  --     let subx = subst (_∋ m) (cong (_▷▷ (µ₂ ▷ m₂)) (++-identityʳ µ₁)) in
  --     let subx' = subst (_∋ m) (cong (_▷▷ µ₂) (++-identityʳ µ₁)) in
  --     let suby = subst (_∋ m) (sym (cong (_▷ m₂) (++-identityʳ µ₂))) in
  --     let suby' = subst (_∋ m) (sym (++-identityʳ µ₂)) in
  --     `/id (x & sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)) ·[ C ] (ϕ₁ ∥ ϕ₂))                   ≡⟨ cong `/id
  --                                                                                         (&-·ₖ-&/⋯ (sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)))
  --                                                                                                   (ϕ₁ ∥ ϕ₂) x) ⟩
  --     `/id (x & sub (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))                 ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ₁ ∥ ϕ₂)))
  --                                                                                         (dist-subst-sub _ _ x
  --                                                                                           (wkₖ* µ₁ id ↑* (µ₂ ▷ m₂))) ⟩
  --     `/id (subx (suby (there y) & wkₖ* µ₁ idᵣ ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))  ≡⟨ cong
  --                                                                                      (λ ■ → `/id (subx (■ & wkₖ* µ₁ idᵣ ↑*
  --                                                                                                    (µ₂ ▷ m₂)) &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                      (sym (dist-subst' (λ µ → µ ▷ m₂) there
  --                                                                                        (sym (++-identityʳ µ₂))
  --                                                                                        (sym (cong (_▷ m₂) (++-identityʳ µ₂)))
  --                                                                                        y)) ⟩
  --     `/id (subx (there (suby' y) & wkₖ* µ₁ idᵣ ↑* (µ₂ ▷ m₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂)) ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                         (~→~' (↑*-▷ µ₂ m₂ _) _ (there (suby' y))) ⟩
  --     `/id (subx (there (suby' y) & wkₖ* µ₁ idᵣ ↑* µ₂ ↑ m₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))   ≡⟨ cong (λ ■ → `/id (subx ■ &/⋯[ C ] ϕ₁ ∥ ϕ₂))
  --                                                                                         (&-↑-there (wkₖ* µ₁ idᵣ ↑* µ₂) (suby' y)) ⟩
  --     `/id (subx (wk _ (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂)) &/⋯[ C ] (ϕ₁ ∥ ϕ₂))         ≡⟨ cong (λ ■ → `/id ■)
  --                                                                                    (~→~' (∥-▷ ϕ₁ ϕ₂) _ _) ⟩
  --     `/id (subx (wk _ (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ refl ⟩
  --     `/id (subx (there (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] (ϕ₁ ∥ (ϕ₂ ↓)) ,ₖ (here refl & ϕ₂)))
  --                                                                                    (sym (dist-subst' (λ µ → µ ▷ m₂) there
  --                                                                                           (cong (_▷▷ µ₂) (++-identityʳ µ₁))
  --                                                                                           (cong (_▷▷ (µ₂ ▷ m₂)) (++-identityʳ µ₁))
  --                                                                                           (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂))) ⟩
  --     `/id (there (subx' (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂)) &/⋯[ C ] ((ϕ₁ ∥ ϕ₂ ↓) ,ₖ (here refl & ϕ₂))) ≡⟨ cong `/id (&-,ₖ-there (ϕ₁ ∥ ϕ₂ ↓) (here refl & ϕ₂) _) ⟩
  --     `/id (subx' (suby' y & wkₖ* µ₁ idᵣ ↑* µ₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂ ↓))             ≡⟨ cong (λ ■ → `/id (■ &/⋯[ C ] ϕ₁ ∥ (ϕ₂ ↓)))
  --                                                                                         (sym (dist-subst-sub _ _ y
  --                                                                                           (wkₖ* µ₁ id ↑* µ₂))) ⟩
  --     `/id (y & sub' (wkₖ* µ₁ id ↑* µ₂) &/⋯[ C ] (ϕ₁ ∥ ϕ₂ ↓))                     ≡⟨ cong `/id (sym (&-·ₖ-&/⋯
  --                                                                                                     (sub' (wkₖ* µ₁ id ↑* µ₂))
  --                                                                                                     (ϕ₁ ∥ ϕ₂ ↓) y)) ⟩
  --     `/id (y & sub' (wkₖ* µ₁ id ↑* µ₂) ·[ C ] (ϕ₁ ∥ ϕ₂ ↓))                       ≡⟨ wk*-∥₁ ϕ₁ (ϕ₂ ↓) _ y ⟩
  --     `/id (y & ϕ₂ ↓)                                                             ≡⟨ cong `/id (&-↓ ϕ₂ y) ⟩
  --     `/id (x & ϕ₂)                                                               ∎

  -- -- Specializations for Renamings ------------------------------------------------

  -- infixl  9  _ᵣ·_  _ᵣ·ᵣ_  _ᵣ·ₛ_
  -- infixr  9  _∘ᵣ_  _ᵣ∘ᵣ_  _ₛ∘ᵣ_

  -- private instance _ = kitᵣ; _ = kitₛ; _ = ckitᵣ

  -- _ᵣ·_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₃
  -- ρ ᵣ· ϕ = ρ ·ₖ ϕ

  -- _∘ᵣ_ : ∀ ⦃ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ₃} → µ₂ –[ 𝕂₂ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ 𝕂₂ ]→ µ₃
  -- ϕ₂ ∘ᵣ ϕ₁ = ϕ₁ ᵣ· ϕ₂

  -- _ᵣ·ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₃
  -- _ᵣ·ₛ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₁ –[ kitᵣ ]→ µ₂ → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitₛ ]→ µ₃
  -- _ᵣ∘ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitᵣ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ kitᵣ ]→ µ₃
  -- _ₛ∘ᵣ_ : ∀ {µ₁} {µ₂} {µ₃} → µ₂ –[ kitₛ ]→ µ₃ → µ₁ –[ kitᵣ ]→ µ₂ → µ₁ –[ kitₛ ]→ µ₃
  -- _ᵣ·ᵣ_ = _ᵣ·_
  -- _ᵣ·ₛ_ = _ᵣ·_
  -- _ᵣ∘ᵣ_ = _∘ᵣ_
  -- _ₛ∘ᵣ_ = _∘ᵣ_

