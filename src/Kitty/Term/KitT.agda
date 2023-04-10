open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitT {𝕄 : Modes} (𝕋 : Terms 𝕄) {ℓ} (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ) (T : Traversal 𝕋 𝕊) where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open Kit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private instance _ = kitᵣ; _ = kitₛ

module Private where
  record KitK (𝕂 : Kit) : Set₁ where
    private instance _ = 𝕂
    field
      wkₖ-⋯' :
        ∀ {µ} {m} {m/M}
          {x/t : µ ∋/⊢[ 𝕂 ] m/M}
        → `/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ `/id' (wk m x/t)

    wkₖ-⋯ :
      ∀ {µ} {m} {mx}
        {x/t : µ ∋/⊢[ 𝕂 ] id/m→M mx}
      → `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ `/id (wk m x/t)
    wkₖ-⋯ {µ} {m} {mx} {x/t} =
      let sub₁ = subst (µ ⊢_) (id/m→M/id mx) in
      let sub₂ = subst ((µ ▷ m) ⊢_) (id/m→M/id mx) in
      `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id         ≡⟨ cong (_⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) (`/id≡`/id' x/t) ⟩
      sub₁ (`/id' x/t) ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡⟨ dist-subst (_⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) (id/m→M/id mx) (`/id' x/t) ⟩
      sub₂ (`/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ≡⟨ cong sub₂ wkₖ-⋯' ⟩
      sub₂ (`/id' (wk m x/t))                   ≡⟨ sym (`/id≡`/id' (wk m x/t)) ⟩
      `/id (wk m x/t)                           ∎

  wkₖ-⋯ᵣ :
    ∀ {µ} {m} {mx} {x : µ ∋ mx}
    → ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ ` there x
  wkₖ-⋯ᵣ {µ} {m} {mx} {x} =
    ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id   ≡⟨ ⋯-var x (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ⟩
    ` (x & wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ≡⟨ cong `_ (&-wkₖ-wk id x) ⟩
    ` (there (x & id))            ≡⟨ cong (λ ■ → ` there ■) (&-id x) ⟩
    ` there x                     ∎

  kitkᵣ : KitK kitᵣ
  kitkᵣ = record { wkₖ-⋯' = wkₖ-⋯ᵣ }

  kitkₛ : KitK kitₛ
  kitkₛ = record { wkₖ-⋯' = refl }

  record KitWk (𝕂₁ : Kit) : Set₁ where
    private instance _ = 𝕂₁
    field
      ~-wk :
        ∀ ⦃ 𝕂₂ : Kit ⦄ ⦃ KK₂ : KitK 𝕂₂ ⦄ {µ} {m} {mx}
          {x/t₁ : µ ∋/⊢[ 𝕂₁ ] id/m→M mx}
          {x/t₂ : µ ∋/⊢[ 𝕂₂ ] id/m→M mx}
        → `/id x/t₁ ≡ `/id x/t₂
        → `/id (wk m x/t₁) ≡ `/id (wk m x/t₂)

  ~-wkᵣ :
    ∀ ⦃ 𝕂₂ : Kit ⦄ {µ} {m} {mx}
      {x₁ : µ ∋ mx}
      {x/t₂ : µ ∋/⊢[ 𝕂₂ ] id/m→M mx}
    → ` x₁ ≡ `/id x/t₂
    → ` there x₁ ≡ `/id (wk m x/t₂)
  ~-wkᵣ ⦃ 𝕂₂ ⦄ {µ} {m} {mx} {x₁} {x/t₂} eq =
    ` there x₁                          ≡⟨ sym (id/`/id (there x₁)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (id/` (there x₁))       ≡⟨ cong (`/id ⦃ 𝕂₂ ⦄) (sym (wk-id/` ⦃ 𝕂₂ ⦄ m x₁)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk ⦃ 𝕂₂ ⦄ m (id/` x₁)) ≡⟨ cong (λ ■ → `/id ⦃ 𝕂₂ ⦄ (wk ⦃ 𝕂₂ ⦄ m ■)) (`/id-injective (trans (id/`/id x₁) eq)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk m x/t₂)             ∎

  kitwkᵣ : KitWk kitᵣ
  kitwkᵣ = record { ~-wk = ~-wkᵣ }

  ~-wkₛ :
    ∀ ⦃ 𝕂₂ : Kit ⦄ ⦃ KK₂ : KitK 𝕂₂ ⦄ {µ} {m} {mx}
      {t₁ : µ ⊢ m→M mx}
      {x/t₂ : µ ∋/⊢[ 𝕂₂ ] id/m→M mx}
    → t₁ ≡ `/id x/t₂
    → wk m t₁ ≡ `/id (wk m x/t₂)
  ~-wkₛ ⦃ 𝕂₂ ⦄ ⦃ KK₂ ⦄ {µ} {m} {mx} {_} {x/t₂} refl =
    wk m (`/id x/t₂)                  ≡⟨⟩
    `/id x/t₂ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡⟨ KitK.wkₖ-⋯ KK₂ ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk m x/t₂)           ∎

  kitwkₛ : KitWk kitₛ
  kitwkₛ = record { ~-wk = ~-wkₛ }

open Private

record KitT (𝕂 : Kit) : Set₁ where
  field
    KitT-KitK  : KitK 𝕂
    KitT-KitWk : KitWk 𝕂

wkₖ-⋯' :
  ∀ ⦃ 𝕂 ⦄ ⦃ KT : KitT 𝕂 ⦄ {µ} {m} {m/M}
    {x/t : µ ∋/⊢[ 𝕂 ] m/M}
  → `/id' x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ `/id' (wk m x/t)
wkₖ-⋯' ⦃ KT = KT ⦄ = KitK.wkₖ-⋯' (KitT.KitT-KitK KT)

wkₖ-⋯ :
  ∀ ⦃ 𝕂 ⦄ ⦃ KT : KitT 𝕂 ⦄ {µ} {m} {mx}
    {x/t : µ ∋/⊢[ 𝕂 ] id/m→M mx}
  → `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ `/id (wk m x/t)
wkₖ-⋯ ⦃ KT = KT ⦄ = KitK.wkₖ-⋯ (KitT.KitT-KitK KT)

~-wk :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄ {µ} {m} {mx}
    {x/t₁ : µ ∋/⊢[ 𝕂₁ ] id/m→M mx}
    {x/t₂ : µ ∋/⊢[ 𝕂₂ ] id/m→M mx}
  → `/id x/t₁ ≡ `/id x/t₂
  → `/id (wk m x/t₁) ≡ `/id (wk m x/t₂)
~-wk ⦃ KT₁ = KT₁ ⦄ ⦃ KT₂ = KT₂ ⦄ = KitWk.~-wk (KitT.KitT-KitWk KT₁) ⦃ KK₂ = KitT.KitT-KitK KT₂ ⦄ 

kittᵣ : KitT kitᵣ
kittᵣ = record
  { KitT-KitK  = kitkᵣ
  ; KitT-KitWk = kitwkᵣ
  }

kittₛ : KitT kitₛ
kittₛ = record
  { KitT-KitK  = kitkₛ
  ; KitT-KitWk = kitwkₛ
  }

open KitT ⦃ … ⦄

private instance _ = kittᵣ; _ = kittₛ

~-cong-wk :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  wkₖ m ϕ ~ wkₖ m ϕ'
~-cong-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x =
  `/id ⦃ 𝕂₁ ⦄ (x & wkₖ _ ϕ)   ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
  `/id ⦃ 𝕂₁ ⦄ (wk _ (x & ϕ))  ≡⟨ ~-wk (ϕ~ϕ' _ x) ⟩
  `/id ⦃ 𝕂₂ ⦄ (wk _ (x & ϕ')) ≡⟨ cong `/id (sym (&-wkₖ-wk ϕ' x)) ⟩
  `/id ⦃ 𝕂₂ ⦄ (x & wkₖ _ ϕ')  ∎

open ~-Reasoning 
~-cong-wk* :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  wkₖ* µ ϕ ~ wkₖ* µ ϕ'
~-cong-wk* {µ = []} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
  wkₖ* [] ϕ' ~∎
~-cong-wk* {µ = µ ▷ m} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* (µ ▷ m) ϕ    ~⟨ wkₖ*-▷ µ m ϕ ⟩
  wkₖ m (wkₖ* µ ϕ)  ~⟨ ~-cong-wk (~-cong-wk* ϕ~ϕ') ⟩
  wkₖ m (wkₖ* µ ϕ') ~⟨ ~-sym (wkₖ*-▷ µ m ϕ') ⟩
  wkₖ* (µ ▷ m) ϕ'   ~∎

~-cong-↑ :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑ m) ~ (ϕ' ↑ m)
~-cong-↑ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' =
  (ϕ ↑ m)                        ~⟨ ↑-,ₖ ϕ m ⟩
  (wkₖ _ ϕ  ,ₖ id/` (here refl)) ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') ~ₓ-refl ⟩
  (wkₖ _ ϕ' ,ₖ id/` (here refl)) ~⟨ ~-sym (↑-,ₖ ϕ' m) ⟩
  (ϕ' ↑ m)                       ~∎

~-cong-↑* :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑* µ) ~ (ϕ' ↑* µ)
~-cong-↑* {µ = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
  (ϕ' ↑* []) ~∎
~-cong-↑* {µ = µ ▷ m} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* (µ ▷ m))  ~⟨ ↑*-▷ µ m ϕ ⟩
  (ϕ ↑* µ) ↑ m    ~⟨ ~-cong-↑ (~-cong-↑* ϕ~ϕ') ⟩
  (ϕ' ↑* µ) ↑ m   ~⟨ ~-sym (↑*-▷ µ m ϕ') ⟩
  (ϕ' ↑* (µ ▷ m)) ~∎

open import Data.List.Properties using (++-assoc)
↑*-▷▷ :
  ∀ ⦃ 𝕂 : Kit ⦄ ⦃ K : KitT 𝕂 ⦄ {µ₁ µ₂} (ϕ : µ₁ –[ 𝕂 ]→ µ₂) µ µ' →
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ' µ µ₁) (++-assoc µ' µ µ₂) in
  ϕ ↑* µ ↑* µ' ~ sub (ϕ ↑* (µ ▷▷ µ'))
↑*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} ϕ µ [] =
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc [] µ µ₁) (++-assoc [] µ µ₂) in
  ϕ ↑* µ ↑* []         ~⟨ ↑*-[] (ϕ ↑* µ) ⟩
  ϕ ↑* (µ ▷▷ [])       ~⟨⟩
  sub (ϕ ↑* (µ ▷▷ [])) ~∎
↑*-▷▷ ⦃ 𝕂 ⦄ {µ₁} {µ₂} ϕ µ (µ' ▷ m') =
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc (µ' ▷ m') µ µ₁) (++-assoc (µ' ▷ m') µ µ₂) in
  let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ' µ µ₁) (++-assoc µ' µ µ₂) in
  ϕ ↑* µ ↑* (µ' ▷ m')         ~⟨ ↑*-▷ µ' m' (ϕ ↑* µ) ⟩
  (ϕ ↑* µ ↑* µ') ↑ m'         ~⟨ ~-cong-↑ (↑*-▷▷ ϕ µ µ') ⟩
  sub' (ϕ ↑* (µ ▷▷ µ')) ↑ m'  ~≡⟨ dist-subst₂'
                                   (λ µ → µ ▷ m') (λ µ → µ ▷ m') (_↑ m')
                                   (++-assoc µ' µ µ₁) (++-assoc (µ' ▷ m') µ µ₁ )
                                   (++-assoc µ' µ µ₂) (++-assoc (µ' ▷ m') µ µ₂)
                                   (ϕ ↑* (µ ▷▷ µ')) ⟩
  sub (ϕ ↑* (µ ▷▷ µ') ↑ m')   ~⟨ ~-sym (~-cong-subst₂ _ _ (↑*-▷ (µ ▷▷ µ') m' ϕ)) ⟩
  sub (ϕ ↑* ((µ ▷▷ µ') ▷ m')) ~⟨⟩
  sub (ϕ ↑* (µ ▷▷ (µ' ▷ m'))) ~∎

