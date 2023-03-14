open import Kitty.Term.Modes
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitT {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : Traversal 𝕋) (𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋) where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋 renaming (_∋/⊢[_]_ to _∋/⊢[_]'_)
open import Kitty.Term.KitOrder 𝕋 renaming (_⊑ₖ_ to _⊑ₖ'_)
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open Traversal T
open Kit ⦃ … ⦄
open Sub ⦃ … ⦄ renaming (_–[_]→_ to _–[_]→'_)
open SubWithLaws ⦃ … ⦄
open ~-Reasoning
open _⊑ₖ'_ ⦃ … ⦄

private instance _ = 𝕊
private instance _ = kitᵣ; _ = kitₛ

record KitK (𝕂 : Kit) : Set₁ where
  private instance _ = 𝕂
  field
    wkₖ-⋯ :
      ∀ {µ} {m} {mx}
        {x/t : µ ∋/⊢[ 𝕂 ]' id/m→M mx}
      → `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ `/id (wk m x/t)

wkₖ-⋯ᵣ :
  ∀ {µ} {m} {mx} {x : µ ∋ mx}
  → ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡ ` there x
wkₖ-⋯ᵣ {µ} {m} {mx} {x} =
  ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id   ≡⟨ ⋯-var x (wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ⟩
  ` (x & wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id) ≡⟨ cong `_ (&-wkₖ-wk id x) ⟩
  ` (there (x & id))            ≡⟨ cong (λ ■ → ` there ■) (&-id x) ⟩
  ` there x                     ∎

kitkᵣ : KitK kitᵣ
kitkᵣ = record { wkₖ-⋯ = wkₖ-⋯ᵣ }

kitkₛ : KitK kitₛ
kitkₛ = record { wkₖ-⋯ = refl }

open KitK ⦃ … ⦄

private instance _ = kitkᵣ; _ = kitkₛ

record KitWk (𝕂₁ : Kit) : Set₁ where
  private instance _ = 𝕂₁
  field
    ~-wk :
      ∀ ⦃ 𝕂₂ : Kit ⦄ ⦃ KK₂ : KitK 𝕂₂ ⦄ {µ} {m} {mx}
        {x/t₁ : µ ∋/⊢[ 𝕂₁ ]' id/m→M mx}
        {x/t₂ : µ ∋/⊢[ 𝕂₂ ]' id/m→M mx}
      → `/id x/t₁ ≡ `/id x/t₂
      → `/id (wk m x/t₁) ≡ `/id (wk m x/t₂)

open KitWk ⦃ … ⦄

~-wkᵣ :
  ∀ ⦃ 𝕂₂ : Kit ⦄ {µ} {m} {mx}
    {x₁ : µ ∋ mx}
    {x/t₂ : µ ∋/⊢[ 𝕂₂ ]' id/m→M mx}
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
    {x/t₂ : µ ∋/⊢[ 𝕂₂ ]' id/m→M mx}
  → t₁ ≡ `/id x/t₂
  → wk m t₁ ≡ `/id (wk m x/t₂)
~-wkₛ ⦃ 𝕂₂ ⦄ {µ} {m} {mx} {_} {x/t₂} refl =
  wk m (`/id x/t₂)                  ≡⟨⟩
  `/id x/t₂ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ m id ≡⟨ wkₖ-⋯ ⟩
  `/id ⦃ 𝕂₂ ⦄ (wk m x/t₂)           ∎

kitwkₛ : KitWk kitₛ
kitwkₛ = record { ~-wk = ~-wkₛ }

~-cong-wk :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitK 𝕂₁ ⦄ ⦃ K₂ : KitK 𝕂₂ ⦄
    ⦃ W₁ : KitWk 𝕂₁ ⦄ ⦃ W₂ : KitWk 𝕂₂ ⦄
    {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→' µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→' µ₂} →
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
    ⦃ K₁ : KitK 𝕂₁ ⦄ ⦃ K₂ : KitK 𝕂₂ ⦄
    ⦃ W₁ : KitWk 𝕂₁ ⦄ ⦃ W₂ : KitWk 𝕂₂ ⦄
    {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→' µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→' µ₂} →
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
    ⦃ K₁ : KitK 𝕂₁ ⦄ ⦃ K₂ : KitK 𝕂₂ ⦄
    ⦃ W₁ : KitWk 𝕂₁ ⦄ ⦃ W₂ : KitWk 𝕂₂ ⦄
    {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→' µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→' µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑ m) ~ (ϕ' ↑ m)
~-cong-↑ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' =
  (ϕ ↑ m)                        ~⟨ ↑-,ₖ ϕ m ⟩
  (wkₖ _ ϕ  ,ₖ id/` (here refl)) ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') ~ₓ-refl ⟩
  (wkₖ _ ϕ' ,ₖ id/` (here refl)) ~⟨ ~-sym (↑-,ₖ ϕ' m) ⟩
  (ϕ' ↑ m)                       ~∎

~-cong-↑* :
  ∀ ⦃ 𝕂₁ 𝕂₂ ⦄
    ⦃ K₁ : KitK 𝕂₁ ⦄ ⦃ K₂ : KitK 𝕂₂ ⦄
    ⦃ W₁ : KitWk 𝕂₁ ⦄ ⦃ W₂ : KitWk 𝕂₂ ⦄
    {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→' µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→' µ₂} →
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

record KitT : Set₁ where
  field
    instance KitT-kit   : Kit
    instance KitT-kitk  : KitK KitT-kit
    instance KitT-kitwk : KitWk KitT-kit

  open Kit KitT-kit     public
  open KitK KitT-kitk   public
  open KitWk KitT-kitwk public

kittᵣ : KitT
kittᵣ = record
  { KitT-kit   = kitᵣ
  ; KitT-kitk  = kitkᵣ
  ; KitT-kitwk = kitwkᵣ
  }

kittₛ : KitT
kittₛ = record
  { KitT-kit   = kitₛ
  ; KitT-kitk  = kitkₛ
  ; KitT-kitwk = kitwkₛ
  }

_∋/⊢[_]_ : List VarMode → (𝕂 : KitT) → KitT.VarMode/TermMode 𝕂 → Set
µ ∋/⊢[ 𝕂 ] sm = KitT._∋/⊢_ 𝕂 µ sm

_–[_]→_ : List VarMode → KitT → List VarMode → Set
µ₁ –[ 𝕂 ]→ µ₂ = µ₁ –[ KitT.KitT-kit 𝕂 ]→' µ₂ 

_⊑ₖ_ : (𝕂₁ 𝕂₂ : KitT) → Set₁
𝕂₁ ⊑ₖ 𝕂₂ = KitT.KitT-kit 𝕂₁ ⊑ₖ' KitT.KitT-kit 𝕂₂

module _⊑ₖ_ {𝕂₁ 𝕂₂ : KitT} = _⊑ₖ'_ {KitT.KitT-kit 𝕂₁} {KitT.KitT-kit 𝕂₂}
