open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
import Kitty.Term.Sub

module Kitty.Term.KitT
    {𝕋 : Terms}
    {ℓ} {𝕊 : Kitty.Term.Sub.SubWithLaws 𝕋 ℓ}
    (T : Traversal 𝕋 𝕊)
  where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Kitty.Term.Prelude
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.Sub 𝕋
open import Kitty.Util.SubstProperties

open Terms 𝕋
open Traversal T
open Kit ⦃ … ⦄
open SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open ~-Reasoning
open _⊑ₖ_ ⦃ … ⦄

private instance _ = kitᵣ; _ = kitₛ

private variable
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

module Private where
  record KitK (𝕂 : Kit _∋/⊢_) : Set₁ where
    private instance _ = 𝕂
    field
      wkₖ-⋯ :
        ∀ {S} {s} {sx}
          {x/t : S ∋/⊢[ 𝕂 ] sx}
        → `/id x/t ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id ≡ `/id (wk s x/t)

  wkₖ-⋯ᵣ :
    ∀ {S} {s} {sx} {x : S ∋ sx}
    → ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id ≡ ` there x
  wkₖ-⋯ᵣ {S} {s} {sx} {x} =
    ` x ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id   ≡⟨ ⋯-var x (wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id) ⟩
    ` (x & wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id) ≡⟨ cong `_ (&-wkₖ-wk id x) ⟩
    ` (there (x & id))            ≡⟨ cong (λ ■ → ` there ■) (&-id x) ⟩
    ` there x                     ∎

  kitkᵣ : KitK kitᵣ
  kitkᵣ = record { wkₖ-⋯ = wkₖ-⋯ᵣ }

  kitkₛ : KitK kitₛ
  kitkₛ = record { wkₖ-⋯ = refl }

  record KitWk (𝕂₁ : Kit _∋/⊢₁_) : Set₁ where
    private instance _ = 𝕂₁
    field
      ~-wk :
        ∀ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ KK₂ : KitK 𝕂₂ ⦄ {S} {s} {sx}
          {x/t₁ : S ∋/⊢[ 𝕂₁ ] sx}
          {x/t₂ : S ∋/⊢[ 𝕂₂ ] sx}
        → `/id x/t₁ ≡ `/id x/t₂
        → `/id (wk s x/t₁) ≡ `/id (wk s x/t₂)

  ~-wkᵣ :
    ∀ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ {S} {s} {sx}
      {x₁ : S ∋ sx}
      {x/t₂ : S ∋/⊢[ 𝕂₂ ] sx}
    → ` x₁ ≡ `/id x/t₂
    → ` there x₁ ≡ `/id (wk s x/t₂)
  ~-wkᵣ ⦃ 𝕂₂ ⦄ {S} {s} {sx} {x₁} {x/t₂} eq =
    ` there x₁                          ≡⟨ sym (id/`/id ⦃ 𝕂₂ ⦄ (there x₁)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (id/` (there x₁))       ≡⟨ cong (`/id ⦃ 𝕂₂ ⦄) (sym (wk-id/` ⦃ 𝕂₂ ⦄ s x₁)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk ⦃ 𝕂₂ ⦄ s (id/` x₁)) ≡⟨ cong (λ ■ → `/id ⦃ 𝕂₂ ⦄ (wk ⦃ 𝕂₂ ⦄ s ■))
                                                (`/id-injective (trans (id/`/id ⦃ 𝕂₂ ⦄ x₁) eq)) ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk s x/t₂)             ∎

  kitwkᵣ : KitWk kitᵣ
  kitwkᵣ = record { ~-wk = λ ⦃ 𝕂₂ ⦄ x → ~-wkᵣ ⦃ 𝕂₂ ⦄ x }

  ~-wkₛ :
    ∀ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ KK₂ : KitK 𝕂₂ ⦄ {S} {s} {sx}
      {t₁ : S ⊢ sx}
      {x/t₂ : S ∋/⊢[ 𝕂₂ ] sx}
    → t₁ ≡ `/id x/t₂
    → wk s t₁ ≡ `/id (wk s x/t₂)
  ~-wkₛ ⦃ 𝕂₂ ⦄ ⦃ KK₂ ⦄ {S} {s} {sx} {_} {x/t₂} refl =
    wk s (`/id x/t₂)                  ≡⟨⟩
    `/id x/t₂ ⋯ wkₖ ⦃ 𝕂 = kitᵣ ⦄ s id ≡⟨ KitK.wkₖ-⋯ KK₂ ⟩
    `/id ⦃ 𝕂₂ ⦄ (wk s x/t₂)           ∎

  kitwkₛ : KitWk kitₛ
  kitwkₛ = record { ~-wk = ~-wkₛ }

open Private

record KitT (𝕂 : Kit _∋/⊢_) : Set₁ where
  field
    KitT-KitK  : KitK 𝕂
    KitT-KitWk : KitWk 𝕂

wk-`/id :
  ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ KT : KitT 𝕂 ⦄ {S} s {sx}
    (x/t : S ∋/⊢[ 𝕂 ] sx)
  → wk s (`/id x/t) ≡ `/id (wk s x/t)
wk-`/id ⦃ KT = KT ⦄ s x/t = KitK.wkₖ-⋯ (KitT.KitT-KitK KT)

~-wk :
  ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ ⦃ KT₁ : KitT 𝕂₁ ⦄ ⦃ KT₂ : KitT 𝕂₂ ⦄ {S} {s} {sx}
    {x/t₁ : S ∋/⊢[ 𝕂₁ ] sx}
    {x/t₂ : S ∋/⊢[ 𝕂₂ ] sx}
  → `/id x/t₁ ≡ `/id x/t₂
  → `/id (wk s x/t₁) ≡ `/id (wk s x/t₂)
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
  ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄ 
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {S₁} {S₂} {s} {ϕ : S₁ –[ 𝕂₁ ]→ S₂} {ϕ' : S₁ –[ 𝕂₂ ]→ S₂} →
  ϕ ~ ϕ' →
  wkₖ s ϕ ~ wkₖ s ϕ'
~-cong-wk ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~ λ sx x →
  `/id ⦃ 𝕂₁ ⦄ (x & wkₖ _ ϕ)   ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
  `/id ⦃ 𝕂₁ ⦄ (wk _ (x & ϕ))  ≡⟨ ~-wk (use-~ ϕ~ϕ' _ x) ⟩
  `/id ⦃ 𝕂₂ ⦄ (wk _ (x & ϕ')) ≡⟨ cong `/id (sym (&-wkₖ-wk ϕ' x)) ⟩
  `/id ⦃ 𝕂₂ ⦄ (x & wkₖ _ ϕ')  ∎

open ~-Reasoning 
~-cong-wk* :
  ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {S₁} {S₂} {S} {ϕ : S₁ –[ 𝕂₁ ]→ S₂} {ϕ' : S₁ –[ 𝕂₂ ]→ S₂} →
  ϕ ~ ϕ' →
  wkₖ* S ϕ ~ wkₖ* S ϕ'
~-cong-wk* {S = []} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* [] ϕ  ~⟨ wkₖ*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (wkₖ*-[] ϕ') ⟩
  wkₖ* [] ϕ' ~∎
~-cong-wk* {S = S ▷ s} {ϕ} {ϕ'} ϕ~ϕ' =
  wkₖ* (S ▷ s) ϕ    ~⟨ wkₖ*-▷ S s ϕ ⟩
  wkₖ s (wkₖ* S ϕ)  ~⟨ ~-cong-wk (~-cong-wk* ϕ~ϕ') ⟩
  wkₖ s (wkₖ* S ϕ') ~⟨ ~-sym (wkₖ*-▷ S s ϕ') ⟩
  wkₖ* (S ▷ s) ϕ'   ~∎

~-cong-↑ :
  ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {S₁} {S₂} {s} {ϕ : S₁ –[ 𝕂₁ ]→ S₂} {ϕ' : S₁ –[ 𝕂₂ ]→ S₂} →
  ϕ ~ ϕ' →
  (ϕ ↑ s) ~ (ϕ' ↑ s)
~-cong-↑ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' =
  (ϕ ↑ s)                        ~⟨ ↑-,ₖ ϕ s ⟩
  (wkₖ _ ϕ  ,ₖ id/` (here refl)) ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') (~ₓ-refl ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄) ⟩
  (wkₖ _ ϕ' ,ₖ id/` (here refl)) ~⟨ ~-sym (↑-,ₖ ϕ' s) ⟩
  (ϕ' ↑ s)                       ~∎

~-cong-↑* :
  ∀ ⦃ 𝕂₁ : Kit _∋/⊢₁_ ⦄ ⦃ 𝕂₂ : Kit _∋/⊢₂_ ⦄
    ⦃ K₁ : KitT 𝕂₁ ⦄ ⦃ K₂ : KitT 𝕂₂ ⦄
    {S₁} {S₂} {S} {ϕ : S₁ –[ 𝕂₁ ]→ S₂} {ϕ' : S₁ –[ 𝕂₂ ]→ S₂} →
  ϕ ~ ϕ' →
  (ϕ ↑* S) ~ (ϕ' ↑* S)
~-cong-↑* {S = []}    {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* [])  ~⟨ ↑*-[] ϕ ⟩
  ϕ          ~⟨ ϕ~ϕ' ⟩
  ϕ'         ~⟨ ~-sym (↑*-[] ϕ') ⟩
  (ϕ' ↑* []) ~∎
~-cong-↑* {S = S ▷ s} {ϕ = ϕ} {ϕ' = ϕ'} ϕ~ϕ' =
  (ϕ ↑* (S ▷ s))  ~⟨ ↑*-▷ S s ϕ ⟩
  (ϕ ↑* S) ↑ s    ~⟨ ~-cong-↑ (~-cong-↑* ϕ~ϕ') ⟩
  (ϕ' ↑* S) ↑ s   ~⟨ ~-sym (↑*-▷ S s ϕ') ⟩
  (ϕ' ↑* (S ▷ s)) ~∎

open import Data.List.Properties using (++-assoc)
↑*-▷▷ :
  ∀ ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ K : KitT 𝕂 ⦄ {S₁ S₂} (ϕ : S₁ –[ 𝕂 ]→ S₂) S S' →
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc S' S S₁) (++-assoc S' S S₂) in
  ϕ ↑* S ↑* S' ~ sub (ϕ ↑* (S ▷▷ S'))
↑*-▷▷ ⦃ 𝕂 ⦄ {S₁} {S₂} ϕ S [] =
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc [] S S₁) (++-assoc [] S S₂) in
  ϕ ↑* S ↑* []         ~⟨ ↑*-[] (ϕ ↑* S) ⟩
  ϕ ↑* (S ▷▷ [])       ~⟨⟩
  sub (ϕ ↑* (S ▷▷ [])) ~∎
↑*-▷▷ ⦃ 𝕂 ⦄ {S₁} {S₂} ϕ S (S' ▷ s') =
  let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc (S' ▷ s') S S₁) (++-assoc (S' ▷ s') S S₂) in
  let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc S' S S₁) (++-assoc S' S S₂) in
  ϕ ↑* S ↑* (S' ▷ s')         ~⟨ ↑*-▷ S' s' (ϕ ↑* S) ⟩
  (ϕ ↑* S ↑* S') ↑ s'         ~⟨ ~-cong-↑ (↑*-▷▷ ϕ S S') ⟩
  sub' (ϕ ↑* (S ▷▷ S')) ↑ s'  ~≡⟨ dist-subst₂'
                                   (λ S → S ▷ s') (λ S → S ▷ s') (_↑ s')
                                   (++-assoc S' S S₁) (++-assoc (S' ▷ s') S S₁ )
                                   (++-assoc S' S S₂) (++-assoc (S' ▷ s') S S₂)
                                   (ϕ ↑* (S ▷▷ S')) ⟩
  sub (ϕ ↑* (S ▷▷ S') ↑ s')   ~⟨ ~-sym (~-cong-subst₂ _ _ (↑*-▷ (S ▷▷ S') s' ϕ)) ⟩
  sub (ϕ ↑* ((S ▷▷ S') ▷ s')) ~⟨⟩
  sub (ϕ ↑* (S ▷▷ (S' ▷ s'))) ~∎

