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

private instance _ = Kᵣ; _ = Kₛ

private variable
  _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ : VarScoped

module Private where
  record KitK (K : Kit _∋/⊢_) : Set₁ where
    private instance _ = K
    field
      wkₖ-⋯ :
        ∀ {S} {s} {sx}
          {x/t : S ∋/⊢[ K ] sx}
        → `/id x/t ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ≡ `/id (wk s x/t)

  wkₖ-⋯ᵣ :
    ∀ {S} {s} {sx} {x : S ∋ sx}
    → ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ≡ ` there x
  wkₖ-⋯ᵣ {S} {s} {sx} {x} =
    ` x ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id   ≡⟨ ⋯-var x (wkₖ ⦃ K = Kᵣ ⦄ s id) ⟩
    ` (x & wkₖ ⦃ K = Kᵣ ⦄ s id) ≡⟨ cong `_ (&-wkₖ-wk id x) ⟩
    ` (there (x & id))            ≡⟨ cong (λ ■ → ` there ■) (&-id x) ⟩
    ` there x                     ∎

  kitkᵣ : KitK Kᵣ
  kitkᵣ = record { wkₖ-⋯ = wkₖ-⋯ᵣ }

  kitkₛ : KitK Kₛ
  kitkₛ = record { wkₖ-⋯ = refl }

  record KitWk (K₁ : Kit _∋/⊢₁_) : Set₁ where
    private instance _ = K₁
    field
      ~-wk :
        ∀ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ KK₂ : KitK K₂ ⦄ {S} {s} {sx}
          {x/t₁ : S ∋/⊢[ K₁ ] sx}
          {x/t₂ : S ∋/⊢[ K₂ ] sx}
        → `/id x/t₁ ≡ `/id x/t₂
        → `/id (wk s x/t₁) ≡ `/id (wk s x/t₂)

  ~-wkᵣ :
    ∀ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ {S} {s} {sx}
      {x₁ : S ∋ sx}
      {x/t₂ : S ∋/⊢[ K₂ ] sx}
    → ` x₁ ≡ `/id x/t₂
    → ` there x₁ ≡ `/id (wk s x/t₂)
  ~-wkᵣ ⦃ K₂ ⦄ {S} {s} {sx} {x₁} {x/t₂} eq =
    ` there x₁                          ≡⟨ sym (id/`/id ⦃ K₂ ⦄ (there x₁)) ⟩
    `/id ⦃ K₂ ⦄ (id/` (there x₁))       ≡⟨ cong (`/id ⦃ K₂ ⦄) (sym (wk-id/` ⦃ K₂ ⦄ s x₁)) ⟩
    `/id ⦃ K₂ ⦄ (wk ⦃ K₂ ⦄ s (id/` x₁)) ≡⟨ cong (λ ■ → `/id ⦃ K₂ ⦄ (wk ⦃ K₂ ⦄ s ■))
                                                (`/id-injective (trans (id/`/id ⦃ K₂ ⦄ x₁) eq)) ⟩
    `/id ⦃ K₂ ⦄ (wk s x/t₂)             ∎

  kitwkᵣ : KitWk Kᵣ
  kitwkᵣ = record { ~-wk = λ ⦃ K₂ ⦄ x → ~-wkᵣ ⦃ K₂ ⦄ x }

  ~-wkₛ :
    ∀ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ KK₂ : KitK K₂ ⦄ {S} {s} {sx}
      {t₁ : S ⊢ sx}
      {x/t₂ : S ∋/⊢[ K₂ ] sx}
    → t₁ ≡ `/id x/t₂
    → wk s t₁ ≡ `/id (wk s x/t₂)
  ~-wkₛ ⦃ K₂ ⦄ ⦃ KK₂ ⦄ {S} {s} {sx} {_} {x/t₂} refl =
    wk s (`/id x/t₂)                  ≡⟨⟩
    `/id x/t₂ ⋯ wkₖ ⦃ K = Kᵣ ⦄ s id ≡⟨ KitK.wkₖ-⋯ KK₂ ⟩
    `/id ⦃ K₂ ⦄ (wk s x/t₂)           ∎

  kitwkₛ : KitWk Kₛ
  kitwkₛ = record { ~-wk = ~-wkₛ }

open Private

record KitT (K : Kit _∋/⊢_) : Set₁ where
  field
    KitT-KitK  : KitK K
    KitT-KitWk : KitWk K

wk-`/id :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ KT : KitT K ⦄ {S} s {sx}
    (x/t : S ∋/⊢[ K ] sx)
  → wk s (`/id x/t) ≡ `/id (wk s x/t)
wk-`/id ⦃ KT = KT ⦄ s x/t = KitK.wkₖ-⋯ (KitT.KitT-KitK KT)

~-wk :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ KT₁ : KitT K₁ ⦄ ⦃ KT₂ : KitT K₂ ⦄ {S} {s} {sx}
    {x/t₁ : S ∋/⊢[ K₁ ] sx}
    {x/t₂ : S ∋/⊢[ K₂ ] sx}
  → `/id x/t₁ ≡ `/id x/t₂
  → `/id (wk s x/t₁) ≡ `/id (wk s x/t₂)
~-wk ⦃ KT₁ = KT₁ ⦄ ⦃ KT₂ = KT₂ ⦄ = KitWk.~-wk (KitT.KitT-KitWk KT₁) ⦃ KK₂ = KitT.KitT-KitK KT₂ ⦄ 

Wᵣ : KitT Kᵣ
Wᵣ = record
  { KitT-KitK  = kitkᵣ
  ; KitT-KitWk = kitwkᵣ
  }

Wₛ : KitT Kₛ
Wₛ = record
  { KitT-KitK  = kitkₛ
  ; KitT-KitWk = kitwkₛ
  }

open KitT ⦃ … ⦄

private instance _ = Wᵣ; _ = Wₛ

~-cong-wk :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ 
    ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
    {S₁} {S₂} {s} {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂} →
  ϕ ~ ϕ' →
  wkₖ s ϕ ~ wkₖ s ϕ'
~-cong-wk ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ W₁ ⦄ ⦃ W₂ ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' = mk-~ λ sx x →
  `/id ⦃ K₁ ⦄ (x & wkₖ _ ϕ)   ≡⟨ cong `/id (&-wkₖ-wk ϕ x) ⟩
  `/id ⦃ K₁ ⦄ (wk _ (x & ϕ))  ≡⟨ ~-wk (use-~ ϕ~ϕ' _ x) ⟩
  `/id ⦃ K₂ ⦄ (wk _ (x & ϕ')) ≡⟨ cong `/id (sym (&-wkₖ-wk ϕ' x)) ⟩
  `/id ⦃ K₂ ⦄ (x & wkₖ _ ϕ')  ∎

open ~-Reasoning 
~-cong-wk* :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
    ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
    {S₁} {S₂} {S} {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂} →
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
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
    ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
    {S₁} {S₂} {s} {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂} →
  ϕ ~ ϕ' →
  (ϕ ↑ s) ~ (ϕ' ↑ s)
~-cong-↑ ⦃ K₁ ⦄ ⦃ K₂ ⦄ {S₁} {S₂} {s} {ϕ} {ϕ'} ϕ~ϕ' =
  (ϕ ↑ s)                        ~⟨ ↑-,ₖ ϕ s ⟩
  (wkₖ _ ϕ  ,ₖ id/` (here refl)) ~⟨ ~-cong-,ₖ (~-cong-wk ϕ~ϕ') (~ₓ-refl ⦃ K₁ ⦄ ⦃ K₂ ⦄) ⟩
  (wkₖ _ ϕ' ,ₖ id/` (here refl)) ~⟨ ~-sym (↑-,ₖ ϕ' s) ⟩
  (ϕ' ↑ s)                       ~∎

~-cong-↑* :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
    ⦃ W₁ : KitT K₁ ⦄ ⦃ W₂ : KitT K₂ ⦄
    {S₁} {S₂} {S} {ϕ : S₁ –[ K₁ ]→ S₂} {ϕ' : S₁ –[ K₂ ]→ S₂} →
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
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : KitT K ⦄ {S₁ S₂} (ϕ : S₁ –[ K ]→ S₂) S S' →
  let sub = subst₂ (_–[ K ]→_) (++-assoc S' S S₁) (++-assoc S' S S₂) in
  ϕ ↑* S ↑* S' ~ sub (ϕ ↑* (S ▷▷ S'))
↑*-▷▷ ⦃ K ⦄ {S₁} {S₂} ϕ S [] =
  let sub = subst₂ (_–[ K ]→_) (++-assoc [] S S₁) (++-assoc [] S S₂) in
  ϕ ↑* S ↑* []         ~⟨ ↑*-[] (ϕ ↑* S) ⟩
  ϕ ↑* (S ▷▷ [])       ~⟨⟩
  sub (ϕ ↑* (S ▷▷ [])) ~∎
↑*-▷▷ ⦃ K ⦄ {S₁} {S₂} ϕ S (S' ▷ s') =
  let sub = subst₂ (_–[ K ]→_) (++-assoc (S' ▷ s') S S₁) (++-assoc (S' ▷ s') S S₂) in
  let sub' = subst₂ (_–[ K ]→_) (++-assoc S' S S₁) (++-assoc S' S S₂) in
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

