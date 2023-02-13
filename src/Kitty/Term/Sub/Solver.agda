open import Kitty.Term.Modes
import Kitty.Term.Sub

module Kitty.Term.Sub.Solver {𝕄 : Modes} (𝕋 : Terms 𝕄) (S : Kitty.Term.Sub.SubWithLaws 𝕋) where

open import Data.List using (List; [])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Kitty.Term.Prelude
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function using (_$_)

open Modes 𝕄
open Terms 𝕋

open import Kitty.Term.Kit 𝕋 hiding (_–[_]→_)
open import Kitty.Term.Sub 𝕋

open Kit ⦃ … ⦄ using (VarMode/TermMode; _∋/⊢_; id/m→M; m→M/id; id/m→M/id; id/`; `/id; `/id'; id/`/id; id/`/id'; wk; wk-id/`; wk*)
open SubWithLaws S
open Sub SubWithLaws-Sub
open ~-Reasoning

data _–[_]→`_ : List VarMode → Kit → List VarMode → Set where
  emb   : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→` µ₂
  []ₖ`  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→` []
  []*`  : ∀ ⦃ 𝕂 ⦄ {µ₂} → [] –[ 𝕂 ]→` µ₂
  _,ₖ`_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→` µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→` µ₂
  wkₖ`  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` (µ₂ ▷ m)
  wkₖ*` : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₂'} µ → µ₂' ≡ µ₂ ▷▷ µ → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` µ₂'

-- ∥ is ,ₖ* so wk can be pushed under it
-- wk* (ϕ₁ ,ₖ* ϕ₂) ≡ wk* ϕ ,ₖ* wk* ϕ₂
-- with id-wk* and ∥-assoc we can bring (ϕ₁ ∥ … ∥ ϕₙ) in the form (f₁ id-wk* ∥ … ∥ fₙ id-wk*)

-- ↓ cancels ,ₖ
-- ↓ may get stuck at emb
-- ↓* can cancel ∥, more precisely:
--   (ϕ₁ ∥ ϕ₂) ↓ ≡ ϕ₁ ∥ ϕ₂ ↓  if ϕ₂ has µ₁ ≢ []
--   (ϕ₁ ∥ ϕ₂) ↓ ≡ ϕ₁ ↓       otherwise
--   (ϕ₁ ∥ ϕ₂) ↓* (m + n) ≡ ϕ₁ ↓* m ∥ ϕ₂ ↓* n  if ϕ₂ has length µ₁ ≡ n
--     probably best to have solver for µ equations if we use ↓*

-- (ϕ ↑* µ) is ϕ ∥ id {µ} ?

-- The Normalform
data _–[_]→N_ : List VarMode → Kit → List VarMode → Set where
  -- All wk, wk*, [], []*, id get pushed in here
  -- TODO: id can also appear in the middle with ∥
  id-wk* : ∀ ⦃ 𝕂 ⦄ µ₁ µ₁' µ₂ → (µ₁ ▷▷ µ₁') –[ 𝕂 ]→N µ₂
  -- Embedding of real substitution thats not ~ []*
  emb    : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → µ₁ –[ 𝕂 ]→N µ₂
  -- []ₖ`  : ∀ ⦃ 𝕂 ⦄ → [] –[ 𝕂 ]→` []
  -- []*`  : ∀ ⦃ 𝕂 ⦄ {µ₂} → [] –[ 𝕂 ]→` µ₂
  -- _,ₖ`_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {m} → µ₁ –[ 𝕂 ]→` µ₂ → µ₂ ∋/⊢[ 𝕂 ] id/m→M m → (µ₁ ▷ m) –[ 𝕂 ]→` µ₂
  -- wkₖ`  : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} m → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` (µ₂ ▷ m)
  -- wkₖ*` : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {µ₂'} µ → µ₂' ≡ µ₂ ▷▷ µ → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` µ₂'

⟦_⟧ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→ µ₂
⟦ emb ϕ ⟧           = ϕ
⟦ []ₖ` ⟧            = []ₖ
⟦ []*` ⟧            = []*
⟦ ϕ` ,ₖ` x/t ⟧      = ⟦ ϕ` ⟧ ,ₖ x/t
⟦ wkₖ` m ϕ` ⟧       = wkₖ m ⟦ ϕ` ⟧
⟦ wkₖ*` µ refl ϕ` ⟧ = wkₖ* µ ⟦ ϕ` ⟧

--------------------------------------------------------------------------------

push-wk* : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` (µ₂ ▷▷ µ)
push-wk* µ (emb x)                               = emb (wkₖ* µ x)
push-wk* ⦃ 𝕂 ⦄ µ []ₖ`                            = subst ([] –[ 𝕂 ]→`_) (sym (++-identityʳ µ)) ([]*` {µ})
push-wk* µ []*`                                  = []*`
push-wk* µ (ϕ` ,ₖ` x/t)                          = push-wk* µ ϕ` ,ₖ` wk* _ x/t
push-wk* ⦃ 𝕂 ⦄ {µ₁} µ (wkₖ` {µ₂ = µ₂} m ϕ`)      = subst (µ₁ –[ 𝕂 ]→`_) (++-assoc µ ([] ▷ m) µ₂) (push-wk* (([] ▷ m) ▷▷ µ) ϕ`)
push-wk* ⦃ 𝕂 ⦄ {µ₁} µ (wkₖ*` {µ₂ = µ₂} µ' eq ϕ`) = subst (µ₁ –[ 𝕂 ]→`_) (trans (++-assoc µ µ' µ₂) (cong (_▷▷ µ) (sym eq))) (push-wk* (µ' ▷▷ µ) ϕ`)

trans-redᵣ : ∀ {ℓ} {A : Set ℓ} {a b : A} (eq : a ≡ b) →
  trans eq refl ≡ eq
trans-redᵣ refl = refl

open import Kitty.Util.SubstProperties

push-wk*-sem : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} µ → (ϕ` : µ₁ –[ 𝕂 ]→` µ₂) →
  ⟦ wkₖ*` µ refl ϕ` ⟧ ~ ⟦ push-wk* µ ϕ` ⟧
push-wk*-sem µ (emb ϕ)       = ~-refl
push-wk*-sem ⦃ 𝕂 ⦄ µ (ϕ` ,ₖ` x/t)  =
  wkₖ* µ (⟦ ϕ` ⟧ ,ₖ x/t)                 ~⟨ dist-wk*-,ₖ µ ⟦ ϕ` ⟧ x/t ⟩
  (wkₖ* µ ⟦ ϕ` ⟧ ,ₖ Kit.wk* 𝕂 _ x/t)     ~⟨⟩
  (⟦ wkₖ*` µ refl ϕ` ⟧ ,ₖ Kit.wk* 𝕂 _ x/t)    ~⟨ ~-cong-,ₖ (push-wk*-sem µ ϕ`) refl ⟩
  (⟦ push-wk* µ ϕ` ⟧ ,ₖ Kit.wk* 𝕂 _ x/t) ~∎
push-wk*-sem ⦃ 𝕂 ⦄ {µ₁} µ (wkₖ` {µ₂ = µ₂} m ϕ`) =
  -- TODO: Factor out wkₖ*` case in mutual block and call it here
  let µ' = [] ▷ m in
  let sub₁` = subst (µ₁ –[ 𝕂 ]→`_) (++-assoc µ µ' µ₂) in
  let sub₂` = subst (µ₁ –[ 𝕂 ]→`_) (++-assoc µ µ' µ₂) in
  let sub₂ = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
  ⟦ wkₖ*` µ refl (wkₖ` m ϕ`) ⟧        ~⟨⟩
  wkₖ* µ (wkₖ m ⟦ ϕ` ⟧)               ~⟨ wkₖ-▷▷ µ m ⟦ ϕ` ⟧ ⟩
  sub₂ (wkₖ* (µ' ▷▷ µ) ⟦ ϕ` ⟧)        ~⟨⟩
  sub₂ ⟦ wkₖ*` (µ' ▷▷ µ) refl ϕ` ⟧    ~⟨ ~-cong-subst-µ₂ _ (push-wk*-sem (µ' ▷▷ µ) ϕ`) ⟩
  sub₂ ⟦ push-wk* (µ' ▷▷ µ) ϕ` ⟧      ~≡⟨ sym (dist-subst ⟦_⟧ (++-assoc µ µ' µ₂) (push-wk* (µ' ▷▷ µ) ϕ`) ) ⟩
  ⟦ sub₂` (push-wk* (µ' ▷▷ µ) ϕ`) ⟧   ~⟨⟩
  ⟦ push-wk* µ (wkₖ` m ϕ`) ⟧          ~∎
push-wk*-sem ⦃ 𝕂 ⦄ {µ₁} µ (wkₖ*` {µ₂ = µ₂} µ' refl ϕ`) = -- {!!}
  let sub₁` = subst (µ₁ –[ 𝕂 ]→`_) (trans (++-assoc µ µ' µ₂) (cong (_▷▷ µ) (sym refl))) in
  let sub₂` = subst (µ₁ –[ 𝕂 ]→`_) (++-assoc µ µ' µ₂) in
  let sub₂ = subst (µ₁ –[ 𝕂 ]→_) (++-assoc µ µ' µ₂) in
  ⟦ wkₖ*` µ refl (wkₖ*` µ' refl ϕ`) ⟧ ~⟨⟩
  wkₖ* µ (wkₖ* µ' ⟦ ϕ` ⟧)             ~⟨ wkₖ*-▷▷ µ µ' ⟦ ϕ` ⟧ ⟩
  sub₂ (wkₖ* (µ' ▷▷ µ) ⟦ ϕ` ⟧)        ~⟨⟩
  sub₂ ⟦ wkₖ*` (µ' ▷▷ µ) refl ϕ` ⟧    ~⟨ ~-cong-subst-µ₂ _ (push-wk*-sem (µ' ▷▷ µ) ϕ`) ⟩
  sub₂ ⟦ push-wk* (µ' ▷▷ µ) ϕ` ⟧      ~≡⟨ sym (dist-subst ⟦_⟧ (++-assoc µ µ' µ₂) (push-wk* (µ' ▷▷ µ) ϕ`) ) ⟩
  ⟦ sub₂` (push-wk* (µ' ▷▷ µ) ϕ`) ⟧   ~≡⟨ cong (λ ■ → ⟦ subst (µ₁ –[ 𝕂 ]→`_) ■ (push-wk* (µ' ▷▷ µ) ϕ`) ⟧)
                                               (sym (trans-redᵣ (++-assoc µ µ' µ₂))) ⟩
  ⟦ sub₁` (push-wk* (µ' ▷▷ µ) ϕ`) ⟧   ~⟨⟩
  ⟦ push-wk* µ (wkₖ*` µ' refl ϕ`) ⟧   ~∎

push-wk*-sem' : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ` : µ₁ –[ 𝕂 ]→` µ₂) →
  ⟦ ϕ` ⟧ ~ ⟦ push-wk* [] ϕ` ⟧
push-wk*-sem' ϕ` =
  ⟦ ϕ` ⟧               ~⟨ ~-sym (wkₖ*-[] ⟦ ϕ` ⟧) ⟩
  ⟦ wkₖ*` [] refl ϕ` ⟧ ~⟨ push-wk*-sem [] ϕ` ⟩
  ⟦ push-wk* [] ϕ` ⟧   ~∎

--------------------------------------------------------------------------------

[]-eta : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` µ₂
[]-eta {µ₁} (emb x)    with µ₁
...                       | []      = []*`
...                       | µ₁ ▷ m₁ = emb x
[]-eta []ₖ`            = []ₖ`
[]-eta []*`            = []*`
[]-eta (ϕ` ,ₖ` x/t)    = []-eta ϕ` ,ₖ` x/t
[]-eta (wkₖ` m ϕ`)     = wkₖ` m ([]-eta ϕ`)
[]-eta (wkₖ*` µ eq ϕ`) = wkₖ*` µ eq ([]-eta ϕ`)

[]-eta-sem : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ` : µ₁ –[ 𝕂 ]→` µ₂) →
  ⟦ ϕ` ⟧ ~ ⟦ []-eta ϕ` ⟧
[]-eta-sem {µ₁ = []}     (emb x) = λ m ()
[]-eta-sem {µ₁ = µ₁ ▷ m} (emb x) = ~-refl
[]-eta-sem []ₖ`                  = ~-refl
[]-eta-sem []*`                  = ~-refl
[]-eta-sem (ϕ` ,ₖ` x/t)          = ~-cong-,ₖ ([]-eta-sem ϕ`) refl
[]-eta-sem (wkₖ` m ϕ`)           = ~-cong-wk ([]-eta-sem ϕ`)
[]-eta-sem (wkₖ*` µ refl ϕ`)     = ~-cong-wk* ([]-eta-sem ϕ`)

--------------------------------------------------------------------------------

norm : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→` µ₂ → µ₁ –[ 𝕂 ]→` µ₂
norm ϕ` = []-eta (push-wk* [] ϕ`)

norm-sem :  ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ` : µ₁ –[ 𝕂 ]→` µ₂) →
  ⟦ norm ϕ` ⟧ ~ ⟦ ϕ` ⟧
norm-sem ϕ` =
  ⟦ []-eta (push-wk* [] ϕ`) ⟧ ~⟨ ~-sym ([]-eta-sem (push-wk* [] ϕ`)) ⟩
  ⟦ push-wk* [] ϕ` ⟧          ~⟨ ~-sym (push-wk*-sem' ϕ`) ⟩
  ⟦ ϕ` ⟧                      ~∎

--------------------------------------------------------------------------------

data _≈_ ⦃ 𝕂 ⦄ : ∀ {µ₁} {µ₂} → (ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂ ) → Set where
  ≈-emb : ∀ {µ₁ µ₂} {ϕ₁ ϕ₂ : µ₁ –[ 𝕂 ]→ µ₂} → ϕ₁ ~ ϕ₂ → emb ϕ₁ ≈ emb ϕ₂
  ≈-[]ₖ : []ₖ` ≈ []ₖ`
  ≈-[]* : ∀ {µ} → []*` {µ} ≈ []*` {µ}
  ≈-,ₖ : ∀ {µ₁} {µ₂} {m} {ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂} {x/t₁ x/t₂ : µ₂ ∋/⊢[ 𝕂 ] id/m→M m} → 
    ϕ₁` ≈ ϕ₂` →
    x/t₁ ≡ x/t₂ →
    (ϕ₁` ,ₖ` x/t₁) ≈ (ϕ₂` ,ₖ` x/t₂)
  ≈-wkₖ*` : ∀ {µ₁} {µ₂} {µ₂'} {µ} {eq₁ eq₂ : µ₂' ≡ µ₂ ▷▷ µ} {ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂} →
    eq₁ ≡ eq₂ →
    ϕ₁` ≈ ϕ₂` →
    wkₖ*` µ eq₁ ϕ₁` ≈ wkₖ*` µ eq₂ ϕ₂`

-- _≈_ : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂ ) → Set
-- ϕ₁` ≈ ϕ₂` = norm ϕ₁` ≡ norm ϕ₂`

sound : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂ )
  → norm ϕ₁` ≡ norm ϕ₂`
  → ⟦ ϕ₁` ⟧ ~ ⟦ ϕ₂` ⟧
sound ϕ₁` ϕ₂` eq =
  ⟦ ϕ₁` ⟧      ~⟨ ~-sym (norm-sem ϕ₁`) ⟩
  ⟦ norm ϕ₁` ⟧ ~⟨ (λ m x → cong (λ ■ → apₖ ⟦ ■ ⟧ m x) eq ) ⟩
  ⟦ norm ϕ₂` ⟧ ~⟨ norm-sem ϕ₂` ⟩
  ⟦ ϕ₂` ⟧      ~∎

[]≡▷▷ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} →
  xs ▷▷ ys ≡ [] →
  xs ≡ [] × ys ≡ []
[]≡▷▷ {xs = xs} {ys = []} eq = eq , refl
[]≡▷▷ {xs = xs} {ys = ys ▷ x} ()

[]≡▷▷₁ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} →
  xs ▷▷ ys ≡ [] →
  xs ≡ []
[]≡▷▷₁ eq = proj₁ ([]≡▷▷ eq)

[]≡▷▷₂ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} →
  xs ▷▷ ys ≡ [] →
  ys ≡ []
[]≡▷▷₂ eq = proj₂ ([]≡▷▷ eq)

complete : ∀ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → (ϕ₁` ϕ₂` : µ₁ –[ 𝕂 ]→` µ₂ )
  → ⟦ ϕ₁` ⟧ ~ ⟦ ϕ₂` ⟧
  → norm ϕ₁` ≈ norm ϕ₂`
complete {µ₁ = []}     (emb ϕ₁) (emb ϕ₂) ϕ₁~ϕ₂ = ≈-[]*
complete {µ₁ = µ₁ ▷ m} (emb ϕ₁) (emb ϕ₂) ϕ₁~ϕ₂ = ≈-emb (~-cong-wk* ϕ₁~ϕ₂)
complete (emb ϕ₁)          []ₖ`              ~ = ≈-[]*
complete (emb ϕ₁)          []*`              ~ = ≈-[]*
complete (emb ϕ₁)          (ϕ₂` ,ₖ` x/t₂)    ~ = {!!}
complete (emb ϕ₁)          (wkₖ` m ϕ₂`)      ~ = {!!} -- same as []ₖ
complete (emb ϕ₁)          (wkₖ*` µ x₁ ϕ₂`)  ~ = {!!}
complete []ₖ`              (emb ϕ₂)          ~ = ≈-[]*
complete []ₖ`              []ₖ`              ~ = ≈-[]*
complete []ₖ`              []*`              ~ = ≈-[]*
-- complete []ₖ`              (wkₖ*` µ eq ϕ₂`) ~  rewrite []≡▷▷₁ {ys = µ} (sym eq) = ?
complete []ₖ`              (wkₖ*` µ eq ϕ₂`)  ~ with []≡▷▷ {ys = µ} (sym eq) | eq
... | refl , refl | refl = {!!} -- lemma but should be true because ϕ₂` has [] for µs
complete []*`              (emb ϕ₂)          ~ = ≈-[]*
complete []*`              []ₖ`              ~ = ≈-[]*
complete []*`              []*`              ~ = ≈-[]*
complete []*`              (wkₖ` m ϕ₂`)      ~ = {!!} -- same as []ₖ
complete []*`              (wkₖ*` µ x ϕ₂`)   ~ = {!!} -- same as []ₖ
complete (ϕ₁` ,ₖ` x/t₁)    (emb ϕ₂)          ~ = {!!}
complete (ϕ₁` ,ₖ` x/t₁)    (ϕ₂` ,ₖ` x/t₂)    ~ = ≈-,ₖ (complete ϕ₁` ϕ₂` {!!}) {!!}
complete (ϕ₁` ,ₖ` x/t₁)    (wkₖ` m ϕ₂`)      ~ = {!!}
complete (ϕ₁` ,ₖ` x/t₁)    (wkₖ*` µ x₁ ϕ₂`)  ~ = {!!}
complete (wkₖ` m ϕ₁`)      (emb ϕ₂)          ~ = {!!}
complete (wkₖ` m ϕ₁`)      []*`              ~ = {!!}
complete (wkₖ` m ϕ₁`)      (ϕ₂` ,ₖ` x₁)      ~ = {!!}
complete (wkₖ` m ϕ₁`)      (wkₖ` m₁ ϕ₂`)     ~ = {!!}
complete (wkₖ` m ϕ₁`)      (wkₖ*` µ₁ x₁ ϕ₂`) ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) (emb ϕ₂)          ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) []ₖ`              ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) []*`              ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) (ϕ₂` ,ₖ` x₁)      ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) (wkₖ` m₁ ϕ₂`)     ~ = {!!}
complete (wkₖ*` µ eq₁ ϕ₁`) (wkₖ*` µ₁ x₁ ϕ₂`) ~ = {!!}
