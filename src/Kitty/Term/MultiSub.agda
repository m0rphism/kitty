open import Kitty.Term.Modes

module Kitty.Term.MultiSub {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Level using (_⊔_; 0ℓ; Level) renaming (suc to lsuc)

open import Kitty.Term.Prelude
open import Kitty.Util.Star
open import Kitty.Term.Kit 𝕋
open import Kitty.Util.SubstProperties

open Modes 𝕄
open Terms 𝕋
open import Kitty.Term.Sub 𝕋
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄
open Kit ⦃ … ⦄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode
    ℓ                         : Level 

open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)

KitPkg : Set₁
KitPkg = Σ[ M ∈ Set ] Σ[ _∋/⊢_ ∈ Scoped M ] (Kit _∋/⊢_)

_–[_]→*_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ → List VarMode → (_ : List KitPkg) → List VarMode → Set (ℓ ⊔ lsuc 0ℓ)
µ₁ –[ 𝕂s ]→* µ₂ = Star (λ (_ , _ , 𝕂) x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

infixl  11  _↑*'_
_↑*'_ :
  ∀ ⦃ 𝕊 : Sub ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {µ₁} {µ₂} →
  µ₁ –[ 𝕂 ]→ µ₂ →
  ∀ µ' →
  (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
f ↑*' []      = f
f ↑*' (µ ▷ m) = f ↑*' µ ↑ m

~-cong-↑*'' :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
    {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑*' µ) ~ (ϕ' ↑*' µ)
~-cong-↑*'' {µ = []}    ϕ~ϕ' = ϕ~ϕ'
~-cong-↑*'' {µ = µ ▷ m} ϕ~ϕ' = ~-cong-↑' (~-cong-↑*'' ϕ~ϕ')

↑*'~↑* :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
    {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} µ →
  ϕ ↑*' µ ~ ϕ ↑* µ
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ} [] = mk-~ λ mx x →
  `/id (x & ϕ ↑*' []) ≡⟨⟩
  `/id (x & ϕ)        ≡⟨ sym (use-~ (↑*-[] ϕ) _ x) ⟩
  `/id (x & ϕ ↑*  [])  ∎
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ} (µ ▷ m) = mk-~ λ mx x →
  `/id (x & ϕ ↑*' (µ ▷ m))  ≡⟨⟩
  `/id (x & ϕ ↑*' µ ↑ m)    ≡⟨ use-~ (~-cong-↑' (↑*'~↑* µ)) _ x ⟩
  `/id (x & ϕ ↑*  µ ↑ m)    ≡⟨ sym (use-~ (↑*-▷ µ m ϕ) _ x) ⟩
  `/id (x & ϕ ↑*  (µ ▷ m))  ∎

infixl  11  _↑**_
_↑**_ :
  ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} →
  µ₁ –[ 𝕂s ]→* µ₂ →
  ∀ µ' →
  (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
[] ↑** µ' = []
(_∷_ {b = _ , _ , 𝕂} f fs) ↑** µ' = (_↑*'_ ⦃ 𝕂 = 𝕂 ⦄ f µ') ∷ (fs ↑** µ')

↑**-[] :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂)
  → fs ↑** [] ≡ fs
↑**-[] [] = refl
↑**-[] (f ∷ fs) = cong (f ∷_) (↑**-[] fs)

dist-↑*'-▷▷ :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ µ' µ''
  → (f : µ₁ –[ 𝕂 ]→ µ₂)
  → let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
    f ↑*' µ' ↑*' µ'' ≡ sub (f ↑*' (µ' ▷▷ µ''))
dist-↑*'-▷▷ {ℓ} {µ₁} {µ₂} µ' []        f = refl
dist-↑*'-▷▷ {ℓ} {µ₁} {µ₂} ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ µ' (µ'' ▷ m) f =
  let sub = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
                               (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
  let sub'' = subst₂ (λ x y → (x ▷ m) –[ 𝕂 ]→ (y ▷ m)) (++-assoc µ'' µ' µ₁)
                                                       (++-assoc µ'' µ' µ₂) in
  let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁)
                                (++-assoc µ'' µ' µ₂) in
  f ↑*' µ' ↑*' (µ'' ▷ m)         ≡⟨⟩
  f ↑*' µ' ↑*' µ'' ↑ m           ≡⟨ cong (_↑ m) (dist-↑*'-▷▷ µ' µ'' f) ⟩
  sub' (f ↑*' (µ' ▷▷ µ'')) ↑ m  ≡⟨ dist-subst₂ (λ ■ → _↑_ ⦃ SubWithLaws-Sub ⦃ 𝕊 ⦄ ⦄ ⦃ 𝕂 ⦄ ■ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑*' (µ' ▷▷ µ'')) ⟩
  sub'' (f ↑*' (µ' ▷▷ µ'') ↑ m) ≡⟨ comm-subst₂ (_▷ m) (_▷ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑*' (µ' ▷▷ µ'') ↑ m) ⟩
  sub (f ↑*' (µ' ▷▷ µ'') ↑ m)   ≡⟨⟩
  sub (f ↑*' (µ' ▷▷ (µ'' ▷ m))) ∎

dist-↑**-▷▷ :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} µ' µ''
  → (f : µ₁ –[ 𝕂s ]→* µ₂)
  → let sub = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
    f ↑** µ' ↑** µ'' ≡ sub (f ↑** (µ' ▷▷ µ''))
dist-↑**-▷▷ {µ₁} {µ₂} {𝕂s = 𝕂s} µ' []        f =
  f ↑** µ' ↑** []  ≡⟨ ↑**-[] (f ↑** µ') ⟩
  f ↑** µ'         ≡⟨⟩
  f ↑** (µ' ▷▷ []) ∎
dist-↑**-▷▷ {ℓ} {µ₁} {.µ₁} µ' (µ'' ▷ m) []       = subst-[]-flip (λ (_ , _ , 𝕂s) µ₂ µ₁ → µ₁ –[ 𝕂s ]→ µ₂) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
dist-↑**-▷▷ {ℓ} {µ₁} {µ₂} {𝕂p@(_ , _ , 𝕂) ∷ 𝕂s}  µ' (µ'' ▷ m) (_∷_ {a₁ = .µ₂} {a₂ = y} f fs) =
  let sub = subst₂ (_–[ 𝕂p ∷ 𝕂s ]→*_) (++-assoc (µ'' ▷ m) µ' µ₁)
                                     (++-assoc (µ'' ▷ m) µ' µ₂) in
  let sub₁ = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' y))
                                (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
  let sub₂ = subst₂ (_–[ 𝕂s ]→*_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
                                  (cong (_∷_ m) (++-assoc µ'' µ' y)) in
  let instance _ = 𝕂 in
  (f ∷ fs) ↑** µ' ↑** (µ'' ▷ m)                                       ≡⟨⟩
  (f ↑*' µ' ↑*' µ'' ↑ m) ∷ (fs ↑** µ' ↑** (µ'' ▷ m))                    ≡⟨ cong₂ _∷_ (dist-↑*'-▷▷ µ' (µ'' ▷ m) f)
                                                                                   (dist-↑**-▷▷ µ' (µ'' ▷ m) fs) ⟩
  (sub₁ (f ↑*' (µ' ▷▷ (µ'' ▷ m)))) ∷ (sub₂ (fs ↑** (µ' ▷▷ (µ'' ▷ m)))) ≡⟨ sym (subst-∷-flipped
                                                                           (λ (_ , _ , 𝕂) µ₂ µ₁ → µ₁ –[ 𝕂 ]→ µ₂)
                                                                           (++-assoc (µ'' ▷ m) µ' µ₂)
                                                                           (++-assoc (µ'' ▷ m) µ' y)
                                                                           (++-assoc (µ'' ▷ m) µ' µ₁)) ⟩
  sub ((f ↑*' (µ' ▷▷ (µ'' ▷ m))) ∷ (fs ↑** (µ' ▷▷ (µ'' ▷ m))))         ≡⟨⟩
  sub ((f ∷ fs) ↑** (µ' ▷▷ (µ'' ▷ m)))                                ∎

module TraversalOps (_⋯_ : ∀ {ℓ} {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ 𝕊 : Sub ℓ ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ; 𝕊 ]→ µ₂ → µ₂ ⊢ M) where
  infixl  8 _⋯*_
  _⋯*_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ M} →
        µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ (_ , _ , 𝕂) _ _ t f → _⋯_ ⦃ 𝕂 ⦄ t f) t fs

  _≈ₓ_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
  _≈ₓ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁')

  _≈ₜ_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
  _≈ₜ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {M} (t : (µ₁ ▷▷ µ₁') ⊢ M) → t ⋯* (f ↑** µ₁') ≡ t ⋯* (g ↑** µ₁')

  subst-⋯ :
    ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ µ₁' µ₂'}
      (f : µ₁ –[ 𝕂s ]→* µ₂) {M} (t : µ₁' ⊢ M)
    → (µ₁≡µ₁' : µ₁ ≡ µ₁')
    → (µ₂≡µ₂' : µ₂ ≡ µ₂')
    → let sub⊢₂⁻¹ = subst (_⊢ _) (sym µ₂≡µ₂') in
      let sub⊢₁⁻¹ = subst (_⊢ M) (sym µ₁≡µ₁') in
      let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) µ₁≡µ₁' µ₂≡µ₂' in
      sub⊢₂⁻¹ (t ⋯* sub→₁₂ f) ≡
      sub⊢₁⁻¹ t ⋯* f
  subst-⋯ f M refl refl = refl

  lemy :
    ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {µ₁ µ₂ µ' µ''}
      (f : µ₁ –[ 𝕂s ]→* µ₂) m (x : (µ₁ ▷▷ µ' ▷▷ µ'') ∋ m)
    → let sub₁ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
      let sub₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
    ((` x) ⋯* ((f ↑** µ') ↑** µ'')) ≡ sub₂ ((` sub₁ x) ⋯* (f ↑** (µ' ▷▷ µ'')))
  lemy {𝕂s = 𝕂s} {µ₁} {µ₂} {µ'} {µ''} f m x =
    let sub∋₁⁻¹ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
    let sub⊢₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
    let sub⊢₂⁻¹ = subst (_⊢ _) (sym (++-assoc µ'' µ' µ₂)) in
    let sub⊢₁⁻¹ = subst (_⊢ m→M m) (sym (++-assoc µ'' µ' µ₁)) in
    let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
    ((` x) ⋯* (f ↑** µ' ↑** µ''))                         ≡⟨ sym (cancel-subst₂ (_⊢ _) (++-assoc µ'' µ' µ₂) _) ⟩
    sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* (f ↑** µ' ↑** µ'')))         ≡⟨ cong (λ ■ → sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* ■))) (dist-↑**-▷▷ µ' µ'' f) ⟩
    sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* sub→₁₂ (f ↑** (µ' ▷▷ µ'')))) ≡⟨ cong sub⊢₂ (subst-⋯ (f ↑** (µ' ▷▷ µ'')) (` x)
                                                                                 (++-assoc µ'' µ' µ₁)
                                                                                 (++-assoc µ'' µ' µ₂)) ⟩
    sub⊢₂ ((sub⊢₁⁻¹ (` x)) ⋯* (f ↑** (µ' ▷▷ µ'')))        ≡⟨ cong sub⊢₂ (cong (_⋯* (f ↑** (µ' ▷▷ µ'')))
                                                            (sym (dist-subst {F = (_∋ _)} {G = (_⊢ _)} `_
                                                              (sym (++-assoc µ'' µ' µ₁)) x))) ⟩
    sub⊢₂ ((` sub∋₁⁻¹ x) ⋯* (f ↑** (µ' ▷▷ µ'')))          ∎

  ≈↑** :
    ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {µ₁ µ₂}
      (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
    → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m)
        → ((` x) ⋯* (f ↑** µ₁')) ≡ ((` x) ⋯* (g ↑** µ₁')))
    → (∀ {µ₁'} {µ₁''} {m} (x : (µ₁ ▷▷ µ₁' ▷▷ µ₁'') ∋ m)
        → ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡ ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')))
  ≈↑** {𝕂s₁} {𝕂s₂} {µ₁ = µ₁} {µ₂ = µ₂} f g f~g {µ₁' = µ₁'} {µ₁'' = µ₁''} x =
    let sub₁ = subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) in
    let sub₂ = subst (_⊢ _) (++-assoc µ₁'' µ₁' µ₂) in
    ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡⟨ lemy f _ x ⟩
    sub₂ ((` sub₁ x) ⋯* (f ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ cong sub₂ (f~g {µ₁' ▷▷ µ₁''} (subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) x) ) ⟩
    sub₂ ((` sub₁ x) ⋯* (g ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ sym (lemy g _ x)  ⟩
    ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')) ∎

open import Data.Unit using (⊤; tt)
module TraversalOps' (_⋯_ : ⊤ → ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ; 𝕊 ]→ µ₂ → µ₂ ⊢ M) where
  open TraversalOps (_⋯_ tt) public

-- TODO: If this worked before it will definitely not work anymore with Agda 2.6.4's instance resolution.
instance
  kit-[] : List KitPkg
  kit-[] = []

  kit-∷ : ∀ {M} {_∋/⊢_ : Scoped M} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ → ⦃ 𝕂s : List KitPkg ⦄ → List KitPkg
  kit-∷ ⦃ 𝕂 ⦄ ⦃ 𝕂s ⦄ = (_ , _ , 𝕂) ∷ 𝕂s
