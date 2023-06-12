open import Kitty.Term.Terms

module Kitty.Term.MultiSub (𝕋 : Terms) where

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

open Terms 𝕋
open import Kitty.Term.Sub 𝕋
open Sub ⦃ … ⦄
open SubWithLaws ⦃ … ⦄
open Kit ⦃ … ⦄

private
  variable
    st                        : SortTy
    s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort st
    S S₁ S₂ S₃ S' S₁' S₂' S₃' : SortCtx
    ℓ                         : Level 

open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)

KitPkg : Set₁
KitPkg = Σ[ _∋/⊢_ ∈ VarScoped ] (Kit _∋/⊢_)

pack-kit : ∀ {_∋/⊢_ : VarScoped} → Kit _∋/⊢_ → KitPkg
pack-kit K = _ ,  K

unpack-kit : (KP : KitPkg) → Kit (proj₁ KP)
unpack-kit (_ , 𝕂) = 𝕂

_–[_]→*_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ → SortCtx → (_ : List KitPkg) → SortCtx → Set (ℓ ⊔ lsuc 0ℓ)
S₁ –[ 𝕂s ]→* S₂ = Star (λ (_ , 𝕂) x y → y –[ 𝕂 ]→ x) 𝕂s S₂ S₁

infixl  11  _↑*'_
_↑*'_ :
  ∀ ⦃ 𝕊 : Sub ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} →
  S₁ –[ 𝕂 ]→ S₂ →
  ∀ S' →
  (S₁ ▷▷ S') –[ 𝕂 ]→ (S₂ ▷▷ S')
f ↑*' []      = f
f ↑*' (S ▷ s) = f ↑*' S ↑ s

~-cong-↑*'' :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
    {S₁} {S₂} {S} {ϕ : S₁ –[ 𝕂 ]→ S₂} {ϕ' : S₁ –[ 𝕂 ]→ S₂} →
  ϕ ~ ϕ' →
  (ϕ ↑*' S) ~ (ϕ' ↑*' S)
~-cong-↑*'' {S = []}    ϕ~ϕ' = ϕ~ϕ'
~-cong-↑*'' {S = S ▷ s} ϕ~ϕ' = ~-cong-↑' (~-cong-↑*'' ϕ~ϕ')

↑*'~↑* :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
    {S₁} {S₂} {ϕ : S₁ –[ 𝕂 ]→ S₂} S →
  ϕ ↑*' S ~ ϕ ↑* S
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {S₁} {S₂} {ϕ} [] = mk-~ λ mx x →
  `/id (x & ϕ ↑*' []) ≡⟨⟩
  `/id (x & ϕ)        ≡⟨ sym (use-~ (↑*-[] ϕ) _ x) ⟩
  `/id (x & ϕ ↑*  [])  ∎
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {S₁} {S₂} {ϕ} (S ▷ s) = mk-~ λ mx x →
  `/id (x & ϕ ↑*' (S ▷ s))  ≡⟨⟩
  `/id (x & ϕ ↑*' S ↑ s)    ≡⟨ use-~ (~-cong-↑' (↑*'~↑* S)) _ x ⟩
  `/id (x & ϕ ↑*  S ↑ s)    ≡⟨ sym (use-~ (↑*-▷ S s ϕ) _ x) ⟩
  `/id (x & ϕ ↑*  (S ▷ s))  ∎

infixl  11  _↑**_
_↑**_ :
  ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} →
  S₁ –[ 𝕂s ]→* S₂ →
  ∀ S' →
  (S' ++ S₁) –[ 𝕂s ]→* (S' ++ S₂)
[] ↑** S' = []
(_∷_ {b = _ , 𝕂} f fs) ↑** S' = (_↑*'_ ⦃ 𝕂 = 𝕂 ⦄ f S') ∷ (fs ↑** S')

↑**-[] :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂} (fs : S₁ –[ 𝕂s ]→* S₂)
  → fs ↑** [] ≡ fs
↑**-[] [] = refl
↑**-[] (f ∷ fs) = cong (f ∷_) (↑**-[] fs)

dist-↑*'-▷▷ :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ S' S''
  → (f : S₁ –[ 𝕂 ]→ S₂)
  → let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc S'' S' S₁) (++-assoc S'' S' S₂) in
    f ↑*' S' ↑*' S'' ≡ sub (f ↑*' (S' ▷▷ S''))
dist-↑*'-▷▷ {ℓ} {S₁} {S₂} S' []        f = refl
dist-↑*'-▷▷ {ℓ} {S₁} {S₂} ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ S' (S'' ▷ s) f =
  let sub = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ s) (++-assoc S'' S' S₁))
                               (cong (_∷_ s) (++-assoc S'' S' S₂)) in
  let sub'' = subst₂ (λ x y → (x ▷ s) –[ 𝕂 ]→ (y ▷ s)) (++-assoc S'' S' S₁)
                                                       (++-assoc S'' S' S₂) in
  let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc S'' S' S₁)
                                (++-assoc S'' S' S₂) in
  f ↑*' S' ↑*' (S'' ▷ s)         ≡⟨⟩
  f ↑*' S' ↑*' S'' ↑ s           ≡⟨ cong (_↑ s) (dist-↑*'-▷▷ S' S'' f) ⟩
  sub' (f ↑*' (S' ▷▷ S'')) ↑ s  ≡⟨ dist-subst₂ (λ ■ → _↑_ ⦃ SubWithLaws-Sub ⦃ 𝕊 ⦄ ⦄ ⦃ 𝕂 ⦄ ■ s) (++-assoc S'' S' S₁) (++-assoc S'' S' S₂) (f ↑*' (S' ▷▷ S'')) ⟩
  sub'' (f ↑*' (S' ▷▷ S'') ↑ s) ≡⟨ comm-subst₂ (_▷ s) (_▷ s) (++-assoc S'' S' S₁) (++-assoc S'' S' S₂) (f ↑*' (S' ▷▷ S'') ↑ s) ⟩
  sub (f ↑*' (S' ▷▷ S'') ↑ s)   ≡⟨⟩
  sub (f ↑*' (S' ▷▷ (S'' ▷ s))) ∎

dist-↑**-▷▷ :
  ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} S' S''
  → (f : S₁ –[ 𝕂s ]→* S₂)
  → let sub = subst₂ (_–[ 𝕂s ]→*_) (++-assoc S'' S' S₁) (++-assoc S'' S' S₂) in
    f ↑** S' ↑** S'' ≡ sub (f ↑** (S' ▷▷ S''))
dist-↑**-▷▷ {S₁} {S₂} {𝕂s = 𝕂s} S' []        f =
  f ↑** S' ↑** []  ≡⟨ ↑**-[] (f ↑** S') ⟩
  f ↑** S'         ≡⟨⟩
  f ↑** (S' ▷▷ []) ∎
dist-↑**-▷▷ {ℓ} {S₁} {.S₁} S' (S'' ▷ s) []       = subst-[]-flip (λ (_ , 𝕂s) S₂ S₁ → S₁ –[ 𝕂s ]→ S₂) (cong (_∷_ s) (++-assoc S'' S' S₁))
dist-↑**-▷▷ {ℓ} {S₁} {S₂} {𝕂p@(_ , 𝕂) ∷ 𝕂s}  S' (S'' ▷ s) (_∷_ {a₁ = .S₂} {a₂ = y} f fs) =
  let sub = subst₂ (_–[ 𝕂p ∷ 𝕂s ]→*_) (++-assoc (S'' ▷ s) S' S₁)
                                     (++-assoc (S'' ▷ s) S' S₂) in
  let sub₁ = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ s) (++-assoc S'' S' y))
                                (cong (_∷_ s) (++-assoc S'' S' S₂)) in
  let sub₂ = subst₂ (_–[ 𝕂s ]→*_) (cong (_∷_ s) (++-assoc S'' S' S₁))
                                  (cong (_∷_ s) (++-assoc S'' S' y)) in
  let instance _ = 𝕂 in
  (f ∷ fs) ↑** S' ↑** (S'' ▷ s)                                       ≡⟨⟩
  (f ↑*' S' ↑*' S'' ↑ s) ∷ (fs ↑** S' ↑** (S'' ▷ s))                    ≡⟨ cong₂ _∷_ (dist-↑*'-▷▷ S' (S'' ▷ s) f)
                                                                                   (dist-↑**-▷▷ S' (S'' ▷ s) fs) ⟩
  (sub₁ (f ↑*' (S' ▷▷ (S'' ▷ s)))) ∷ (sub₂ (fs ↑** (S' ▷▷ (S'' ▷ s)))) ≡⟨ sym (subst-∷-flipped
                                                                           (λ (_ , 𝕂) S₂ S₁ → S₁ –[ 𝕂 ]→ S₂)
                                                                           (++-assoc (S'' ▷ s) S' S₂)
                                                                           (++-assoc (S'' ▷ s) S' y)
                                                                           (++-assoc (S'' ▷ s) S' S₁)) ⟩
  sub ((f ↑*' (S' ▷▷ (S'' ▷ s))) ∷ (fs ↑** (S' ▷▷ (S'' ▷ s))))         ≡⟨⟩
  sub ((f ∷ fs) ↑** (S' ▷▷ (S'' ▷ s)))                                ∎

module TraversalOps (_⋯_ : ∀ {ℓ} {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ ⦃ 𝕊 : Sub ℓ ⦄ {S₁} {S₂} {st} {s : Sort st} → S₁ ⊢ s → S₁ –[ 𝕂 ; 𝕊 ]→ S₂ → S₂ ⊢ s) where
  infixl  8 _⋯*_
  _⋯*_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂} {st} {s : Sort st} →
        S₁ ⊢ s → S₁ –[ 𝕂s ]→* S₂ → S₂ ⊢ s
  t ⋯* fs = fold-star' (λ (_ , 𝕂) _ _ t f → _⋯_ ⦃ 𝕂 ⦄ t f) t fs

  _≈ₓ_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {S₁ S₂} → (f : S₁ –[ 𝕂s₁ ]→* S₂) → (g : S₁ –[ 𝕂s₂ ]→* S₂) → Set
  _≈ₓ_ {S₁ = S₁} f g = ∀ {S₁'} {s} (x : (S₁ ▷▷ S₁') ∋ s) → (` x) ⋯* (f ↑** S₁') ≡ (` x) ⋯* (g ↑** S₁')

  _≈ₜ_ : ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {S₁ S₂} → (f : S₁ –[ 𝕂s₁ ]→* S₂) → (g : S₁ –[ 𝕂s₂ ]→* S₂) → Set
  _≈ₜ_ {S₁ = S₁} f g = ∀ {S₁'} {st} {s : Sort st} (t : (S₁ ▷▷ S₁') ⊢ s) → t ⋯* (f ↑** S₁') ≡ t ⋯* (g ↑** S₁')

  subst-⋯ :
    ∀ ⦃ 𝕊 : Sub ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂ S₁' S₂'} {st} {s : Sort st}
      (f : S₁ –[ 𝕂s ]→* S₂) (t : S₁' ⊢ s)
    → (S₁≡S₁' : S₁ ≡ S₁')
    → (S₂≡S₂' : S₂ ≡ S₂')
    → let sub⊢₂⁻¹ = subst (_⊢ _) (sym S₂≡S₂') in
      let sub⊢₁⁻¹ = subst (_⊢ s) (sym S₁≡S₁') in
      let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) S₁≡S₁' S₂≡S₂' in
      sub⊢₂⁻¹ (t ⋯* sub→₁₂ f) ≡
      sub⊢₁⁻¹ t ⋯* f
  subst-⋯ f s refl refl = refl

  lemy :
    ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s : List KitPkg} {S₁ S₂ S' S''}
      (f : S₁ –[ 𝕂s ]→* S₂) s (x : (S₁ ▷▷ S' ▷▷ S'') ∋ s)
    → let sub₁ = subst (_∋ _) (sym (++-assoc S'' S' S₁)) in
      let sub₂ = subst (_⊢ _) (++-assoc S'' S' S₂) in
    ((` x) ⋯* ((f ↑** S') ↑** S'')) ≡ sub₂ ((` sub₁ x) ⋯* (f ↑** (S' ▷▷ S'')))
  lemy {𝕂s = 𝕂s} {S₁} {S₂} {S'} {S''} f s x =
    let sub∋₁⁻¹ = subst (_∋ _) (sym (++-assoc S'' S' S₁)) in
    let sub⊢₂ = subst (_⊢ _) (++-assoc S'' S' S₂) in
    let sub⊢₂⁻¹ = subst (_⊢ _) (sym (++-assoc S'' S' S₂)) in
    let sub⊢₁⁻¹ = subst (_⊢ s) (sym (++-assoc S'' S' S₁)) in
    let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) (++-assoc S'' S' S₁) (++-assoc S'' S' S₂) in
    ((` x) ⋯* (f ↑** S' ↑** S''))                         ≡⟨ sym (cancel-subst₂ (_⊢ _) (++-assoc S'' S' S₂) _) ⟩
    sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* (f ↑** S' ↑** S'')))         ≡⟨ cong (λ ■ → sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* ■))) (dist-↑**-▷▷ S' S'' f) ⟩
    sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* sub→₁₂ (f ↑** (S' ▷▷ S'')))) ≡⟨ cong sub⊢₂ (subst-⋯ (f ↑** (S' ▷▷ S'')) (` x)
                                                                                 (++-assoc S'' S' S₁)
                                                                                 (++-assoc S'' S' S₂)) ⟩
    sub⊢₂ ((sub⊢₁⁻¹ (` x)) ⋯* (f ↑** (S' ▷▷ S'')))        ≡⟨ cong sub⊢₂ (cong (_⋯* (f ↑** (S' ▷▷ S'')))
                                                            (sym (dist-subst {F = (_∋ _)} {G = (_⊢ _)} `_
                                                              (sym (++-assoc S'' S' S₁)) x))) ⟩
    sub⊢₂ ((` sub∋₁⁻¹ x) ⋯* (f ↑** (S' ▷▷ S'')))          ∎

  ≈↑** :
    ∀ ⦃ 𝕊 : SubWithLaws ℓ ⦄ {𝕂s₁ 𝕂s₂ : List KitPkg} {S₁ S₂}
      (f : S₁ –[ 𝕂s₁ ]→* S₂) (g : S₁ –[ 𝕂s₂ ]→* S₂)
    → (∀ {S₁'} {s} (x : (S₁ ▷▷ S₁') ∋ s)
        → ((` x) ⋯* (f ↑** S₁')) ≡ ((` x) ⋯* (g ↑** S₁')))
    → (∀ {S₁'} {S₁''} {s} (x : (S₁ ▷▷ S₁' ▷▷ S₁'') ∋ s)
        → ((` x) ⋯* ((f ↑** S₁') ↑** S₁'')) ≡ ((` x) ⋯* ((g ↑** S₁') ↑** S₁'')))
  ≈↑** {𝕂s₁} {𝕂s₂} {S₁ = S₁} {S₂ = S₂} f g f~g {S₁' = S₁'} {S₁'' = S₁''} x =
    let sub₁ = subst (_∋ _) (sym (++-assoc S₁'' S₁' S₁)) in
    let sub₂ = subst (_⊢ _) (++-assoc S₁'' S₁' S₂) in
    ((` x) ⋯* ((f ↑** S₁') ↑** S₁'')) ≡⟨ lemy f _ x ⟩
    sub₂ ((` sub₁ x) ⋯* (f ↑** (S₁' ▷▷ S₁''))) ≡⟨ cong sub₂ (f~g {S₁' ▷▷ S₁''} (subst (_∋ _) (sym (++-assoc S₁'' S₁' S₁)) x) ) ⟩
    sub₂ ((` sub₁ x) ⋯* (g ↑** (S₁' ▷▷ S₁''))) ≡⟨ sym (lemy g _ x)  ⟩
    ((` x) ⋯* ((g ↑** S₁') ↑** S₁'')) ∎

open import Data.Unit using (⊤; tt)
module TraversalOps' (_⋯_ : ⊤ → ∀ {ℓ} ⦃ 𝕊 : Sub ℓ ⦄ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ {S₁} {S₂} {st} {s : Sort st} → S₁ ⊢ s → S₁ –[ 𝕂 ; 𝕊 ]→ S₂ → S₂ ⊢ s) where
  open TraversalOps (_⋯_ tt) public

-- TODO: If this worked before it will definitely not work anymore with Agda 2.6.4's instance resolution.
instance
  kit-[] : List KitPkg
  kit-[] = []

  kit-∷ : ∀ {_∋/⊢_ : VarScoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄ → ⦃ 𝕂s : List KitPkg ⦄ → List KitPkg
  kit-∷ ⦃ 𝕂 ⦄ ⦃ 𝕂s ⦄ = (_ , 𝕂) ∷ 𝕂s
