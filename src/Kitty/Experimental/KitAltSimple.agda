open import Kitty.Modes

-- Version of KitAlt with a simpler KitTraversal.⋯-↑ field.

module Kitty.Experimental.KitAltSimple {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List.Relation.Unary.Any using (here; there)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Kitty.Prelude
open import Level using (_⊔_)

open import Kitty.Experimental.Star

open Modes 𝕄
open Terms 𝕋

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Alternative KitTraversal ----------------------------------------------------

open import Kitty.Kit 𝕋
open import Kitty.Homotopy

open Kit {{...}}

_–[_]→*_ : List VarMode → (_ : List Kit) → List VarMode → Set _
µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

infixl  6  _↑**_
_↑**_ : {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
[] ↑** µ' = []
(_∷_ {b = 𝕂} f fs) ↑** µ' = (Kit._↑*_ 𝕂 f µ') ∷ (fs ↑** µ')

↑**-neutral :
  ∀ {𝕂s : List Kit}
  → (fs : µ₁ –[ 𝕂s ]→* µ₂)
  → fs ↑** [] ≡ fs
↑**-neutral []       = refl
↑**-neutral (f ∷ fs) = cong (f ∷_) (↑**-neutral fs)

subst-[] :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) {a₁ a₁'}
  → (eq₁ : a₁ ≡ a₁')
  → [] ≡ subst₂ (Star R []) eq₁ eq₁ []
subst-[] R refl = refl

subst-[]-flip :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) {a₁ a₁'}
  → (eq₁ : a₁ ≡ a₁')
  → [] ≡ subst₂ (λ x y → Star R [] y x) eq₁ eq₁ []
subst-[]-flip R refl = refl

subst-∷ :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) {a₁ a₁' a₂ a₂' a₃ a₃' : A}
    {b} {bs} {r : R b a₁ a₂} {rs : Star R bs a₂ a₃}
  → (eq₁ : a₁ ≡ a₁')
  → (eq₂ : a₂ ≡ a₂')
  → (eq₃ : a₃ ≡ a₃')
  → let sub = subst₂ (Star R (b ∷ bs)) eq₁ eq₃ in
    let sub₁ = subst₂ (R b) eq₁ eq₂ in
    let sub₂ = subst₂ (Star R bs) eq₂ eq₃ in
    sub (r ∷ rs) ≡ sub₁ r ∷ sub₂ rs
subst-∷ R refl refl refl = refl

subst-∷-flipped :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) {a₁ a₁' a₂ a₂' a₃ a₃' : A}
    {b} {bs} {r : R b a₁ a₂} {rs : Star R bs a₂ a₃}
  → (eq₁ : a₁ ≡ a₁')
  → (eq₂ : a₂ ≡ a₂')
  → (eq₃ : a₃ ≡ a₃')
  → let sub = subst₂ (λ x y → Star R (b ∷ bs) y x) eq₃ eq₁ in
    let sub₁ = subst₂ (λ x y → R b y x) eq₂ eq₁ in
    let sub₂ = subst₂ (λ x y → Star R bs y x) eq₃ eq₂ in
    sub (r ∷ rs) ≡ sub₁ r ∷ sub₂ rs
subst-∷-flipped R refl refl refl = refl

open import Kitty.SubstProperties

dist-↑*-▷▷ :
  ∀ {{𝕂 : Kit}} µ' µ''
  → (f : µ₁ –[ 𝕂 ]→ µ₂)
  → let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
    f ↑* µ' ↑* µ'' ≡ sub (f ↑* (µ' ▷▷ µ''))
dist-↑*-▷▷ {µ₁} {µ₂} µ' []        f = refl
dist-↑*-▷▷ {µ₁} {µ₂} {{𝕂}} µ' (µ'' ▷ m) f =
  let sub = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
                               (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
  let sub'' = subst₂ (λ x y → (x ▷ m) –[ 𝕂 ]→ (y ▷ m)) (++-assoc µ'' µ' µ₁)
                                                       (++-assoc µ'' µ' µ₂) in
  let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁)
                                (++-assoc µ'' µ' µ₂) in
  f ↑* µ' ↑* (µ'' ▷ m)         ≡⟨⟩
  f ↑* µ' ↑* µ'' ↑ m           ≡⟨ cong (_↑ m) (dist-↑*-▷▷ µ' µ'' f) ⟩
  sub' (f ↑* (µ' ▷▷ µ'')) ↑ m  ≡⟨ dist-subst₂ (λ ■ → _↑_ ⦃ 𝕂 ⦄ ■ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑* (µ' ▷▷ µ'')) ⟩
  sub'' (f ↑* (µ' ▷▷ µ'') ↑ m) ≡⟨ comm-subst₂ (_▷ m) (_▷ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑* (µ' ▷▷ µ'') ↑ m) ⟩
  sub (f ↑* (µ' ▷▷ µ'') ↑ m)   ≡⟨⟩
  sub (f ↑* (µ' ▷▷ (µ'' ▷ m))) ∎

dist-↑**-▷▷ :
  ∀ {𝕂s : List Kit} µ' µ''
  → (f : µ₁ –[ 𝕂s ]→* µ₂)
  → let sub = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
    f ↑** µ' ↑** µ'' ≡ sub (f ↑** (µ' ▷▷ µ''))
dist-↑**-▷▷ {µ₁} {µ₂} {𝕂s = 𝕂s} µ' []        f =
  f ↑** µ' ↑** []  ≡⟨ ↑**-neutral (f ↑** µ') ⟩
  f ↑** µ'         ≡⟨⟩
  f ↑** (µ' ▷▷ []) ∎
dist-↑**-▷▷ {µ₁} {.µ₁} µ' (µ'' ▷ m) []       = subst-[]-flip (λ 𝕂s µ₂ µ₁ → µ₁ –[ 𝕂s ]→ µ₂) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
dist-↑**-▷▷ {µ₁} {µ₂} {𝕂 ∷ 𝕂s}  µ' (µ'' ▷ m) (_∷_ {x = .µ₂} {y = y} f fs) =
  let sub = subst₂ (_–[ 𝕂 ∷ 𝕂s ]→*_) (++-assoc (µ'' ▷ m) µ' µ₁)
                                     (++-assoc (µ'' ▷ m) µ' µ₂) in
  let sub₁ = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' y))
                                (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
  let sub₂ = subst₂ (_–[ 𝕂s ]→*_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
                                  (cong (_∷_ m) (++-assoc µ'' µ' y)) in
  let instance _ = 𝕂 in
  (f ∷ fs) ↑** µ' ↑** (µ'' ▷ m)                                       ≡⟨⟩
  (f ↑* µ' ↑* µ'' ↑ m) ∷ (fs ↑** µ' ↑** (µ'' ▷ m))                    ≡⟨ cong₂ _∷_ (dist-↑*-▷▷ µ' (µ'' ▷ m) f)
                                                                                   (dist-↑**-▷▷ µ' (µ'' ▷ m) fs) ⟩
  (sub₁ (f ↑* (µ' ▷▷ (µ'' ▷ m)))) ∷ (sub₂ (fs ↑** (µ' ▷▷ (µ'' ▷ m)))) ≡⟨ sym (subst-∷-flipped
                                                                           (λ 𝕂s µ₂ µ₁ → µ₁ –[ 𝕂s ]→ µ₂)
                                                                           (++-assoc (µ'' ▷ m) µ' µ₂)
                                                                           (++-assoc (µ'' ▷ m) µ' y)
                                                                           (++-assoc (µ'' ▷ m) µ' µ₁)) ⟩
  sub ((f ↑* (µ' ▷▷ (µ'' ▷ m))) ∷ (fs ↑** (µ' ▷▷ (µ'' ▷ m))))         ≡⟨⟩
  sub ((f ∷ fs) ↑** (µ' ▷▷ (µ'' ▷ m)))                                ∎

subst-⋯ :
  ∀ {𝕂s : List Kit} {µ₁ µ₂ µ₁' µ₂'}
    (_⋯*_ : ∀ {µ₁} {M} {µ₂} {𝕂s : List Kit} → µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M)
    (f : µ₁ –[ 𝕂s ]→* µ₂) {M} (t : µ₁' ⊢ M)
  → (µ₁≡µ₁' : µ₁ ≡ µ₁')
  → (µ₂≡µ₂' : µ₂ ≡ µ₂')
  → let sub⊢₂⁻¹ = subst (_⊢ _) (sym µ₂≡µ₂') in
    let sub⊢₁⁻¹ = subst (_⊢ M) (sym µ₁≡µ₁') in
    let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) µ₁≡µ₁' µ₂≡µ₂' in
    sub⊢₂⁻¹ (t ⋯* sub→₁₂ f) ≡
    sub⊢₁⁻¹ t ⋯* f
subst-⋯ _ f M refl refl = refl

lemy :
  ∀ {𝕂s : List Kit} {µ₁ µ₂ µ' µ''}
    (_⋯*_ : ∀ {µ₁} {M} {µ₂} {𝕂s : List Kit} → µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M)
    (f : µ₁ –[ 𝕂s ]→* µ₂) m (x : (µ₁ ▷▷ µ' ▷▷ µ'') ∋ m)
  → let sub₁ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
    let sub₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
  ((` x) ⋯* ((f ↑** µ') ↑** µ'')) ≡ sub₂ ((` sub₁ x) ⋯* (f ↑** (µ' ▷▷ µ'')))
lemy {𝕂s = 𝕂s} {µ₁} {µ₂} {µ'} {µ''} _⋯*_ f m x =
  let sub∋₁⁻¹ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
  let sub⊢₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
  let sub⊢₂⁻¹ = subst (_⊢ _) (sym (++-assoc µ'' µ' µ₂)) in
  let sub⊢₁⁻¹ = subst (_⊢ m→M m) (sym (++-assoc µ'' µ' µ₁)) in
  let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
  ((` x) ⋯* (f ↑** µ' ↑** µ''))                         ≡⟨ sym (cancel-subst₂ (_⊢ _) (++-assoc µ'' µ' µ₂) _) ⟩
  sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* (f ↑** µ' ↑** µ'')))         ≡⟨ cong (λ ■ → sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* ■))) (dist-↑**-▷▷ µ' µ'' f) ⟩
  sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* sub→₁₂ (f ↑** (µ' ▷▷ µ'')))) ≡⟨ cong sub⊢₂ (subst-⋯ _⋯*_ (f ↑** (µ' ▷▷ µ'')) (` x)
                                                                                    (++-assoc µ'' µ' µ₁)
                                                                                    (++-assoc µ'' µ' µ₂)) ⟩
  sub⊢₂ ((sub⊢₁⁻¹ (` x)) ⋯* (f ↑** (µ' ▷▷ µ'')))        ≡⟨ cong sub⊢₂ (cong (_⋯* (f ↑** (µ' ▷▷ µ'')))
                                                          (sym (dist-subst {F = (_∋ _)} {G = (_⊢ _)} `_
                                                            (sym (++-assoc µ'' µ' µ₁)) x))) ⟩
  sub⊢₂ ((` sub∋₁⁻¹ x) ⋯* (f ↑** (µ' ▷▷ µ'')))          ∎

helper :
  ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂}
    (_⋯*_ : ∀ {µ₁} {M} {µ₂} {𝕂s : List Kit} → µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M)
    (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
  → (∀ {µ₁'} m (x : (µ₁ ▷▷ µ₁') ∋ m)
      → ((` x) ⋯* (f ↑** µ₁')) ≡ ((` x) ⋯* (g ↑** µ₁')))
  → (∀ {µ₁'} {µ₁''} m (x : (µ₁ ▷▷ µ₁' ▷▷ µ₁'') ∋ m)
      → ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡ ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')))
helper {𝕂s₁} {𝕂s₂} {µ₁ = µ₁} {µ₂ = µ₂} _⋯*_ f g f~g {µ₁' = µ₁'} {µ₁'' = µ₁''} m x =
  let sub₁ = subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) in
  let sub₂ = subst (_⊢ _) (++-assoc µ₁'' µ₁' µ₂) in
  ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡⟨ lemy _⋯*_ f _ x ⟩
  sub₂ ((` sub₁ x) ⋯* (f ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ cong sub₂ (f~g {µ₁' ▷▷ µ₁''} _ (subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) x) ) ⟩
  sub₂ ((` sub₁ x) ⋯* (g ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ sym (lemy _⋯*_ g _ x)  ⟩
  ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')) ∎

instance
  kit-[] : List Kit
  kit-[] = []

  kit-∷ : {{𝕂 : Kit}} → {{𝕂s : List Kit}} → List Kit
  kit-∷ {{𝕂}} {{𝕂s}} = 𝕂 ∷ 𝕂s

record KitTraversalAlt : Set₁ where
  constructor mkKitTraversalAlt
  infixl  5  _⋯_  _⋯*_

  field
    _⋯_   : ∀ {{𝕂 : Kit}} →
            µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M

  _⋯*_ : ∀ {𝕂s : List Kit} →
          µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

  field
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id _ (f _ x)
    ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
          (∀ m (x : µ₁ ∋ m) → ` x ⋯* f ≡ ` x ⋯* g) →
          (t : µ₁ ⊢ M) → t ⋯* f ≡ t ⋯* g

-- Deriving KitTraversal, KitAssoc, and KitAssocLemmas -------------------------

module Derive (KT : KitTraversalAlt) where
  open KitTraversalAlt KT public

  private
    kit-traversal : KitTraversal
    kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

  open KitTraversal kit-traversal hiding (_⋯_; ⋯-var; kitᵣ; kitₛ) public

  ~-cong-⋯ :
    ∀ {{𝕂 : Kit}} {f g : µ₁ –[ 𝕂 ]→ µ₂}  (v : µ₁ ⊢ M)
    → f ~ g
    → v ⋯ f ≡ v ⋯ g
  ~-cong-⋯ {f = f} {g} v f~g =
    ⋯-↑ (f ∷ [])
        (g ∷ [])
        (λ m x →
          begin
            (` x) ⋯ f
          ≡⟨ ⋯-var x f ⟩
            `/id _ (f _ x)
          ≡⟨ cong (`/id _) (f~g _ x) ⟩
            `/id _ (g _ x)
          ≡⟨ sym (⋯-var x g) ⟩
            (` x) ⋯ g
          ∎)
        v

  private
    kit-homotopy : KitHomotopy kit-traversal
    kit-homotopy = record { ~-cong-⋯ = ~-cong-⋯ }

  open import Kitty.Compose 𝕋 kit-traversal kit-homotopy

  open ComposeKit {{...}} public

  private
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ f ⋯ g ≡ v ⋯ (g ∘ₖ f)
    ⋯-assoc {{𝕂₁}} {{𝕂₂}} {{𝕂}} v f g =
      v ⋯ f ⋯ g                            ≡⟨ refl ⟩
      v ⋯* (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
        ≡⟨ ⋯-↑ (g ∷[ 𝕂₁ ] f ∷[ 𝕂₂ ] [])
              ((g ∘ₖ f) ∷[ 𝕂 ] [])
              (λ m₁ x →
                ` x ⋯ f ⋯ g               ≡⟨ cong (_⋯ g) (⋯-var x f) ⟩
                (`/id _ (f _ x)) ⋯ g      ≡⟨ tm-⋯-∘ f g x ⟩
                `/id _ ((g ∘ₖ f) _ x)     ≡⟨ cong (λ h → `/id _ h) (sym (dist-↑*-∘ [] g f _ x)) ⟩
                `/id _ ((g ∘ₖ f) _ x)     ≡⟨ sym (⋯-var x (g ∘ₖ f)) ⟩
                ` x ⋯ (g ∘ₖ f)            ∎)
              v
        ⟩
      v ⋯* (_∷_ {b = 𝕂} (g ∘ₖ f) [])       ≡⟨ refl ⟩
      v ⋯ (g ∘ₖ f)       ∎

    kit-assoc : KitAssoc
    kit-assoc = record { ⋯-assoc = ⋯-assoc }

  open KitAssoc kit-assoc public hiding (kitᵣᵣ; kitᵣₛ; kitₛᵣ; kitₛₛ; wk-kitᵣ; wk-kitₛ)

  private
    ⋯-id' : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v
    ⋯-id' {{𝕂}} {µ} {M} v =
      ⋯-↑ (idₖ ∷[ 𝕂 ] [])
          []
          (λ m x →
            ` x ⋯ idₖ {{𝕂}}           ≡⟨ ⋯-var x idₖ ⟩
            `/id _ ((idₖ {{𝕂}}) _ x)  ≡⟨ cong (λ h → `/id _ h) (id↑*~id [] _ _ x) ⟩
            `/id _ (idₖ {{𝕂}} _ x)    ≡⟨⟩
            `/id _ (id/` _ x)         ≡⟨ id/`/id x ⟩
            ` x                       ∎)
          v

    kitassoc-lemmas : KitAssocLemmas
    kitassoc-lemmas = record { ⋯-id = ⋯-id' }

  open KitAssocLemmas kitassoc-lemmas public

  instance
    kitᵣ  = KitTraversal.kitᵣ kit-traversal
    kitₛ  = KitTraversal.kitₛ kit-traversal
    kitᵣᵣ = KitAssoc.kitᵣᵣ kit-assoc
    kitₛᵣ = KitAssoc.kitₛᵣ kit-assoc
    kitᵣₛ = KitAssoc.kitᵣₛ kit-assoc
    kitₛₛ = KitAssoc.kitₛₛ kit-assoc
    wk-kitᵣ = KitAssoc.wk-kitᵣ kit-assoc
    wk-kitₛ = KitAssoc.wk-kitₛ kit-assoc

  open Kit {{...}} public
  open import Kitty.Kit 𝕋 public


