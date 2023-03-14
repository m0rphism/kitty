open import Kitty.Term.Modes

module Kitty.Term.MultiSub {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Level using (_⊔_)

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

_–[_]→*_ : ∀ ⦃ 𝕊 : Sub ⦄ → List VarMode → (_ : List Kit) → List VarMode → Set _
µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

infix   4  _~*_
data _~*_ ⦃ 𝕊 : Sub ⦄ {µ₁} : ∀ {𝕂s} {µ₂} (ϕs₁ ϕs₂ : µ₁ –[ 𝕂s ]→* µ₂) → Set where
  ~*-[] : [] ~* []
  ~*-∷  : ∀ {𝕂 𝕂s} {ϕ₁ ϕ₂ : µ₂ –[ 𝕂 ]→ µ₃} {ϕs₁ ϕs₂ : µ₁ –[ 𝕂s ]→* µ₂}
    → let instance _ = 𝕂 in
      ϕ₁ ~ ϕ₂
    → ϕs₁ ~* ϕs₂
    → (ϕ₁ ∷ ϕs₁) ~* (ϕ₂ ∷ ϕs₂)

infixl  11  _↑*'_
_↑*'_ : ∀ ⦃ 𝕊 : Sub ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} → µ₁ –[ 𝕂 ]→ µ₂ → ∀ µ' → (µ₁ ▷▷ µ') –[ 𝕂 ]→ (µ₂ ▷▷ µ')
f ↑*' []      = f
f ↑*' (µ ▷ m) = f ↑*' µ ↑ m

~-cong-↑*'' : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} {ϕ' : µ₁ –[ 𝕂 ]→ µ₂} →
  ϕ ~ ϕ' →
  (ϕ ↑*' µ) ~ (ϕ' ↑*' µ)
~-cong-↑*'' {µ = []}    ϕ~ϕ' = ϕ~ϕ'
~-cong-↑*'' {µ = µ ▷ m} ϕ~ϕ' = ~-cong-↑' (~-cong-↑*'' ϕ~ϕ')

-- open import Data.List.Relation.Unary.Any using (here; there)
-- ~-cong-↑'x : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {m} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
--   ϕ ~ ϕ' →
--   (ϕ ↑ m) ~ (ϕ' ↑ m)
-- ~-cong-↑'x ⦃ 𝕊 ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x@(here refl) =
--   `/id ⦃ 𝕂₁ ⦄ (x & (ϕ  ↑ m))              ≡⟨ cong `/id (&-↑-here ϕ) ⟩
--   `/id ⦃ 𝕂₁ ⦄ (id/` (here refl))          ≡⟨ id/`/id (here refl) ⟩
--   ` here refl                             ≡⟨ sym (id/`/id (here refl)) ⟩
--   `/id ⦃ 𝕂₂ ⦄ (id/` (here refl))          ≡⟨ sym (cong `/id (&-↑-here ϕ')) ⟩
--   `/id ⦃ 𝕂₂ ⦄ (x & (ϕ' ↑ m))              ∎
-- ~-cong-↑'x ⦃ 𝕊 ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ {µ₁} {µ₂} {m} {ϕ} {ϕ'} ϕ~ϕ' mx x@(there y) =
--   `/id ⦃ 𝕂₁ ⦄ (x & (ϕ  ↑ m))              ≡⟨ cong `/id (&-↑-there ϕ y) ⟩
--   `/id ⦃ 𝕂₁ ⦄ (wk m (y & ϕ))              ≡⟨ {!cong (λ ■ → `/id (wk m ■))!} ⟩
--   `/id ⦃ 𝕂₂ ⦄ (wk m (y & ϕ'))             ≡⟨ sym (cong `/id (&-↑-there ϕ' y)) ⟩
--   `/id ⦃ 𝕂₂ ⦄ (x & (ϕ' ↑ m))              ∎



-- ~-cong-↑*'' : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂₁ 𝕂₂ : Kit ⦄ {µ₁} {µ₂} {µ} {ϕ : µ₁ –[ 𝕂₁ ]→ µ₂} {ϕ' : µ₁ –[ 𝕂₂ ]→ µ₂} →
--   ϕ ~ ϕ' →
--   (ϕ ↑*' µ) ~ (ϕ' ↑*' µ)
-- ~-cong-↑*'' {µ = []}    ϕ~ϕ' = ϕ~ϕ'
-- ~-cong-↑*'' {µ = µ ▷ m} ϕ~ϕ' = ~-cong-↑' (~-cong-↑*'' ϕ~ϕ')

↑*'~↑* : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {ϕ : µ₁ –[ 𝕂 ]→ µ₂} µ → ϕ ↑*' µ ~ ϕ ↑* µ
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ} [] mx x =
  `/id (x & ϕ ↑*' []) ≡⟨⟩
  `/id (x & ϕ)        ≡⟨ sym (↑*-[] ϕ _ x) ⟩
  `/id (x & ϕ ↑*  [])  ∎
↑*'~↑* ⦃ 𝕊 ⦄ ⦃ 𝕂 ⦄ {µ₁} {µ₂} {ϕ} (µ ▷ m) mx x =
  `/id (x & ϕ ↑*' (µ ▷ m))  ≡⟨⟩
  `/id (x & ϕ ↑*' µ ↑ m)    ≡⟨ ~-cong-↑' (↑*'~↑* µ) _ x ⟩
  `/id (x & ϕ ↑*  µ ↑ m)    ≡⟨ sym (↑*-▷ µ m ϕ _ x) ⟩
  `/id (x & ϕ ↑*  (µ ▷ m))  ∎

infixl  11  _↑**_
_↑**_ : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
[] ↑** µ' = []
(_∷_ {b = 𝕂} f fs) ↑** µ' = (_↑*'_ ⦃ 𝕂 = 𝕂 ⦄ f µ') ∷ (fs ↑** µ')

-- infixl  11  _↑**_
-- _↑**_ : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
-- [] ↑** µ' = []
-- (_∷_ {b = 𝕂} f fs) ↑** µ' = (_↑*_ ⦃ 𝕂 = 𝕂 ⦄ f µ') ∷ (fs ↑** µ')

-- -- See ↑**-[]
-- ↑**-neutral :
--   ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s : List Kit}
--   → (fs : µ₁ –[ 𝕂s ]→* µ₂)
--   → fs ↑** [] ~* fs
-- ↑**-neutral {𝕂s = []}     []       = ~*-[]
-- ↑**-neutral {𝕂s = 𝕂 ∷ 𝕂s} (f ∷ fs) = ~*-∷ (↑*-[] f) (↑**-neutral fs) where instance _ = 𝕂

-- dist-↑*-▷▷ :
--   ∀ {{𝕂 : Kit}} µ' µ''
--   → (f : µ₁ –[ 𝕂 ]→ µ₂)
--   → let sub = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
--     f ↑* µ' ↑* µ'' ≡ sub (f ↑* (µ' ▷▷ µ''))
-- dist-↑*-▷▷ {µ₁} {µ₂} µ' []        f = refl
-- dist-↑*-▷▷ {µ₁} {µ₂} {{𝕂}} µ' (µ'' ▷ m) f =
--   let sub = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
--                                (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
--   let sub'' = subst₂ (λ x y → (x ▷ m) –[ 𝕂 ]→ (y ▷ m)) (++-assoc µ'' µ' µ₁)
--                                                        (++-assoc µ'' µ' µ₂) in
--   let sub' = subst₂ (_–[ 𝕂 ]→_) (++-assoc µ'' µ' µ₁)
--                                 (++-assoc µ'' µ' µ₂) in
--   f ↑* µ' ↑* (µ'' ▷ m)         ≡⟨⟩
--   f ↑* µ' ↑* µ'' ↑ m           ≡⟨ cong (_↑ m) (dist-↑*-▷▷ µ' µ'' f) ⟩
--   sub' (f ↑* (µ' ▷▷ µ'')) ↑ m  ≡⟨ dist-subst₂ (λ ■ → _↑_ ⦃ 𝕂 ⦄ ■ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑* (µ' ▷▷ µ'')) ⟩
--   sub'' (f ↑* (µ' ▷▷ µ'') ↑ m) ≡⟨ comm-subst₂ (_▷ m) (_▷ m) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) (f ↑* (µ' ▷▷ µ'') ↑ m) ⟩
--   sub (f ↑* (µ' ▷▷ µ'') ↑ m)   ≡⟨⟩
--   sub (f ↑* (µ' ▷▷ (µ'' ▷ m))) ∎

-- dist-↑**-▷▷ :
--   ∀ {𝕂s : List Kit} µ' µ''
--   → (f : µ₁ –[ 𝕂s ]→* µ₂)
--   → let sub = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
--     f ↑** µ' ↑** µ'' ≡ sub (f ↑** (µ' ▷▷ µ''))
-- dist-↑**-▷▷ {µ₁} {µ₂} {𝕂s = 𝕂s} µ' []        f =
--   f ↑** µ' ↑** []  ≡⟨ ↑**-neutral (f ↑** µ') ⟩
--   f ↑** µ'         ≡⟨⟩
--   f ↑** (µ' ▷▷ []) ∎
-- dist-↑**-▷▷ {µ₁} {.µ₁} µ' (µ'' ▷ m) []       = subst-[]-flip (λ 𝕂s µ₂ µ₁ → µ₁ –[ 𝕂s ]→ µ₂) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
-- dist-↑**-▷▷ {µ₁} {µ₂} {𝕂 ∷ 𝕂s}  µ' (µ'' ▷ m) (_∷_ {x = .µ₂} {y = y} f fs) =
--   let sub = subst₂ (_–[ 𝕂 ∷ 𝕂s ]→*_) (++-assoc (µ'' ▷ m) µ' µ₁)
--                                      (++-assoc (µ'' ▷ m) µ' µ₂) in
--   let sub₁ = subst₂ (_–[ 𝕂 ]→_) (cong (_∷_ m) (++-assoc µ'' µ' y))
--                                 (cong (_∷_ m) (++-assoc µ'' µ' µ₂)) in
--   let sub₂ = subst₂ (_–[ 𝕂s ]→*_) (cong (_∷_ m) (++-assoc µ'' µ' µ₁))
--                                   (cong (_∷_ m) (++-assoc µ'' µ' y)) in
--   let instance _ = 𝕂 in
--   (f ∷ fs) ↑** µ' ↑** (µ'' ▷ m)                                       ≡⟨⟩
--   (f ↑* µ' ↑* µ'' ↑ m) ∷ (fs ↑** µ' ↑** (µ'' ▷ m))                    ≡⟨ cong₂ _∷_ (dist-↑*-▷▷ µ' (µ'' ▷ m) f)
--                                                                                    (dist-↑**-▷▷ µ' (µ'' ▷ m) fs) ⟩
--   (sub₁ (f ↑* (µ' ▷▷ (µ'' ▷ m)))) ∷ (sub₂ (fs ↑** (µ' ▷▷ (µ'' ▷ m)))) ≡⟨ sym (subst-∷-flipped
--                                                                            (λ 𝕂s µ₂ µ₁ → µ₁ –[ 𝕂s ]→ µ₂)
--                                                                            (++-assoc (µ'' ▷ m) µ' µ₂)
--                                                                            (++-assoc (µ'' ▷ m) µ' y)
--                                                                            (++-assoc (µ'' ▷ m) µ' µ₁)) ⟩
--   sub ((f ↑* (µ' ▷▷ (µ'' ▷ m))) ∷ (fs ↑** (µ' ▷▷ (µ'' ▷ m))))         ≡⟨⟩
--   sub ((f ∷ fs) ↑** (µ' ▷▷ (µ'' ▷ m)))                                ∎

module TraversalOps (_⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ; 𝕊 ]→ µ₂ → µ₂ ⊢ M) where
  infixl  8 _⋯*_
  _⋯*_ : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s : List Kit} {µ₁ µ₂ M} →
        µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
  t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

  _≈ₓ_ : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
  _≈ₓ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁')

  _≈ₜ_ : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
  _≈ₜ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {M} (t : (µ₁ ▷▷ µ₁') ⊢ M) → t ⋯* (f ↑** µ₁') ≡ t ⋯* (g ↑** µ₁')

  subst-⋯ :
    ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s : List Kit} {µ₁ µ₂ µ₁' µ₂'}
      (f : µ₁ –[ 𝕂s ]→* µ₂) {M} (t : µ₁' ⊢ M)
    → (µ₁≡µ₁' : µ₁ ≡ µ₁')
    → (µ₂≡µ₂' : µ₂ ≡ µ₂')
    → let sub⊢₂⁻¹ = subst (_⊢ _) (sym µ₂≡µ₂') in
      let sub⊢₁⁻¹ = subst (_⊢ M) (sym µ₁≡µ₁') in
      let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) µ₁≡µ₁' µ₂≡µ₂' in
      sub⊢₂⁻¹ (t ⋯* sub→₁₂ f) ≡
      sub⊢₁⁻¹ t ⋯* f
  subst-⋯ f M refl refl = refl

  -- ↑**-[]' : ∀ ⦃ 𝕊 : Sub ⦄ {𝕂s : List Kit} {µ₁} {µ₂} (fs : µ₁ –[ 𝕂s ]→* µ₂) {m} (x : µ₁ ∋ m)
  --       → (` x) ⋯* fs ↑** [] ≡ (` x) ⋯* fs
  -- ↑**-[]' = Star-indʳ
  --   {P = λ {𝕂s} {µ₂} {µ₁} fs → ∀ {m} (x : µ₁ ∋ m) → (` x) ⋯* fs ↑** [] ≡ (` x) ⋯* fs}
  --   (λ { [] x → refl })
  --   λ {𝕂s} {𝕂} fs f IH x → let instance _ = 𝕂 in
  --     (` x) ⋯* (fs ∷ʳ f) ↑** []           ≡⟨ {!!} ⟩
  --     (` x) ⋯* ((fs ↑** []) ∷ʳ (f ↑* [])) ≡⟨ sym (fold-star'-∷ʳ _ (` x) (fs ↑** []) (f ↑* [])) ⟩
  --     (` x) ⋯ (f ↑* []) ⋯* (fs ↑** [])    ≡⟨ {!!} ⟩
  --     (` x) ⋯ f ⋯* (fs ↑** [])            ≡⟨ {!IH!} ⟩
  --     (` x) ⋯ f ⋯* fs                     ≡⟨ fold-star'-∷ʳ _ (` x) fs f ⟩
  --     (` x) ⋯* (fs ∷ʳ f)                  ∎


--   lemy :
--     ∀ {𝕂s : List Kit} {µ₁ µ₂ µ' µ''}
--       (f : µ₁ –[ 𝕂s ]→* µ₂) m (x : (µ₁ ▷▷ µ' ▷▷ µ'') ∋ m)
--     → let sub₁ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
--       let sub₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
--     ((` x) ⋯* ((f ↑** µ') ↑** µ'')) ≡ sub₂ ((` sub₁ x) ⋯* (f ↑** (µ' ▷▷ µ'')))
--   lemy {𝕂s = 𝕂s} {µ₁} {µ₂} {µ'} {µ''} f m x =
--     let sub∋₁⁻¹ = subst (_∋ _) (sym (++-assoc µ'' µ' µ₁)) in
--     let sub⊢₂ = subst (_⊢ _) (++-assoc µ'' µ' µ₂) in
--     let sub⊢₂⁻¹ = subst (_⊢ _) (sym (++-assoc µ'' µ' µ₂)) in
--     let sub⊢₁⁻¹ = subst (_⊢ m→M m) (sym (++-assoc µ'' µ' µ₁)) in
--     let sub→₁₂ = subst₂ (_–[ 𝕂s ]→*_) (++-assoc µ'' µ' µ₁) (++-assoc µ'' µ' µ₂) in
--     ((` x) ⋯* (f ↑** µ' ↑** µ''))                         ≡⟨ sym (cancel-subst₂ (_⊢ _) (++-assoc µ'' µ' µ₂) _) ⟩
--     sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* (f ↑** µ' ↑** µ'')))         ≡⟨ cong (λ ■ → sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* ■))) (dist-↑**-▷▷ µ' µ'' f) ⟩
--     sub⊢₂ (sub⊢₂⁻¹ ((` x) ⋯* sub→₁₂ (f ↑** (µ' ▷▷ µ'')))) ≡⟨ cong sub⊢₂ (subst-⋯ (f ↑** (µ' ▷▷ µ'')) (` x)
--                                                                                  (++-assoc µ'' µ' µ₁)
--                                                                                  (++-assoc µ'' µ' µ₂)) ⟩
--     sub⊢₂ ((sub⊢₁⁻¹ (` x)) ⋯* (f ↑** (µ' ▷▷ µ'')))        ≡⟨ cong sub⊢₂ (cong (_⋯* (f ↑** (µ' ▷▷ µ'')))
--                                                             (sym (dist-subst {F = (_∋ _)} {G = (_⊢ _)} `_
--                                                               (sym (++-assoc µ'' µ' µ₁)) x))) ⟩
--     sub⊢₂ ((` sub∋₁⁻¹ x) ⋯* (f ↑** (µ' ▷▷ µ'')))          ∎

--   ≈↑** :
--     ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂}
--       (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
--     → (∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m)
--         → ((` x) ⋯* (f ↑** µ₁')) ≡ ((` x) ⋯* (g ↑** µ₁')))
--     → (∀ {µ₁'} {µ₁''} {m} (x : (µ₁ ▷▷ µ₁' ▷▷ µ₁'') ∋ m)
--         → ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡ ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')))
--   ≈↑** {𝕂s₁} {𝕂s₂} {µ₁ = µ₁} {µ₂ = µ₂} f g f~g {µ₁' = µ₁'} {µ₁'' = µ₁''} x =
--     let sub₁ = subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) in
--     let sub₂ = subst (_⊢ _) (++-assoc µ₁'' µ₁' µ₂) in
--     ((` x) ⋯* ((f ↑** µ₁') ↑** µ₁'')) ≡⟨ lemy f _ x ⟩
--     sub₂ ((` sub₁ x) ⋯* (f ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ cong sub₂ (f~g {µ₁' ▷▷ µ₁''} (subst (_∋ _) (sym (++-assoc µ₁'' µ₁' µ₁)) x) ) ⟩
--     sub₂ ((` sub₁ x) ⋯* (g ↑** (µ₁' ▷▷ µ₁''))) ≡⟨ sym (lemy g _ x)  ⟩
--     ((` x) ⋯* ((g ↑** µ₁') ↑** µ₁'')) ∎

open import Data.Unit using (⊤; tt)
module TraversalOps' (_⋯_ : ⊤ → ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ; 𝕊 ]→ µ₂ → µ₂ ⊢ M) where
  open TraversalOps (_⋯_ tt) public

instance
  kit-[] : List Kit
  kit-[] = []

  kit-∷ : {{𝕂 : Kit}} → {{𝕂s : List Kit}} → List Kit
  kit-∷ {{𝕂}} {{𝕂s}} = 𝕂 ∷ 𝕂s
