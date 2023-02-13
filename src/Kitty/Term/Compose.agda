open import Kitty.Term.Modes
open import Kitty.Term.Kit using (KitTraversal; KitHomotopy)

module Kitty.Term.Compose {𝕄 : Modes} (𝕋 : Terms 𝕄) (T : KitTraversal 𝕋) (H : KitHomotopy 𝕋 T) where

open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open ≡-Reasoning
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id)

open import Kitty.Term.Prelude
open import Kitty.Util.Homotopy
open ~-Reasoning

open Modes 𝕄
open Terms 𝕋
open Kitty.Term.Kit 𝕋
open Kitty.Term.Kit.KitTraversal T
open Kitty.Term.Kit.KitHomotopy H

open Kit {{...}}

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- If the client provides a `KitAssoc` which works for all `ComposeKit`s,
-- they get `⋯-assoc` for `_ᵣ∘ᵣ_`, `_ₛ∘ᵣ_`, `_ᵣ∘ₛ_`, and `_ₛ∘ₛ_`.

record ComposeKit ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄ : Set₁ where
  infixr 9 _∘ₖ_
  infixl 9 _·ₖ_

  field
    _∘ₖ_ : µ₂ –[ 𝕂₁ ]→ µ₃ → µ₁ –[ 𝕂₂ ]→ µ₂ → µ₁ –[ 𝕂 ]→ µ₃

    tm-⋯-∘ : (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
      `/id _ (ϕ₁ _ x) ⋯ ϕ₂ ≡ `/id _ ((ϕ₂ ∘ₖ ϕ₁) _ x)

    dist-↑-∘ : ∀ m (ϕ₁ : µ₂ –[ 𝕂₁ ]→ µ₃) (ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂) →
      (ϕ₁ ∘ₖ ϕ₂) ↑ m ~ (ϕ₁ ↑ m) ∘ₖ (ϕ₂ ↑ m)

    ~-cong-∘₁ : {ϕ₁ ϕ₁' : µ₂ –[ 𝕂₁ ]→ µ₃} (ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂)  →
      ϕ₁ ~ ϕ₁' →
      ϕ₁ ∘ₖ ϕ₂ ~ ϕ₁' ∘ₖ ϕ₂

    ~-cong-∘₂ : (ϕ₁ : µ₂ –[ 𝕂₁ ]→ µ₃) {ϕ₂ ϕ₂' : µ₁ –[ 𝕂₂ ]→ µ₂}  →
      ϕ₂ ~ ϕ₂' →
      ϕ₁ ∘ₖ ϕ₂ ~ ϕ₁ ∘ₖ ϕ₂'

    _⋯'_ : ∀ (t : µ₁ ∋/⊢[ 𝕂₁ ] (id/m→M m)) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) → µ₂ ∋/⊢[ 𝕂 ] (id/m→M m)
    _⋯''_ : ∀ (t : µ₁ ∋/⊢[ 𝕂₂ ] (id/m→M m)) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) → µ₂ ∋/⊢[ 𝕂 ] (id/m→M m)

    ~-cong-⋯'' :
      ∀ ⦃ 𝕂 : Kit ⦄ {f g : µ₁ –[ 𝕂₁ ]→ µ₂} (t : µ₁ ∋/⊢[ 𝕂₂ ] (id/m→M m))
      → f ~ g
      → t ⋯'' f ≡ t ⋯'' g

    tm-⋯''-∘ : (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
      (ϕ₁ _ x) ⋯'' ϕ₂ ≡ (ϕ₂ ∘ₖ ϕ₁) _ x

    𝕂₁→𝕂 : µ ∋/⊢[ 𝕂₁ ] (id/m→M m) → µ ∋/⊢[ 𝕂 ] (id/m→M m)
    𝕂₂→𝕂 : µ ∋/⊢[ 𝕂₂ ] (id/m→M m) → µ ∋/⊢[ 𝕂 ] (id/m→M m)

    𝕂₁→𝕂₁ : (eq : 𝕂₁ ≡ 𝕂) → (x : µ ∋/⊢[ 𝕂₁ ] (id/m→M m)) → 𝕂₁→𝕂 x ≡ subst (_ ∋/⊢[_] _) eq x
    𝕂₂→𝕂₂ : (eq : 𝕂₂ ≡ 𝕂) → (x : µ ∋/⊢[ 𝕂₂ ] (id/m→M m)) → 𝕂₂→𝕂 x ≡ subst (_ ∋/⊢[_] _) eq x

    ⋯''-var : ∀ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) →
      id/` _ x ⋯'' ϕ ≡ 𝕂₁→𝕂 (ϕ _ x)

      -- ComposeKit._⋯''_ C₂₁ t' ϕ                                            ≡⟨ {!!} ⟩
      -- ComposeKit._⋯''_ C (id/` _ (here refl)) ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆ ≡⟨⟩

  _·ₖ_ : µ₁ –[ 𝕂₂ ]→ µ₂ → µ₂ –[ 𝕂₁ ]→ µ₃ → µ₁ –[ 𝕂 ]→ µ₃
  ϕ₁ ·ₖ ϕ₂ = ϕ₂ ∘ₖ ϕ₁

  dist-↑*-∘ : ∀ µ (ϕ₁ : µ₂ –[ 𝕂₁ ]→ µ₃) (ϕ₂ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    (ϕ₁ ∘ₖ ϕ₂) ↑* µ ~ (ϕ₁ ↑* µ) ∘ₖ (ϕ₂ ↑* µ)
  dist-↑*-∘ []      ϕ₁ ϕ₂ = ~-refl
  dist-↑*-∘ (µ ▷ m) ϕ₁ ϕ₂ =
    (ϕ₁ ∘ₖ ϕ₂) ↑* (µ ▷ m)               ~⟨⟩
    ((ϕ₁ ∘ₖ ϕ₂) ↑* µ) ↑ m               ~⟨ ~-cong-↑ (dist-↑*-∘ µ ϕ₁ ϕ₂) ⟩
    ((ϕ₁ ↑* µ) ∘ₖ (ϕ₂ ↑* µ)) ↑ m        ~⟨ dist-↑-∘ m (ϕ₁ ↑* µ) (ϕ₂ ↑* µ) ⟩
    ((ϕ₁ ↑* µ) ↑ m) ∘ₖ ((ϕ₂ ↑* µ) ↑ m)  ~⟨⟩
    (ϕ₁ ↑* (µ ▷ m)) ∘ₖ (ϕ₂ ↑* (µ ▷ m))  ~∎

_∘[_]_ : {𝕂₁ 𝕂₂ 𝕂 : Kit}
       → µ₂ –[ 𝕂₁ ]→ µ₃
       → ComposeKit ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄
       → µ₁ –[ 𝕂₂ ]→ µ₂
       → µ₁ –[ 𝕂 ]→ µ₃
_∘[_]_ {𝕂₁ = 𝕂₁} {𝕂₂} {𝕂} ϕ₁ C ϕ₂ = ComposeKit._∘ₖ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ C ϕ₁ ϕ₂

_·[_]_ : {𝕂₁ 𝕂₂ 𝕂 : Kit}
       → µ₁ –[ 𝕂₂ ]→ µ₂
       → ComposeKit ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄
       → µ₂ –[ 𝕂₁ ]→ µ₃
       → µ₁ –[ 𝕂 ]→ µ₃
_·[_]_ {𝕂₁ = 𝕂₁} {𝕂₂} {𝕂} ϕ₁ C ϕ₂ = ComposeKit._·ₖ_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ C ϕ₁ ϕ₂

_⋯[_]_ : {𝕂₁ 𝕂₂ 𝕂 : Kit}
       → µ₁ ∋/⊢[ 𝕂₂ ] (Kit.id/m→M 𝕂₂ m)
       → ComposeKit ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄
       → µ₁ –[ 𝕂₁ ]→ µ₂
       → µ₂ ∋/⊢[ 𝕂 ] (Kit.id/m→M 𝕂 m)
_⋯[_]_ {𝕂₁ = 𝕂₁} {𝕂₂} {𝕂} x C ϕ = ComposeKit._⋯''_ ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ C x ϕ

record KitAssoc : Set₁ where
  open ComposeKit {{...}}

  field
    ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
                (v : µ₁ ⊢ M) (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) →
      v ⋯ ϕ₁ ⋯ ϕ₂ ≡ v ⋯ (ϕ₂ ∘ₖ ϕ₁)

  ∘~∘→⋯≡⋯ : ∀ {{𝕂₁ 𝕂₂ 𝕂₁' 𝕂₂' 𝕂 : Kit}}
              {{𝔸  : ComposeKit {{𝕂₂ }} {{𝕂₁ }} {{𝕂}} }}
              {{𝔸' : ComposeKit {{𝕂₂'}} {{𝕂₁'}} {{𝕂}} }}
              {ϕ₁  : µ₁ –[ 𝕂₁  ]→ µ₂ } {ϕ₂  : µ₂  –[ 𝕂₂  ]→ µ₃}
              {ϕ₁' : µ₁ –[ 𝕂₁' ]→ µ₂'} {ϕ₂' : µ₂' –[ 𝕂₂' ]→ µ₃} →
    ϕ₂ ∘ₖ ϕ₁ ~ ϕ₂' ∘ₖ ϕ₁' →
    ∀ {M} (t : µ₁ ⊢ M) →
    t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁' ⋯ ϕ₂'
  ∘~∘→⋯≡⋯ {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₁' = ϕ₁'} {ϕ₂' = ϕ₂'} eq t =
    t ⋯ ϕ₁ ⋯ ϕ₂    ≡⟨ ⋯-assoc t ϕ₁ ϕ₂ ⟩
    t ⋯ ϕ₂ ∘ₖ ϕ₁   ≡⟨ ~-cong-⋯ t eq ⟩
    t ⋯ ϕ₂' ∘ₖ ϕ₁' ≡⟨ sym (⋯-assoc t ϕ₁' ϕ₂') ⟩
    t ⋯ ϕ₁' ⋯ ϕ₂'  ∎

  -- Example:
  --
  --   instance kit-assoc : KitAssoc {{traversal}}
  --   KitAssoc.⋯-assoc kit-assoc (` x) f g =
  --     tm' (f _ x) ⋯ g    ≡⟨ tm'-⋯-∘ f g x ⟩
  --     tm' ((g ∘ₖ f) _ x) ∎
  --   KitAssoc.⋯-assoc kit-assoc (λ→ e) f g = cong λ→_
  --     (e ⋯ f ↑ _ ⋯ g ↑ _        ≡⟨ ⋯-assoc e (f ↑ _) (g ↑ _) ⟩
  --      e ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (e ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
  --      e ⋯ (g ∘ₖ f) ↑ _         ∎)
  --   KitAssoc.⋯-assoc kit-assoc (e₁ · e₂) f g = cong₂ _·_ (⋯-assoc e₁ f g) (⋯-assoc e₂ f g)

  private instance _ = kitᵣ
  private instance _ = kitₛ


  ~-cong-ᵣ∘ᵣ₁ : {ϕ₁ ϕ₁' : µ₂ →ᵣ µ₃} (ϕ₂ : µ₁ →ᵣ µ₂)  →
    ϕ₁ ~ ϕ₁' →
    ϕ₁ ᵣ∘ᵣ ϕ₂ ~ ϕ₁' ᵣ∘ᵣ ϕ₂
  ~-cong-ᵣ∘ᵣ₁ {ϕ₁ = ϕ₁} {ϕ₁'} ϕ₂ ϕ₁~ϕ₁' _ x  = ϕ₁~ϕ₁' _ (ϕ₂ _ x)

  ~-cong-ᵣ∘ᵣ₂ : (ϕ₁ : µ₂ →ᵣ µ₃) {ϕ₂ ϕ₂' : µ₁ →ᵣ µ₂}  →
    ϕ₂ ~ ϕ₂' →
    ϕ₁ ᵣ∘ᵣ ϕ₂ ~ ϕ₁ ᵣ∘ᵣ ϕ₂'
  ~-cong-ᵣ∘ᵣ₂ ϕ₁ {ϕ₂} {ϕ₂'} ϕ₂~ϕ₂' _ x  = cong (ϕ₁ _) (ϕ₂~ϕ₂' _ x)

  kitᵣᵣ : ComposeKit {{kitᵣ}} {{kitᵣ}} {{kitᵣ}}
  ComposeKit._∘ₖ_       kitᵣᵣ = _ᵣ∘ᵣ_
  ComposeKit.tm-⋯-∘     kitᵣᵣ = λ ρ₁ ρ₂ x → ⋯-var (ρ₁ _ x) ρ₂ where instance _ = kitᵣ
  ComposeKit.dist-↑-∘   kitᵣᵣ = λ _ ρ₁ ρ₂ → λ where
                                                    _ (here px) → refl
                                                    _ (there x) → refl
  ComposeKit.~-cong-∘₁  kitᵣᵣ = ~-cong-ᵣ∘ᵣ₁
  ComposeKit.~-cong-∘₂  kitᵣᵣ = ~-cong-ᵣ∘ᵣ₂
  ComposeKit._⋯'_       kitᵣᵣ = λ x ρ → ρ _ x
  ComposeKit._⋯''_      kitᵣᵣ = λ x ρ → ρ _ x
  ComposeKit.tm-⋯''-∘   kitᵣᵣ = λ ϕ₁ ϕ₂ x → refl
  ComposeKit.𝕂₁→𝕂      kitᵣᵣ = λ x → x
  ComposeKit.𝕂₂→𝕂      kitᵣᵣ = λ x → x
  ComposeKit.𝕂₁→𝕂₁     kitᵣᵣ = λ { refl x → refl }
  ComposeKit.𝕂₂→𝕂₂     kitᵣᵣ = λ { refl x → refl }
  ComposeKit.⋯''-var    kitᵣᵣ = λ x ϕ → refl
  ComposeKit.~-cong-⋯'' kitᵣᵣ = λ x f~g → f~g _ x


  ~-cong-ₛ∘ᵣ₁ : {ϕ₁ ϕ₁' : µ₂ →ₛ µ₃} (ϕ₂ : µ₁ →ᵣ µ₂)  →
    ϕ₁ ~ ϕ₁' →
    ϕ₁ ₛ∘ᵣ ϕ₂ ~ ϕ₁' ₛ∘ᵣ ϕ₂
  ~-cong-ₛ∘ᵣ₁ {ϕ₁ = ϕ₁} {ϕ₁'} ϕ₂ ϕ₁~ϕ₁' _ x  = ϕ₁~ϕ₁' _ (ϕ₂ _ x)

  ~-cong-ₛ∘ᵣ₂ : (ϕ₁ : µ₂ →ₛ µ₃) {ϕ₂ ϕ₂' : µ₁ →ᵣ µ₂}  →
    ϕ₂ ~ ϕ₂' →
    ϕ₁ ₛ∘ᵣ ϕ₂ ~ ϕ₁ ₛ∘ᵣ ϕ₂'
  ~-cong-ₛ∘ᵣ₂ ϕ₁ {ϕ₂} {ϕ₂'} ϕ₂~ϕ₂' _ x  = cong (ϕ₁ _) (ϕ₂~ϕ₂' _ x)

  kitₛᵣ : ComposeKit {{kitₛ}} {{kitᵣ}} {{kitₛ}}
  ComposeKit._∘ₖ_       kitₛᵣ = _ₛ∘ᵣ_
  ComposeKit.tm-⋯-∘     kitₛᵣ = λ σ₁ ρ₂ x → ⋯-var (σ₁ _ x) ρ₂ where instance _ = kitₛ
  ComposeKit.dist-↑-∘   kitₛᵣ = λ _ σ₁ ρ₂ → λ where
                                                    _ (here px) → refl
                                                    _ (there x) → refl
  ComposeKit.~-cong-∘₁  kitₛᵣ = ~-cong-ₛ∘ᵣ₁
  ComposeKit.~-cong-∘₂  kitₛᵣ = ~-cong-ₛ∘ᵣ₂
  ComposeKit._⋯'_       kitₛᵣ = λ t ρ → t ⋯ ρ
  ComposeKit._⋯''_      kitₛᵣ = λ x σ → σ _ x
  ComposeKit.tm-⋯''-∘   kitₛᵣ = λ ϕ₁ ϕ₂ x → refl
  ComposeKit.𝕂₁→𝕂      kitₛᵣ = λ t → t
  ComposeKit.𝕂₂→𝕂      kitₛᵣ = λ x → ` x
  ComposeKit.𝕂₁→𝕂₁     kitₛᵣ = λ { refl x → refl }
  ComposeKit.𝕂₂→𝕂₂     kitₛᵣ = λ ()
  ComposeKit.⋯''-var    kitₛᵣ = λ x ϕ → refl
  ComposeKit.~-cong-⋯'' kitₛᵣ = λ x f~g → f~g _ x

  private instance _ = kitᵣᵣ
  private instance _ = kitₛᵣ


  ~-cong-ᵣ∘ₛ₁ : {ϕ₁ ϕ₁' : µ₂ →ᵣ µ₃} (ϕ₂ : µ₁ →ₛ µ₂)  →
    ϕ₁ ~ ϕ₁' →
    ϕ₁ ᵣ∘ₛ ϕ₂ ~ ϕ₁' ᵣ∘ₛ ϕ₂
  ~-cong-ᵣ∘ₛ₁ {ϕ₁ = ϕ₁} {ϕ₁'} ϕ₂ ϕ₁~ϕ₁' _ x  =
    (ϕ₁  ᵣ∘ₛ ϕ₂) _ x ≡⟨⟩
    ϕ₂ _ x ⋯ᵣ ϕ₁     ≡⟨ ~-cong-⋯ _ ϕ₁~ϕ₁' ⟩
    ϕ₂ _ x ⋯ᵣ ϕ₁'    ≡⟨⟩
    (ϕ₁' ᵣ∘ₛ ϕ₂) _ x ∎

  ~-cong-ᵣ∘ₛ₂ : (ϕ₁ : µ₂ →ᵣ µ₃) {ϕ₂ ϕ₂' : µ₁ →ₛ µ₂}  →
    ϕ₂ ~ ϕ₂' →
    ϕ₁ ᵣ∘ₛ ϕ₂ ~ ϕ₁ ᵣ∘ₛ ϕ₂'
  ~-cong-ᵣ∘ₛ₂ ϕ₁ {ϕ₂} {ϕ₂'} ϕ₂~ϕ₂' _ x  =
    (ϕ₁  ᵣ∘ₛ ϕ₂) _ x ≡⟨⟩
    ϕ₂ _ x ⋯ᵣ ϕ₁     ≡⟨ cong (_⋯ᵣ ϕ₁) (ϕ₂~ϕ₂' _ x) ⟩
    ϕ₂' _ x ⋯ᵣ ϕ₁    ≡⟨⟩
    (ϕ₁ ᵣ∘ₛ ϕ₂') _ x ∎

  kitᵣₛ : ComposeKit {{kitᵣ}} {{kitₛ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitᵣₛ = _ᵣ∘ₛ_
  ComposeKit.tm-⋯-∘   kitᵣₛ = λ ρ₁ σ₂ x → refl
  ComposeKit.dist-↑-∘ kitᵣₛ =
    λ m₁ ρ₁ σ₂ → λ where
        m (here refl) →
          ((ρ₁ ᵣ∘ₛ σ₂) ↑ m) m (here refl)       ≡⟨⟩
          (` here refl)                         ≡⟨⟩
          (` ((ρ₁ ↑ m₁) _ (here refl)))         ≡⟨ sym (⋯-var (here refl) (ρ₁ ↑ m₁)) ⟩
          ((` here refl) ⋯ (ρ₁ ↑ m₁))           ≡⟨⟩
          ((ρ₁ ↑ m) ᵣ∘ₛ (σ₂ ↑ m)) m (here refl) ∎
        m (there x)   →
          (σ₂ m x ⋯ ρ₁) ⋯ wk          ≡⟨ ⋯-assoc (σ₂ m x) ρ₁ wk ⟩
          σ₂ m x ⋯ (wk ᵣ∘ᵣ ρ₁)        ≡⟨⟩
          σ₂ m x ⋯ ((ρ₁ ↑ m₁) ᵣ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ₂ m x) wk (ρ₁ ↑ m₁)) ⟩
          (σ₂ m x ⋯ wk) ⋯ (ρ₁ ↑ m₁)   ∎
  ComposeKit.~-cong-∘₁  kitᵣₛ = ~-cong-ᵣ∘ₛ₁
  ComposeKit.~-cong-∘₂  kitᵣₛ = ~-cong-ᵣ∘ₛ₂
  ComposeKit._⋯'_       kitᵣₛ = λ x σ → σ _ x
  ComposeKit._⋯''_      kitᵣₛ = λ t ρ → t ⋯ ρ
  ComposeKit.tm-⋯''-∘   kitᵣₛ = λ ϕ₁ ϕ₂ x → refl
  ComposeKit.𝕂₁→𝕂      kitᵣₛ = λ x → ` x
  ComposeKit.𝕂₂→𝕂      kitᵣₛ = λ t → t
  ComposeKit.𝕂₁→𝕂₁     kitᵣₛ = λ ()
  ComposeKit.𝕂₂→𝕂₂     kitᵣₛ = λ { refl x → refl }
  ComposeKit.⋯''-var    kitᵣₛ = λ x ϕ → ⋯-var x ϕ
  ComposeKit.~-cong-⋯'' kitᵣₛ = λ t f~g → ~-cong-⋯ t f~g

  private instance _ = kitᵣₛ

  ~-cong-ₛ∘ₛ₁ : {ϕ₁ ϕ₁' : µ₂ →ₛ µ₃} (ϕ₂ : µ₁ →ₛ µ₂)  →
    ϕ₁ ~ ϕ₁' →
    ϕ₁ ₛ∘ₛ ϕ₂ ~ ϕ₁' ₛ∘ₛ ϕ₂
  ~-cong-ₛ∘ₛ₁ {ϕ₁ = ϕ₁} {ϕ₁'} ϕ₂ ϕ₁~ϕ₁' _ x  =
    (ϕ₁  ₛ∘ₛ ϕ₂) _ x ≡⟨⟩
    ϕ₂ _ x ⋯ₛ ϕ₁     ≡⟨ ~-cong-⋯ _ ϕ₁~ϕ₁' ⟩
    ϕ₂ _ x ⋯ₛ ϕ₁'    ≡⟨⟩
    (ϕ₁' ₛ∘ₛ ϕ₂) _ x ∎

  ~-cong-ₛ∘ₛ₂ : (ϕ₁ : µ₂ →ₛ µ₃) {ϕ₂ ϕ₂' : µ₁ →ₛ µ₂}  →
    ϕ₂ ~ ϕ₂' →
    ϕ₁ ₛ∘ₛ ϕ₂ ~ ϕ₁ ₛ∘ₛ ϕ₂'
  ~-cong-ₛ∘ₛ₂ ϕ₁ {ϕ₂} {ϕ₂'} ϕ₂~ϕ₂' _ x  =
    (ϕ₁  ₛ∘ₛ ϕ₂) _ x ≡⟨⟩
    ϕ₂ _ x ⋯ₛ ϕ₁     ≡⟨ cong (_⋯ₛ ϕ₁) (ϕ₂~ϕ₂' _ x) ⟩
    ϕ₂' _ x ⋯ₛ ϕ₁    ≡⟨⟩
    (ϕ₁ ₛ∘ₛ ϕ₂') _ x ∎

  kitₛₛ : ComposeKit {{kitₛ}} {{kitₛ}} {{kitₛ}}
  ComposeKit._∘ₖ_     kitₛₛ = _ₛ∘ₛ_
  ComposeKit.tm-⋯-∘   kitₛₛ = λ σ₁ σ₂ x → refl
  ComposeKit.dist-↑-∘ kitₛₛ =
    λ m₁ σ₁ σ₂ → λ where
        m (here refl) →
          (` here refl)             ≡⟨ sym (⋯-var (here refl) (σ₁ ↑ m₁)) ⟩
          (` here refl) ⋯ (σ₁ ↑ m₁) ∎
        m (there x)   →
          (σ₂ m x ⋯ σ₁) ⋯ wk          ≡⟨ ⋯-assoc (σ₂ m x) σ₁ wk ⟩
          σ₂ m x ⋯ (wk ᵣ∘ₛ σ₁)        ≡⟨⟩
          σ₂ m x ⋯ ((σ₁ ↑ m₁) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ₂ m x) wk (σ₁ ↑ m₁)) ⟩
          (σ₂ m x ⋯ wk) ⋯ (σ₁ ↑ m₁)   ∎
  ComposeKit.~-cong-∘₁ kitₛₛ = ~-cong-ₛ∘ₛ₁
  ComposeKit.~-cong-∘₂ kitₛₛ = ~-cong-ₛ∘ₛ₂
  ComposeKit._⋯'_      kitₛₛ = λ t σ → t ⋯ σ
  ComposeKit._⋯''_     kitₛₛ = λ t σ → t ⋯ σ
  ComposeKit.tm-⋯''-∘  kitₛₛ = λ ϕ₁ ϕ₂ x → refl
  ComposeKit.𝕂₁→𝕂     kitₛₛ = λ t → t
  ComposeKit.𝕂₂→𝕂     kitₛₛ = λ t → t
  ComposeKit.𝕂₁→𝕂₁    kitₛₛ = λ { refl x → refl }
  ComposeKit.𝕂₂→𝕂₂    kitₛₛ = λ { refl x → refl }
  ComposeKit.⋯''-var   kitₛₛ = λ x ϕ → ⋯-var x ϕ
  ComposeKit.~-cong-⋯'' kitₛₛ = λ t f~g → ~-cong-⋯ t f~g

  private instance _ = kitₛₛ

  record WkDistKit
      {{𝕂 : Kit}}
      {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
      {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
      : Set₁ where
    field
      comm-↑-wk : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
        (ϕ ↑ m) ∘ₖ wkᵣ ~ wkᵣ ∘ₖ ϕ
      wk-cancels-,ₖ-∘ : ∀ (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
        (ϕ ,ₖ v) ∘ₖ wkᵣ ~ ϕ

    -- TODO: generalize kitᵣ to arbitrary kits and include ⦅⦆ lemmas.

    -- This isn't limited to renamings i.e. wkᵣ ...
    dist-↑-f : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
      v ⋯ᵣ wkᵣ ⋯ (ϕ ↑ m) ≡ v ⋯ ϕ ⋯ᵣ wkᵣ
    dist-↑-f v ϕ =
      v ⋯ wkᵣ ⋯ (ϕ ↑ _)  ≡⟨ ⋯-assoc v wk (ϕ ↑ _)  ⟩
      v ⋯ (ϕ ↑ _) ∘ₖ wkᵣ ≡⟨ ~-cong-⋯ v (comm-↑-wk ϕ) ⟩
      v ⋯ wkᵣ ∘ₖ ϕ       ≡⟨ sym (⋯-assoc v ϕ wk) ⟩
      v ⋯ ϕ ⋯ wkᵣ        ∎

    wk-cancels-,ₖ : ∀ (v : µ₁ ⊢ M) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) (v' : µ₂ ∋/⊢[ 𝕂 ] id/m→M m) →
      v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v') ≡ v ⋯ ϕ
    wk-cancels-,ₖ v ϕ v' =
      v ⋯ᵣ wkᵣ ⋯ (ϕ ,ₖ v')   ≡⟨ ⋯-assoc v wkᵣ (ϕ ,ₖ v') ⟩
      v ⋯ ((ϕ ,ₖ v') ∘ₖ wkᵣ) ≡⟨ ~-cong-⋯ _ (wk-cancels-,ₖ-∘ ϕ v') ⟩
      v ⋯ ϕ                  ∎

  wk-kitᵣ : WkDistKit {{kitᵣ}} {{kitᵣᵣ}} {{kitᵣᵣ}}
  wk-kitᵣ = record
    { comm-↑-wk = λ ϕ → ~-refl
    ; wk-cancels-,ₖ-∘ = λ ϕ v → ~-refl
    }

  wk-kitₛ : WkDistKit {{kitₛ}} {{kitₛᵣ}} {{kitᵣₛ}}
  wk-kitₛ = record
    { comm-↑-wk = λ ϕ → ~-refl
    ; wk-cancels-,ₖ-∘ = λ ϕ v → ~-refl
    }

  private instance _ = wk-kitᵣ
  private instance _ = wk-kitₛ

  open WkDistKit {{...}}

  open WkDistKit wk-kitᵣ public renaming (dist-↑-f to dist-↑-ren; wk-cancels-,ₖ to wk-cancels-,ᵣ) using ()
  open WkDistKit wk-kitₛ public renaming (dist-↑-f to dist-↑-sub; wk-cancels-,ₖ to wk-cancels-,ₛ) using ()

  record KitAssocLemmas : Set₁ where
    open ComposeKit {{...}}

    field
      ⋯-id : ∀ {{𝕂 : Kit}} {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{𝕂}} ≡ v

    ⋯-idₛ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitₛ}} ≡ v
    ⋯-idₛ = ⋯-id

    ⋯-idᵣ : ∀ {µ M} (v : µ ⊢ M) → v ⋯ idₖ {{kitᵣ}} ≡ v
    ⋯-idᵣ = ⋯-id

    -- record KitAssocLemmas'' : Set₁ where
    --   field
    --     ⋯''-id : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
    --               ⦃ C : ComposeKit ⦃ 𝕂₁ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
    --               {µ M} (v : µ ∋/⊢[ 𝕂₂ ] M)
    --             → v ⋯[ C ] idₖ ≡ v

    ren→sub : ∀ (e : µ₁ ⊢ M) (ρ : µ₁ →ᵣ µ₂) →
              e ⋯ᵣ ρ ≡ e ⋯ₛ (idₛ ₛ∘ᵣ ρ)
    ren→sub e ρ =
      e ⋯ᵣ ρ           ≡⟨ sym (⋯-idₛ (e ⋯ᵣ ρ)) ⟩
      e ⋯ᵣ ρ ⋯ₛ idₛ    ≡⟨ ⋯-assoc e ρ id/` ⟩
      e ⋯ₛ (idₛ ₛ∘ᵣ ρ) ∎

    -- ren→sub' : ∀ ⦃ 𝕂₂ 𝕂 : Kit ⦄
    --              ⦃ Cᵣ : ComposeKit ⦃ kitᵣ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
    --              ⦃ Cₛ : ComposeKit ⦃ kitₛ ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
    --              (e : µ₁ ∋/⊢[ 𝕂₂ ] id/m→M m) (ρ : µ₁ →ᵣ µ₂) →
    --            e ⋯[ Cᵣ ] ρ ≡ e ⋯[ Cₛ ] (idₛ ₛ∘ᵣ ρ)
    -- ren→sub' e ρ = {!!}
    --   -- e ⋯ᵣ ρ           ≡⟨ sym (⋯-idₛ (e ⋯ᵣ ρ)) ⟩
    --   -- e ⋯ᵣ ρ ⋯ₛ idₛ    ≡⟨ ⋯-assoc e ρ id/` ⟩
    --   -- e ⋯ₛ (idₛ ₛ∘ᵣ ρ) ∎

    wk-cancels-⦅⦆ :
      ∀ {{𝕂 : Kit}}
        {{𝔸₁ : ComposeKit {{𝕂}} {{kitᵣ}} {{𝕂}} }}
        {{𝔸₂ : ComposeKit {{kitᵣ}} {{𝕂}} {{𝕂}} }}
        {{_ : WkDistKit {{𝕂}} {{𝔸₁}} {{𝔸₂}} }} {µ M m}
        (v : µ ⊢ M) (v' : µ ∋/⊢[ 𝕂 ] id/m→M m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡ v
    wk-cancels-⦅⦆ v v' =
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ ≡⟨ wk-cancels-,ₖ v idₖ v' ⟩
      v ⋯ idₖ          ≡⟨ ⋯-id v ⟩
      v                ∎

    wk-cancels-⦅⦆ᵣ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ∋ m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ᵣ ≡ v
    wk-cancels-⦅⦆ᵣ = wk-cancels-⦅⦆

    wk-cancels-⦅⦆ₛ : ∀ {µ M m} (v : µ ⊢ M) (v' : µ ⊢ m→M m) →
      v ⋯ wkᵣ ⋯ ⦅ v' ⦆ₛ ≡ v
    wk-cancels-⦅⦆ₛ = wk-cancels-⦅⦆

    -- TODO: prove for other combinations between ρ and σ.
    ↑∘⦅⦆-is-,ₛ : ∀ {µ₁ µ₂ m} (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      ⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m) ~ σ ,ₛ t
    ↑∘⦅⦆-is-,ₛ t σ _ (here refl) = ⋯-var (here refl) ⦅ t ⦆
    ↑∘⦅⦆-is-,ₛ t σ _ (there x)   = wk-cancels-⦅⦆ₛ (σ _ x) t

    -- TODO: prove for other combinations between ρ and σ.
    ⋯↑⋯⦅⦆-is-⋯,ₛ : ∀ {µ₁ µ₂ m} (t' : (µ₁ ▷ m) ⊢ M) (t : µ₂ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      t' ⋯ (σ ↑ m) ⋯ ⦅ t ⦆ₛ ≡ t' ⋯ (σ ,ₛ t)
    ⋯↑⋯⦅⦆-is-⋯,ₛ {m = m} t' t σ =
      t' ⋯ₛ (σ ↑ m) ⋯ₛ ⦅ t ⦆ₛ    ≡⟨ ⋯-assoc t' (σ ↑ m) ⦅ t ⦆ₛ ⟩
      t' ⋯ₛ (⦅ t ⦆ₛ ₛ∘ₛ (σ ↑ m)) ≡⟨ ~-cong-⋯ t' (↑∘⦅⦆-is-,ₛ t σ) ⟩
      t' ⋯ₛ (σ ,ₛ t)             ∎

    dist-ᵣ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
      ρ ᵣ∘ᵣ ⦅ x ⦆ ~ ⦅ ρ _ x ⦆ ᵣ∘ᵣ (ρ ↑ m)
    dist-ᵣ∘ᵣ-⦅⦆ x σ _ (here refl) = refl
    dist-ᵣ∘ᵣ-⦅⦆ x σ _ (there _)   = refl

    dist-ᵣ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
      ρ ᵣ∘ₛ ⦅ t ⦆ ~ ⦅ t ⋯ ρ ⦆ ₛ∘ᵣ (ρ ↑ m)
    dist-ᵣ∘ₛ-⦅⦆ t σ _ (here refl) = refl
    dist-ᵣ∘ₛ-⦅⦆ t σ _ (there x)   = ⋯-var x σ

    dist-ₛ∘ᵣ-⦅⦆ : ∀ {µ₁ µ₂ m} (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      σ ₛ∘ᵣ ⦅ x ⦆ ~ ⦅ σ _ x ⦆ ₛ∘ₛ (σ ↑ m)
    dist-ₛ∘ᵣ-⦅⦆ x σ _ (here refl) = sym (⋯-var (here refl) ⦅ σ _ x ⦆)
    dist-ₛ∘ᵣ-⦅⦆ x σ _ (there y) =
        σ _ y                             ≡⟨ sym (⋯-id (σ _ y)) ⟩
        σ _ y ⋯ ((idₖ ,ₖ (σ _ x)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ y) wk ⦅ σ _ x ⦆) ⟩
        (σ _ y ⋯ wk) ⋯ (idₖ ,ₖ (σ _ x))   ∎

    dist-ₛ∘ₛ-⦅⦆ : ∀ {µ₁ µ₂ m} (t : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      σ ₛ∘ₛ ⦅ t ⦆ ~ ⦅ t ⋯ σ ⦆ ₛ∘ₛ (σ ↑ m)
    dist-ₛ∘ₛ-⦅⦆ t σ _ (here refl) =
        t ⋯ σ                     ≡⟨⟩
        ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
        (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
    dist-ₛ∘ₛ-⦅⦆ t σ _ (there x) =
        (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
        σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
        σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
        (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎

    dist-⦅⦆ᵣ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (ρ : µ₁ →ᵣ µ₂) →
      t ⋯ ⦅ x ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ ρ _ x ⦆
    dist-⦅⦆ᵣ-⋯ᵣ t x ρ = ∘~∘→⋯≡⋯ (dist-ᵣ∘ᵣ-⦅⦆ x ρ) t

    dist-⦅⦆ₛ-⋯ᵣ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ρ : µ₁ →ᵣ µ₂) →
      t ⋯ ⦅ t' ⦆ ⋯ ρ ≡ t ⋯ (ρ ↑ m) ⋯ ⦅ t' ⋯ ρ ⦆
    dist-⦅⦆ₛ-⋯ᵣ t t' ρ = ∘~∘→⋯≡⋯ (dist-ᵣ∘ₛ-⦅⦆ t' ρ) t

    dist-⦅⦆ᵣ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (x : µ₁ ∋ m) (σ : µ₁ →ₛ µ₂) →
      t ⋯ ⦅ x ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ σ _ x ⦆
    dist-⦅⦆ᵣ-⋯ₛ t₂ t σ = ∘~∘→⋯≡⋯ (dist-ₛ∘ᵣ-⦅⦆ t σ) t₂

    dist-⦅⦆ₛ-⋯ₛ : ∀ {µ₁ µ₂ m M} (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (σ : µ₁ →ₛ µ₂) →
      t ⋯ ⦅ t' ⦆ ⋯ σ ≡ t ⋯ (σ ↑ m) ⋯ ⦅ t' ⋯ σ ⦆
    dist-⦅⦆ₛ-⋯ₛ t₂ t σ = ∘~∘→⋯≡⋯ (dist-ₛ∘ₛ-⦅⦆ t σ) t₂

    -- postulate TODO : ∀ {ℓ} {A : Set ℓ} → A

    -- open import Kitty.Util.Star
    -- open import Data.List using (_++_)

    -- _–[_]→*_ : List VarMode → (_ : List Kit) → List VarMode → Set _
    -- µ₁ –[ 𝕂s ]→* µ₂ = Star (λ 𝕂 x y → y –[ 𝕂 ]→ x) 𝕂s µ₂ µ₁

    -- infixl  6  _↑**_
    -- _↑**_ : {𝕂s : List Kit} → µ₁ –[ 𝕂s ]→* µ₂ → ∀ µ' → (µ' ++ µ₁) –[ 𝕂s ]→* (µ' ++ µ₂)
    -- [] ↑** µ' = []
    -- (_∷_ {b = 𝕂} f fs) ↑** µ' = (Kit._↑*_ 𝕂 f µ') ∷ (fs ↑** µ')

    -- infixl  5 _⋯*_
    -- _⋯*_ : ∀ {𝕂s : List Kit} {µ₁ µ₂ M} →
    --       µ₁ ⊢ M → µ₁ –[ 𝕂s ]→* µ₂ → µ₂ ⊢ M
    -- t ⋯* fs = fold-star' (λ 𝕂 _ _ t f → _⋯_ {{𝕂}} t f) t fs

    -- _≈ₓ_ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
    -- _≈ₓ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {m} (x : (µ₁ ▷▷ µ₁') ∋ m) → (` x) ⋯* (f ↑** µ₁') ≡ (` x) ⋯* (g ↑** µ₁')

    -- _≈ₜ_ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} → (f : µ₁ –[ 𝕂s₁ ]→* µ₂) → (g : µ₁ –[ 𝕂s₂ ]→* µ₂) → Set
    -- _≈ₜ_ {µ₁ = µ₁} f g = ∀ {µ₁'} {M} (t : (µ₁ ▷▷ µ₁') ⊢ M) → t ⋯* (f ↑** µ₁') ≡ t ⋯* (g ↑** µ₁')

    -- ⋯-↑ : ∀ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
    --       f ≈ₓ g → f ≈ₜ g
    -- ⋯-↑ = TODO

    -- dist-⦅⦆-∘ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
    --               ⦃ C₂₁ : ComposeKit ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂 ⦄ ⦄
    --               ⦃ C : ComposeKit ⦃ 𝕂 ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
    --               {µ₁ µ₂ m}
    --               (t' :  µ₁ ∋/⊢[ 𝕂₁ ] Kit.id/m→M 𝕂₁ m) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    --   ComposeKit._∘ₖ_ C₂₁ ϕ ⦅ t' ⦆ ~ ComposeKit._∘ₖ_ C ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆ (ϕ ↑ m) 
    -- dist-⦅⦆-∘ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t' ϕ _ (here refl) =
    --   (ϕ ∘[ C₂₁ ] ⦅ t' ⦆) _ (here refl)                    ≡⟨ sym (ComposeKit.tm-⋯''-∘ C₂₁ ⦅ t' ⦆ ϕ (here refl) ) ⟩
    --   ⦅ t' ⦆ _ (here refl) ⋯[ C₂₁ ] ϕ                      ≡⟨⟩
    --   t' ⋯[ C₂₁ ] ϕ                                        ≡⟨ sym (ComposeKit.𝕂₁→𝕂₁ C refl (t' ⋯[ C₂₁ ] ϕ) ) ⟩
    --   ComposeKit.𝕂₁→𝕂 C (t' ⋯[ C₂₁ ] ϕ)                    ≡⟨⟩
    --   ComposeKit.𝕂₁→𝕂 C (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ _ (here refl))  ≡⟨ sym (ComposeKit.⋯''-var C (here refl) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆) ⟩
    --   id/` _ (here refl) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆          ≡⟨⟩
    --   (ϕ ↑ _) _ (here refl) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨ ComposeKit.tm-⋯''-∘ C (ϕ ↑ _) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆ (here refl) ⟩
    --   (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ ∘[ C ] (ϕ ↑ _)) _ (here refl)     ∎
    -- dist-⦅⦆-∘ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t' ϕ _ (there x) =
    --   (ϕ ∘[ C₂₁ ] ⦅ t' ⦆) _ (there x)                    ≡⟨ sym (ComposeKit.tm-⋯''-∘ C₂₁ ⦅ t' ⦆ ϕ (there x) ) ⟩
    --   ⦅ t' ⦆ _ (there x)  ⋯[ C₂₁ ] ϕ                      ≡⟨⟩
    --   id/` _ x            ⋯[ C₂₁ ] ϕ                      ≡⟨ {!!} ⟩
    --   ComposeKit.𝕂₁→𝕂 C₂₁ (ϕ _ x)                             ≡⟨ {!!} ⟩
    --   wk _ (ϕ _ x)        ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨⟩
    --   (ϕ ↑ _) _ (there x) ⋯[ C ] ⦅ t' ⋯[ C₂₁ ] ϕ ⦆       ≡⟨ ComposeKit.tm-⋯''-∘ C (ϕ ↑ _) ⦅ t' ⋯[ C₂₁ ] ϕ ⦆ (there x) ⟩
    --   (⦅ t' ⋯[ C₂₁ ] ϕ ⦆ ∘[ C ] (ϕ ↑ _)) _ (there x)     ∎

    -- -- ⋯''-var : ∀ (x : µ₁ ∋ m) (ϕ : µ₁ –[ 𝕂₁ ]→ µ₂) →
    -- --   id/` _ x ⋯'' ϕ ≡ 𝕂₁→𝕂 (ϕ _ x)

    -- -- tm-⋯''-∘ : (ϕ₁ : µ₁ –[ 𝕂₂ ]→ µ₂) (ϕ₂ : µ₂ –[ 𝕂₁ ]→ µ₃) (x : µ₁ ∋ m) →
    -- --   (ϕ₁ _ x) ⋯'' ϕ₂ ≡ (ϕ₂ ∘ₖ ϕ₁) _ x

    -- -- dist-ₛ∘ₛ-⦅⦆ t σ _ (here refl) =
    -- --     t ⋯ σ                     ≡⟨⟩
    -- --     ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
    -- --     (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
    -- -- dist-ₛ∘ₛ-⦅⦆ t σ _ (there x) =
    -- --     (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
    -- --     σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
    -- --     σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
    -- --     (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎

    -- dist-⦅⦆-⋯ : ∀ ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit ⦄
    --               ⦃ C₂₁ : ComposeKit ⦃ 𝕂₂ ⦄ ⦃ 𝕂₁ ⦄ ⦃ 𝕂 ⦄ ⦄
    --               ⦃ C : ComposeKit ⦃ 𝕂 ⦄ ⦃ 𝕂₂ ⦄ ⦃ 𝕂 ⦄ ⦄
    --               {µ₁ µ₂ m M}
    --               (t : (m ∷ µ₁) ⊢ M) (t' : Kit._∋/⊢_ 𝕂₁ µ₁ (id/m→M m)) (ϕ : µ₁ –[ 𝕂₂ ]→ µ₂) →
    --   t ⋯ ⦅ t' ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆
    -- dist-⦅⦆-⋯ ⦃ C₂₁ = C₂₁ ⦄ ⦃ C = C ⦄ t t' ϕ =
    --   t ⋯ ⦅ t' ⦆ ⋯ ϕ                                               ≡⟨ ⋯-assoc t ⦅ t' ⦆ ϕ ⟩
    --   t ⋯ (ComposeKit._∘ₖ_ C₂₁ ϕ ⦅ t' ⦆)                           ≡⟨ ~-cong-⋯ t (dist-⦅⦆-∘ t' ϕ) ⟩
    --   t ⋯ (ComposeKit._∘ₖ_ C ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆ (ϕ ↑ _)) ≡⟨ sym (⋯-assoc t (ϕ ↑ _) ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆) ⟩
    --   t ⋯ (ϕ ↑ _) ⋯ ⦅ ComposeKit._⋯''_ C₂₁ t' ϕ ⦆                   ∎

    -- dist-⦅⦆-⋯ₛ : ∀ ⦃ 𝕂 : Kit ⦄
    --               (t : (m ∷ µ₁) ⊢ M) (t' : µ₁ ⊢ m→M m) (ϕ : µ₁ –[ 𝕂 ]→ µ₂) →
    --   t ⋯ ⦅ t' ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ t' ⋯ ϕ ⦆
    -- dist-⦅⦆-⋯ₛ t t' ϕ =
    --   t ⋯ ⦅ t' ⦆ ⋯ ϕ              ≡⟨ {!!} ⟩
    --   -- t ⋯ (ϕ ∘ₖ ⦅ t' ⦆)           ≡⟨ {!!} ⟩
    --   -- t ⋯ (⦅ t' ⋯ ϕ ⦆ ∘ₖ (ϕ ↑ _)) ≡⟨ {!!} ⟩
    --   t ⋯ ϕ ↑ _ ⋯ ⦅ t' ⋯ ϕ ⦆      ∎

  -- record KitTraversalLemmas : Set₁ where
  --   open AssocAssumptions {{...}}
  --   field
  --     {{kit-traversal}} : KitTraversal
  --     ⋯-id : ∀ {{𝕂 : Kit}} (v : µ ⊢ K) → v ⋯ idₖ {{𝕂}} ≡ v

  --   dist-∘-⦅⦆ :
  --     ∀ {{𝕂₁ : Kit }}
  --       {{𝕂₂ : Kit }}
  --       {{𝕂  : Kit }}
  --       {{𝔸₁ : AssocAssumptions {{kit-traversal}} {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
  --       {{𝔸₂ : AssocAssumptions {{kit-traversal}} {{𝕂₂}} {{𝕂₁}} {{𝕂}} }}
  --       {{_ : KitCompose {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{kit-traversal}} {{𝔸₁}} }}
  --       {{_ : KitCompose {{𝕂₂}} {{𝕂₁}} {{𝕂}} {{kit-traversal}} {{𝔸₂}} }}
  --       (t : µ ◆ k→SK k) (σ : µ₁ –[ 𝕂₁ ]→ µ₂) →
  --     σ ∘ₖ ⦅ t ⦆ ≡ ⦅ `/id _ t ⋯ σ ⦆ ∘ₖ (σ ↑ k)
  --   -- ⦅_⦆ : µ ◆ k→SK k → (k ∷ µ) –→ µ
  --   dist-∘-⦅⦆ t σ = {!!}
  --   -- dist-∘-⦅⦆ t σ = fun-ext₂ λ where
  --   --   _ (here refl) →
  --   --     t ⋯ σ                     ≡⟨⟩
  --   --     ⦅ t ⋯ σ ⦆ _ (here refl)   ≡⟨ sym (⋯-var (here refl) ⦅ t ⋯ σ ⦆) ⟩
  --   --     (` here refl) ⋯ ⦅ t ⋯ σ ⦆ ∎
  --   --   _ (there x) →
  --   --     (` x) ⋯ σ                         ≡⟨ ⋯-var x σ ⟩
  --   --     σ _ x                             ≡⟨ sym (⋯-id (σ _ x)) ⟩
  --   --     σ _ x ⋯ ((idₖ ,ₖ (t ⋯ σ)) ₛ∘ᵣ wk) ≡⟨ sym (⋯-assoc (σ _ x) wk ⦅ t ⋯ σ ⦆) ⟩
  --   --     (σ _ x ⋯ wk) ⋯ (idₖ ,ₖ (t ⋯ σ))   ∎
