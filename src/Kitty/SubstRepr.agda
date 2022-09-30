open import Kitty.Modes

module Kitty.SubstRepr {𝕄 : Modes} (𝕋 : Terms 𝕄) where

open import Data.List using (List; []; _∷_)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Primitive using (Level; _⊔_)

open import Kitty.Prelude
import Kitty.Kit 𝕋 as FKit

open Modes 𝕄

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
  M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
  µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

-- Binary Homotopy
infix 3 _~_
_~_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃}
        (f g : (a : A) → (b : B a) → C a b)
      → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
ϕ₁ ~ ϕ₂ = ∀ m x → ϕ₁ m x ≡ ϕ₂ m x

module DKit where
  open FKit using (Kit)
  open Kit ⦃ ... ⦄ using 
    ( VarMode/TermMode ; _∋/⊢_
    ; id/m→M ; m→M/id ; id/m→M/id
    ; id/` ; `/id ; id/`/id
    ; wk-id/` ) renaming (wk to wk-⊢; _–→_ to _⟦–→⟧_)

  data _–→_ ⦃ K : Kit ⦄ : List VarMode → List VarMode → Set where
    0ₖ   : [] –→ []
    id   : µ –→ µ
    ⦅_⦆  : µ ∋/⊢ id/m→M m → (µ ▷ m) –→ µ
    ⦅_⦆₀ : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
    _∥_  : µ₁ –→ µ → µ₂ –→ µ → (µ₁ ▷▷ µ₂) –→ µ
    _∥₁_  : µ₁ –→ µ → ([] ▷ m) –→ µ → (µ₁ ▷ m) –→ µ
    wk   : µ –→ (µ ▷ m)
    _,ₖ_ : µ₁ –→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –→ µ₂
    _↑_  : µ₁ –→ µ₂ → ∀ m → (µ₁ ▷ m) –→ (µ₂ ▷ m)
    _∘_  : µ₂ –→ µ₃ → µ₁ –→ µ₂ → µ₁ –→ µ₃

  _–[_]→_ : List VarMode → Kit → List VarMode → Set
  µ₁ –[ K ]→ µ₂ = _–→_ ⦃ K ⦄ µ₁ µ₂

  module _ ⦃ K : Kit ⦄ where

    id' : µ –→ µ
    id' {[]}    = 0ₖ
    id' {µ ▷ m} = id' ↑ m

    0ₖ'  : [] –→ []
    0ₖ'  = id

    ⦅_⦆' ⦅_⦆'' : µ ∋/⊢ id/m→M m → (µ ▷ m) –→ µ
    ⦅ t ⦆'  = id ,ₖ t
    ⦅ t ⦆'' = id ∥ ⦅ t ⦆₀

    ⦅_⦆₀' : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
    ⦅ t ⦆₀' = {!0ₖ ∥₁ !}

    _∥'_ : µ₁ –→ µ → µ₂ –→ µ → (µ₁ ▷▷ µ₂) –→ µ
    ϕ₁ ∥' ϕ₂ = {!!}

    _∥₁'_  : µ₁ –→ µ → ([] ▷ m) –→ µ → (µ₁ ▷ m) –→ µ
    ϕ₁ ∥₁' ϕ₂ = {!!} ∘ (id ,ₖ {!!})
    -- ϕ₁ ∥₁' ϕ₂ = {!!} ∘ (ϕ₁ ↑ _)

    _,ₖ'_ : µ₁ –→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –→ µ₂
    ϕ ,ₖ' t = ϕ ∥ ⦅ t ⦆₀

    wk' : µ –→ (µ ▷ m)
    wk' = {!id ,ₖ ?!}

    _↑'_  : µ₁ –→ µ₂ → ∀ m → (µ₁ ▷ m) –→ (µ₂ ▷ m)
    -- ϕ ↑' m = (wk ∘ ϕ) ∥₁ (wk ∘ ⦅ id/` m {! !} ⦆₀)
    ϕ ↑' m = {!ϕ ,ₖ ?!}
    -- ϕ ↑' m = wk ∘ (ϕ ,ₖ {!!})
    -- ϕ ↑' m = (wk ∘ ϕ) ,ₖ {!!}

module DKitSem where
  open FKit using (Kit)
  open Kit ⦃ ... ⦄ using 
    ( VarMode/TermMode ; _∋/⊢_
    ; id/m→M ; m→M/id ; id/m→M/id
    ; id/` ; `/id ; id/`/id
    ; wk-id/` ) renaming (wk to wk-⊢; _–→_ to _⟦–→⟧_)
  open import Data.List.Relation.Unary.Any using (here; there)

  data All {A : Set ℓ₁} (R : A → Set ℓ₂) : List A → Set ℓ₂ where
    [] : All R []
    _∷_ : ∀ {x xs} → R x → All R xs → All R (x ∷ xs)

  _⟦–→⟧'_ : ⦃ K : Kit ⦄ → List VarMode → List VarMode → Set
  µ₁ ⟦–→⟧' µ₂ = All (λ m → µ₂ ∋/⊢ id/m→M m) µ₁

  ⟦–→⟧'→⟦–→⟧ : ⦃ K : Kit ⦄ → µ₁ ⟦–→⟧' µ₂ → µ₁ ⟦–→⟧ µ₂
  ⟦–→⟧'→⟦–→⟧ []      m ()
  ⟦–→⟧'→⟦–→⟧ (t ∷ ϕ) m (here refl) = t
  ⟦–→⟧'→⟦–→⟧ (t ∷ ϕ) m (there x)   = ⟦–→⟧'→⟦–→⟧ ϕ m x

  data _–→_ ⦃ K : Kit ⦄ : List VarMode → List VarMode → Set where
    id    : µ –→ µ
    _∘_   : µ₂ –→ µ₃ → µ₁ –→ µ₂ → µ₁ –→ µ₃
    _∥_   : µ₁ –→ µ → µ₂ –→ µ → (µ₁ ▷▷ µ₂) –→ µ
    wk    : µ –→ (µ ▷▷ µ')
    kw    : µ –→ (µ' ▷▷ µ)
    ⟦_⟧⁻¹ : µ₁ ⟦–→⟧' µ₂ → µ₁ –→ µ₂ 
    -- wk    : ∀ µ₁ µ₂ → µ –→ (µ₁ ▷▷ µ ▷▷ µ₂)

  -- 0ₖ    : [] –→ []
  -- _↑_  : ⦃ K : Kit ⦄ → µ₁ –→ µ₂ → ∀ µ → (µ₁ ▷▷ µ) –→ (µ₂ ▷▷ µ)
  -- _↓_  : ⦃ K : Kit ⦄ → µ₁ –→ µ₂ → ∀ µ → (µ ▷▷ µ₁) –→ (µ ▷▷ µ₂)
  -- ⦅_⦆₀ : µ ∋/⊢ id/m→M m → ([] ▷ m) –→ µ
  -- _,ₖ_ : µ₁ –→ µ₂ → µ₂ ∋/⊢ id/m→M m → (µ₁ ▷ m) –→ µ₂
  -- ⦅_⦆  : µ ∋/⊢ id/m→M m → (µ ▷ m) –→ µ
  pattern 0ₖ       = id {µ = []}
  pattern ⦅_⦆₀ t   = ⟦ t ∷ [] ⟧⁻¹
  pattern _,ₖ_ ϕ t = ϕ ∥ ⦅ t ⦆₀
  pattern ⦅_⦆ t    = id ,ₖ t
  pattern _↑_ ϕ µ  = (wk ∘ ϕ) ∥ kw {µ = µ}
  pattern _↓_ ϕ µ  = wk ∥ (kw {µ' = µ} ∘ ϕ)

  open FKit
  open import Kitty.Compose 𝕋
  module _ (KT : KitTraversal) (KA : KitAssoc KT) (KAL : KitAssoc.KitAssocLemmas KT KA) where
    open KitTraversal KT
    open KitAssoc KT KA
    open KitAssocLemmas KAL

    module KIT = Kit ⦃ ... ⦄
    module CKIT = ComposeKit ⦃ ... ⦄

    ⟦_⟧ : ⦃ K : Kit ⦄ ⦃ CK : ComposeKit KT ⦃ K ⦄ ⦃ K ⦄ ⦃ K ⦄ ⦄ → µ₁ –→ µ₂ → µ₁ ⟦–→⟧ µ₂
    ⟦ id       ⟧ = KIT.idₖ
    ⟦ ϕ₁ ∘ ϕ₂  ⟧ = ⟦ ϕ₁ ⟧ CKIT.∘ₖ ⟦ ϕ₂ ⟧
    ⟦ ϕ₁ ∥ ϕ₂  ⟧ = ⟦ ϕ₁ ⟧ KIT.∥ ⟦ ϕ₂ ⟧
    ⟦ ⟦ ts ⟧⁻¹ ⟧ = ⟦–→⟧'→⟦–→⟧ ts
    ⟦ wk       ⟧ = KIT.wk'*
    ⟦ kw       ⟧ = KIT.idₖ'

    module Lemmas ⦃ K : Kit ⦄ ⦃ CK : ComposeKit KT ⦃ K ⦄ ⦃ K ⦄ ⦃ K ⦄ ⦄ where
      ∥0 : (ϕ : µ₁ –→ []) → ⟦ ϕ ∥ 0ₖ ⟧ ~ ⟦ ϕ ⟧
      ∥0 ϕ m x = refl

      0∥ : let s = subst (_⟦–→⟧ _) (ListP.++-identityʳ µ₁) in
           (ϕ : µ₁ –→ []) → s ⟦ 0ₖ ∥ ϕ ⟧ ~ ⟦ ϕ ⟧
      0∥ {µ₁ = µ₁ ▷ m₁} ϕ .m₁ (here refl) = {!!}
      0∥ {µ₁ = µ₁ ▷ m₁} ϕ m (there x) = {!!}

      -- 0∥ : let s = subst (_–→ _) (ListP.++-identityʳ µ₁) in
      --      (ϕ : µ₁ –→ []) → ⟦ s (0ₖ ∥ ϕ) ⟧ ~ ⟦ ϕ ⟧
      -- 0∥ {µ₁ = µ₁ ▷ m₁} ϕ .m₁ (here refl) = {!!}
      -- 0∥ {µ₁ = µ₁ ▷ m₁} ϕ m (there x) = {!!}
      -- 0∥ ϕ m (here refl) = {!ref!}
      -- 0∥ ϕ m (there x) = {!!}

      -- TODO: probably easier to proof this in the semantic realm
      dist-∘-∥ : (ϕ : µ –→ µ') → (ϕ₁ : µ₁ –→ µ) → (ϕ₂ : µ₂ –→ µ)
          → ⟦ ϕ ∘ (ϕ₁ ∥ ϕ₂) ⟧ ~ ⟦ (ϕ ∘ ϕ₁) ∥ (ϕ ∘ ϕ₂) ⟧ 
      -- dist-∘-∥ ϕ ϕ₁ ϕ₂ m x = {!x!}
      dist-∘-∥ {µ₁ = .(_ ▷ m)} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (here refl) = refl
      dist-∘-∥ {µ₁ = .(_ ▷ _)} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (there x) = {!dist-∘-∥ ϕ ϕ₁ ϕ₂ m x!}
      dist-∘-∥ {µ₁ = µ₁} {µ₂ = µ₂ ▷ x₁} ϕ ϕ₁ ϕ₂ m x = {!!}

      -- pull in wk and then use lemma below (doesn't work, only works from left)
      lem : (ϕ₁ : µ₁ –→ µ) → (ϕ₂ : µ₂ –→ µ)
          → ⟦ (ϕ₁ ∥ ϕ₂) ∘ wk {µ' = µ₂} ⟧ ~ ⟦ ϕ₁ ⟧ 
      lem ϕ₁ ϕ₂ m (here refl) = {!refl!}
      lem ϕ₁ ϕ₂ m (there x) = {!!}

      -- lem' : (ϕ : (µ₁ ▷▷ µ₂) –→ µ)
      --      → ⟦ ϕ ∘ wk {µ' = µ₂} ⟧ ~ ⟦ id {µ₁} ⟧ 
      -- lem' ϕ m (here refl) = {!refl!}
      -- lem' ϕ m (there x) = {!!}

    simp : ⦃ K : Kit ⦄ → µ₁ –→ µ₂ → µ₁ –→ µ₂
    simp (ϕ₁ ∘ id) = ϕ₁
    simp (ϕ₁ ∘ (ϕ₂ ∘ ϕ₃)) = {!!}
    simp (ϕ₁ ∘ (ϕ₂ ∥ ϕ₃)) = (ϕ₁ ∘ ϕ₂) ∥ (ϕ₁ ∘ ϕ₃)
    simp (ϕ₁ ∘ ⟦ ts ⟧⁻¹) = {!!}
    simp (ϕ₁ ∘ wk) = {!!}
    simp (ϕ₁ ∘ kw) = {!!}
    simp (ϕ₁ ∥ ϕ₂) = {!!}
    simp ϕ         = ϕ

open import Kitty.Kit 𝕋
open import Kitty.Compose 𝕋
module _ (KT : KitTraversal) (KA : KitAssoc KT) (KAL : KitAssoc.KitAssocLemmas KT KA) where
  open KitTraversal KT
  open KitAssoc KT KA
  open KitAssocLemmas KAL

  open Kit ⦃ ... ⦄
  open ComposeKit ⦃ ... ⦄ renaming (_∘ₖ_ to _∘_)
  open import Data.List.Relation.Unary.Any using (here; there)

  module Lemmas ⦃ K : Kit ⦄ ⦃ CK : ComposeKit KT ⦃ K ⦄ ⦃ K ⦄ ⦃ K ⦄ ⦄ where
    dist-∘-∥ₛ : (ϕ : µ →ₛ µ') → (ϕ₁ : µ₁ →ₛ µ) → (ϕ₂ : µ₂ →ₛ µ)
        → ϕ ₛ∘ₛ (ϕ₁ ∥ₛ ϕ₂) ~ (ϕ ₛ∘ₛ ϕ₁) ∥ₛ (ϕ ₛ∘ₛ ϕ₂)
    dist-∘-∥ₛ {µ₁ = µ₁ ▷ x₁} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (here refl) = refl
    dist-∘-∥ₛ {µ₁ = µ₁ ▷ x₁} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (there x)   = dist-∘-∥ₛ ϕ (λ _ x → ϕ₁ _ (there x)) ϕ₂ _ x
    dist-∘-∥ₛ {µ₁ = µ₁} {µ₂ = µ₂ ▷ x₁} ϕ ϕ₁ ϕ₂ m (here refl) = refl
    dist-∘-∥ₛ {µ₁ = µ₁} {µ₂ = µ₂ ▷ x₁} ϕ ϕ₁ ϕ₂ m (there x)   = dist-∘-∥ₛ ϕ ϕ₁ (λ _ x → ϕ₂ _ (there x)) _ x

    dist-∘-∥ : (ϕ : µ –→ µ') → (ϕ₁ : µ₁ –→ µ) → (ϕ₂ : µ₂ –→ µ)
        → ϕ ∘ (ϕ₁ ∥ ϕ₂) ~ (ϕ ∘ ϕ₁) ∥ (ϕ ∘ ϕ₂)
    dist-∘-∥ ϕ ϕ₁ ϕ₂ m x = {!x!}
    -- dist-∘-∥ {µ₁ = .(_ ▷ m)} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (here refl) = refl
    -- dist-∘-∥ {µ₁ = .(_ ▷ _)} {µ₂ = []} ϕ ϕ₁ ϕ₂ m (there x) = {!dist-∘-∥ ϕ ϕ₁ ϕ₂ m x!}
    -- dist-∘-∥ {µ₁ = µ₁} {µ₂ = µ₂ ▷ x₁} ϕ ϕ₁ ϕ₂ m x = {!!}
