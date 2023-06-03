module Paper.Kits where

--! K >

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.Any public using (here; there)
open import Data.List.Relation.Unary.All as All public using (All; []; _∷_)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

--! Variables {
infix  4  _∋_

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set _
xs ∋ x = x ∈ xs

pattern Z = here refl
pattern S x = there x
--! }

--! ModeTy
data ModeTy : Set where
  Var NoVar : ModeTy

--! Terms
record Terms : Set₁ where
  field
    Mode         : ModeTy → Set
    _⊢_          : ∀ {t} → List (Mode Var) → Mode t → Set
    `_           : ∀ {µ} {m : Mode Var} → µ ∋ m → µ ⊢ m
    `-injective  : ∀ {µ m} {x₁ x₂ : µ ∋ m} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂

  Scoped : Set₁
  Scoped = List (Mode Var) → Mode Var → Set

  variable _∋/⊢_  _∋/⊢₁_ _∋/⊢₂_ : Scoped

  --! Kit {
  record Kit (_∋/⊢_ : Scoped) : Set where
    field
      id/`            : ∀ {µ m} → µ ∋ m → µ ∋/⊢ m
      `/id            : ∀ {µ m} → µ ∋/⊢ m → µ ⊢ m
      id/`/id         : ∀ {µ m} (x : µ ∋ m) → `/id (id/` x) ≡ ` x

      id/`-injective  : ∀  {µ m} {x₁ x₂ : µ ∋ m} →
                           id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
      `/id-injective  : ∀  {µ m} {x/t₁ x/t₂ : µ ∋/⊢ m} →
                           `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂

      wk              : ∀ {µ m} m' → µ ∋/⊢ m → (m' ∷ µ) ∋/⊢ m
      wk-id/`         : ∀  {µ m} m' (x : µ ∋ m) →
                           wk m' (id/` x) ≡ id/` (there x)
    --! }

    --! Map
    Map : (µ₁ µ₂ : List (Mode Var)) → Set
    Map µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢ m

    infixl  8  _&_
    --! Ap
    _&_ : ∀ {µ₁ µ₂ m} → µ₁ ∋ m → Map µ₁ µ₂ → µ₂ ∋/⊢ m
    x & f = f _ x 

    wkm : ∀ {µ₁ µ₂} m → Map µ₁ µ₂ → Map µ₁ (m ∷ µ₂)
    wkm m f _ x = wk m (f _ x)

    --! Ext
    _∷ₘ_ :
      ∀ {µ₁ µ₂ m} → µ₂ ∋/⊢ m → Map µ₁ µ₂ → Map (m ∷ µ₁) µ₂
    (x/t ∷ₘ f) _ Z     = x/t
    (x/t ∷ₘ f) _ (S x) = f _ x

    --! Lift
    _↑_ : ∀ {µ₁ µ₂} → Map µ₁ µ₂ → ∀ m → Map (m ∷ µ₁) (m ∷ µ₂)
    f ↑ m = id/` (here refl) ∷ₘ wkm m f
      
    --! Id
    id : ∀ {µ} → Map µ µ
    id m x = id/` x

    --! Single
    ⦅_⦆ : ∀ {µ m} → µ ∋/⊢ m → Map (m ∷ µ) µ
    ⦅ x/t ⦆ = x/t ∷ₘ id

    --! Weaken
    weaken : ∀ {µ} m → Map µ (m ∷ µ)
    weaken m = wkm m id

    --! Eq
    _~_ :
      ∀ {µ₁ µ₂}
      → (ϕ₁ ϕ₂ : Map µ₁ µ₂)
      → Set
    _~_ {µ₁ = µ₁} ϕ₁ ϕ₂ = ∀ m (x : µ₁ ∋ m) → ϕ₁ m x ≡ ϕ₂ m x

    --! FunExt
    postulate
      ~-ext : 
        ∀ {µ₁ µ₂} {ϕ₁ ϕ₂ : Map µ₁ µ₂}
        → ϕ₁ ~ ϕ₂
        → ϕ₁ ≡ ϕ₂

    --! IdLift
    id↑~id : ∀ {µ m} → (id ↑ m) ~ id {m ∷ µ}
    id↑~id m Z     = refl
    id↑~id m (S x) =
      (id ↑ _) m (S x) ≡⟨⟩
      wk _ (id/` x)    ≡⟨ wk-id/` _ x ⟩
      id/` (S x)       ≡⟨⟩
      id m (S x)       ∎

  --! KitNotation {
  _∋/⊢[_]_ : List (Mode Var) → Kit _∋/⊢_ → Mode Var → Set
  _∋/⊢[_]_ {_∋/⊢_} µ K m = µ ∋/⊢ m

  _–[_]→_ : List (Mode Var) → Kit _∋/⊢_ → List (Mode Var) → Set
  µ₁ –[ K ]→ µ₂ = Map µ₁ µ₂ where open Kit K

  open Kit ⦃ … ⦄ public
  --! }

  --! Traversal {
  record Traversal : Set₁ where
    infixl   5  _⋯_

    field
      _⋯_   :
        ∀ ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂ t} {m : Mode t} 
        → µ₁ ⊢ m → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ m

      ⋯-var :
        ∀ ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} {m : Mode Var} 
          (x : µ₁ ∋ m) (ϕ : µ₁ –[ K ]→ µ₂)
        → (` x) ⋯ ϕ ≡ `/id (x & ϕ)

      ⋯-id :
        ∀ ⦃ K : Kit _∋/⊢_ ⦄ {µ t} {m : Mode t} 
          (t : µ ⊢ m)
        → t ⋯ id ⦃ K ⦄ ≡ t

    --! }

    --! KitInstances {
    instance
      Kᵣ : Kit _∋_
      Kᵣ = record
        { id/`           = λ x → x
        ; `/id           = `_
        ; id/`/id        = λ x → refl
        ; id/`-injective = λ eq → eq
        ; `/id-injective = `-injective
        ; wk             = λ m' x → there x
        ; wk-id/`        = λ m' x → refl
        }

      Kₛ : Kit _⊢_
      Kₛ = record
        { id/`           = `_
        ; `/id           = λ t → t
        ; id/`/id        = λ x → refl
        ; id/`-injective = `-injective
        ; `/id-injective = λ eq → eq
        ; wk             = λ m' t → t ⋯ weaken m'
        ; wk-id/`        = λ m' x → (` x) ⋯ weaken m' ≡⟨ ⋯-var x (weaken m') ⟩
                                    ` (x & weaken m') ≡⟨⟩
                                    ` S x             ∎
        }
    --! }

    --! KitOpen
    open Kit Kᵣ public using () renaming 
      (Map to _→ᵣ_; wkm to wkmᵣ; _∷ₘ_ to _∷ᵣ_; _↑_ to _↑ᵣ_; id to idᵣ; ⦅_⦆ to ⦅_⦆ᵣ; weaken to weakenᵣ)
    open Kit Kₛ public using () renaming 
      (Map to _→ₛ_; wkm to wkmₛ; _∷ₘ_ to _∷ₛ_; _↑_ to _↑ₛ_; id to idₛ; ⦅_⦆ to ⦅_⦆ₛ; weaken to weakenₛ)

    -- Counterpart to wk-id/`
    --! WkKit {
    record WkKit (K : Kit _∋/⊢_): Set₁ where
      private instance _ = K
      field
        wk-`/id :
          ∀ m {µ m'} (x/t : µ ∋/⊢ m')
          → `/id x/t ⋯ weakenᵣ m ≡ `/id (wk m x/t)
    --! }

    --! WkKitInstances {
    instance
      Wᵣ : WkKit Kᵣ
      Wᵣ = record { wk-`/id = λ m x → ⋯-var x (weaken m) }

      Wₛ : WkKit Kₛ
      Wₛ = record { wk-`/id = λ m t → refl }

    open WkKit ⦃ … ⦄ public
    --! }

    --! ComposeKit {
    record ComposeKit (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) (K₁⊔K₂ : Kit _∋/⊢_) : Set where
      infixl  8  _&/⋯_

      private instance _ = K₁; _ = K₂; _ = K₁⊔K₂

      field
        _&/⋯_ :
          ∀ {µ₁} {µ₂} {m} → µ₁ ∋/⊢[ K₁ ] m → µ₁ –[ K₂ ]→ µ₂ → µ₂ ∋/⊢[ K₁⊔K₂ ] m

        &/⋯-⋯ :
          ∀ {µ₁} {µ₂} {m} (x/t : µ₁ ∋/⊢[ K₁ ] m) (ϕ : µ₁ –[ K₂ ]→ µ₂) 
          → `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ

        &/⋯-wk-↑ :
          ∀ {µ₁} {µ₂} {m'} {m} (x/t : µ₁ ∋/⊢[ K₁ ] m) (ϕ : µ₁ –[ K₂ ]→ µ₂)
          → wk m' (x/t &/⋯ ϕ) ≡ wk m' x/t &/⋯ (ϕ ↑ m')

      --! }

      --! Composition
      _·ₘ_ : ∀ {µ₁ µ₂ µ₃} → µ₁ –[ K₁ ]→ µ₂ → µ₂ –[ K₂ ]→ µ₃ → µ₁ –[ K₁⊔K₂ ]→ µ₃
      (ϕ₁ ·ₘ ϕ₂) _ x = x & ϕ₁ &/⋯ ϕ₂ 

      --! ComposeKitAp
      &/⋯-& :
        ∀ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (ϕ : µ₁ –[ K₂ ]→ µ₂) 
        → `/id (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (x & ϕ)
      &/⋯-& {µ₁} {µ₂} {m} x ϕ = 
          `/id (id/` x &/⋯ ϕ)      ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
          `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ ≡⟨ cong (_⋯ ϕ) (id/`/id ⦃ K₁ ⦄ x) ⟩
          ` x ⋯ ϕ                  ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
          `/id ⦃ K₂ ⦄  (x & ϕ)     ∎

      --! DistLiftCompose
      dist-↑-· :
        ∀ {µ₁} {µ₂} {µ₃} m
          (ϕ₁ : µ₁ –[ K₁ ]→ µ₂)
          (ϕ₂ : µ₂ –[ K₂ ]→ µ₃)
        → ((ϕ₁ ·ₘ ϕ₂) ↑ m) ~ ((ϕ₁ ↑ m) ·ₘ (ϕ₂ ↑ m))
      dist-↑-· m ϕ₁ ϕ₂ m₁ x@Z = `/id-injective (
        `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ·ₘ ϕ₂) ↑ m))       ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (id/` Z)                     ≡⟨ id/`/id ⦃ K₁⊔K₂ ⦄ Z ⟩
        ` Z                                         ≡⟨ sym (id/`/id ⦃ K₂ ⦄ Z) ⟩
        `/id ⦃ K₂ ⦄ (id/` Z)                        ≡⟨⟩
        `/id ⦃ K₂ ⦄ (Z & (ϕ₂ ↑ m))                  ≡⟨ sym (&/⋯-& (id/` Z) (ϕ₂ ↑ m)) ⟩
        `/id ⦃ K₁⊔K₂ ⦄ (id/` Z &/⋯ (ϕ₂ ↑ m))        ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m))  ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ↑ m) ·ₘ (ϕ₂ ↑ m))) ∎
        )
      dist-↑-· m ϕ₁ ϕ₂ m₁ x@(S y) = `/id-injective (
        `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ·ₘ ϕ₂) ↑ m))       ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk _ (y & (ϕ₁ ·ₘ ϕ₂)))      ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk _ (y & ϕ₁ &/⋯ ϕ₂))       ≡⟨ cong `/id (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ m)) ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (x & (ϕ₁ ↑ m) &/⋯ (ϕ₂ ↑ m))  ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ↑ m) ·ₘ (ϕ₂ ↑ m))) ∎
        )

    --! ComposeKitNotation {
    _·[_]_ :
      ∀ {K₁ : Kit _∋/⊢₁_} {K₂ : Kit _∋/⊢₂_} {K₁⊔K₂ : Kit _∋/⊢_} {µ₁ µ₂ µ₃}
      → µ₁ –[ K₁ ]→ µ₂ → ComposeKit K₁ K₂ K₁⊔K₂ → µ₂ –[ K₂ ]→ µ₃ → µ₁ –[ K₁⊔K₂ ]→ µ₃
    ϕ₁ ·[ C ] ϕ₂ = ϕ₁ ·ₘ ϕ₂ where open ComposeKit C

    open ComposeKit ⦃ … ⦄ public
    --! }

    --! ComposeTraversal {
    record ComposeTraversal : Set₁ where
      field
        ⋯-assoc :
          ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
            ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
            {µ₁ µ₂ µ₃ t} {m : Mode t}
            (t : µ₁ ⊢ m) (ϕ₁ : µ₁ –[ K₁ ]→ µ₂) (ϕ₂ : µ₂ –[ K₂ ]→ µ₃)
          → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₘ ϕ₂)
    --! }

      --! CommLiftWeaken
      ↑-wk :
        ∀  ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
           ⦃ C : ComposeKit K Kᵣ K ⦄ ⦃ C : ComposeKit Kᵣ K K ⦄ 
           {µ₁ µ₂} (ϕ : µ₁ –[ K ]→ µ₂) m
        → (ϕ ·ₘ weaken m) ~ (weaken m ·ₘ (ϕ ↑ m))
      ↑-wk {µ₁} {µ₂} ϕ m mx x = `/id-injective (
          `/id ((ϕ ·ₘ weakenᵣ m) mx x)       ≡⟨⟩
          `/id (x & ϕ &/⋯ weakenᵣ m)         ≡⟨ &/⋯-⋯ (x & ϕ) (weakenᵣ m) ⟩
          `/id (`/id (x & ϕ) ⋯ weakenᵣ m)    ≡⟨ wk-`/id m (x & ϕ) ⟩
          `/id (S x & (ϕ ↑ m))               ≡⟨ sym (&/⋯-& (S x) (ϕ ↑ m)) ⟩
          `/id (S x &/⋯ (ϕ ↑ m))             ≡⟨⟩
          `/id (x & weakenᵣ m &/⋯ (ϕ ↑ m))   ≡⟨⟩
          `/id ((weakenᵣ m ·ₘ (ϕ ↑ m)) mx x) ∎
        )

      --! CommLiftWeakenTraverse
      ⋯-↑-wk :
        ∀  ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
           ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit Kᵣ K K ⦄ 
           {µ₁ µ₂ mt} {m : Mode mt} (t : µ₁ ⊢ m) (ϕ : µ₁ –[ K ]→ µ₂) m
        → t ⋯ ϕ ⋯ weakenᵣ m ≡ t ⋯ weakenᵣ m ⋯ (ϕ ↑ m)
      ⋯-↑-wk t ϕ m =
        t ⋯ ϕ ⋯ weakenᵣ m          ≡⟨ ⋯-assoc t ϕ (weakenᵣ m) ⟩
        t ⋯ (ϕ ·ₘ weakenᵣ m)       ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ m)) ⟩
        t ⋯ (weakenᵣ m ·ₘ (ϕ ↑ m)) ≡⟨ sym (⋯-assoc t (weakenᵣ m) (ϕ ↑ m)) ⟩
        t ⋯ weakenᵣ m ⋯ (ϕ ↑ m)    ∎

      --! ComposeKitInstances {
      instance
        Cᵣ : ∀ ⦃ K₂ : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K₂ K₂
        Cᵣ = record
          { _&/⋯_ = _&_
          ; &/⋯-⋯ = λ x ϕ →
            `/id (x & ϕ) ≡⟨ sym (⋯-var x ϕ) ⟩
            (` x) ⋯ ϕ    ∎
          ; &/⋯-wk-↑ = λ x ϕ → refl
          }

        Cₛ : ∀ ⦃ K₂ : Kit _∋/⊢_ ⦄ ⦃ W₂ : WkKit K₂ ⦄ ⦃ C : ComposeKit K₂ Kᵣ K₂ ⦄
             → ComposeKit Kₛ K₂ Kₛ
        Cₛ ⦃ C = C ⦄ = record
          { _&/⋯_    = _⋯_
          ; &/⋯-⋯    = λ t ϕ → refl
          ; &/⋯-wk-↑ = λ t ϕ → ⋯-↑-wk t ϕ _
          }
      --! }

      --! ComposeKitInstancesConcrete
      Cᵣᵣ : ComposeKit Kᵣ Kᵣ Kᵣ
      Cᵣₛ : ComposeKit Kᵣ Kₛ Kₛ
      Cₛᵣ : ComposeKit Kₛ Kᵣ Kₛ
      Cₛₛ : ComposeKit Kₛ Kᵣ Kₛ
      Cᵣᵣ = Cᵣ
      Cᵣₛ = Cᵣ
      Cₛᵣ = Cₛ
      Cₛₛ = Cₛ

      --! WeakenCancelsSingle
      wk-cancels-⦅⦆ :
        ∀ ⦃ K : Kit _∋/⊢_ ⦄ {µ m} (x/t : µ ∋/⊢[ K ] m) 
        → (weakenᵣ m ·[ Cᵣ ] ⦅ x/t ⦆) ~ id
      wk-cancels-⦅⦆ ⦃ K ⦄ x/t mx x = `/id-injective (
          `/id ⦃ K ⦄ (x & (weakenᵣ _ ·[ Cᵣ ] ⦅ x/t ⦆)) ≡⟨⟩
          `/id ⦃ K ⦄ (id/` (S x) &/⋯ ⦅ x/t ⦆)          ≡⟨ &/⋯-& ⦃ Cᵣ ⦃ K ⦄ ⦄ (S x) ⦅ x/t ⦆ ⟩
          `/id ⦃ K ⦄ (id/` x)                          ≡⟨⟩
          `/id ⦃ K ⦄ (x & id)                          ∎
        )

      --! WeakenCancelsSingleTraverse
      wk-cancels-⦅⦆-⋯ :
        ∀ ⦃ K : Kit _∋/⊢_ ⦄ {µ m mt} {m' : Mode mt} (t : µ ⊢ m') (x/t : µ ∋/⊢[ K ] m) 
        → t ⋯ weakenᵣ m ⋯ ⦅ x/t ⦆ ≡ t
      wk-cancels-⦅⦆-⋯ t x/t =
        t ⋯ weakenᵣ _ ⋯ ⦅ x/t ⦆    ≡⟨ ⋯-assoc t (weakenᵣ _) ⦅ x/t ⦆ ⟩
        t ⋯ (weakenᵣ _ ·ₘ ⦅ x/t ⦆) ≡⟨ cong (t ⋯_) (~-ext (wk-cancels-⦅⦆ x/t)) ⟩
        t ⋯ id                     ≡⟨ ⋯-id t ⟩
        t                          ∎

      --! DistLiftSingle
      dist-↑-⦅⦆ :
        ∀  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
           ⦃ W₂ : WkKit K₂ ⦄ ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
           {µ₁ µ₂ m} (x/t : µ₁ ∋/⊢[ K₁ ] m) (ϕ : µ₁ –[ K₂ ]→ µ₂) →
        (⦅ x/t ⦆ ·[ C₁ ] ϕ) ~ ((ϕ ↑ m) ·[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆)
      dist-↑-⦅⦆ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@Z = `/id-injective (
          `/id ⦃ K ⦄ (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))               ≡⟨⟩
          `/id ⦃ K ⦄ (x/t &/⋯ ϕ)                             ≡⟨⟩
          `/id ⦃ K ⦄ (Z & ⦅ (x/t &/⋯ ϕ) ⦆)                   ≡⟨ sym (&/⋯-& ⦃ C₂ ⦄ Z ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
          `/id ⦃ K ⦄ (id/` ⦃ K₂ ⦄ Z &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)     ≡⟨⟩
          `/id ⦃ K ⦄ (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆)) ∎
        )
      dist-↑-⦅⦆ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ {µ₁} {µ₂} {m} x/t ϕ mx x@(S y) = `/id-injective (
          `/id (x & (⦅ x/t ⦆ ·[ C₁ ] ϕ))               ≡⟨⟩
          `/id (id/` ⦃ K₁ ⦄ y &/⋯ ϕ)                   ≡⟨ &/⋯-& ⦃ C₁ ⦄ y ϕ ⟩
          `/id (y & ϕ)                                 ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y & ϕ)) (x/t &/⋯ ϕ)) ⟩
          `/id (y & ϕ) ⋯ weakenᵣ m ⋯ ⦅ (x/t &/⋯ ϕ) ⦆   ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆) (wk-`/id m (y & ϕ)) ⟩
          `/id (wk m (y & ϕ)) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆        ≡⟨ sym (&/⋯-⋯ (wk m (y & ϕ)) ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
          `/id (wk m (y & ϕ) &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)      ≡⟨⟩
          `/id (x & ((ϕ ↑ m) ·[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆)) ∎
        )

      --! DistLiftSingleTraverse
      dist-↑-⦅⦆-⋯ :
        ∀  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
           ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₂ : WkKit K₂ ⦄ ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
           {µ₁ µ₂ m mt} {m' : Mode mt} (t : (m ∷ µ₁) ⊢ m')
           (x/t : µ₁ ∋/⊢[ K₁ ] m) (ϕ : µ₁ –[ K₂ ]→ µ₂) →
        t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ m) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆
      dist-↑-⦅⦆-⋯ t x/t ϕ =
        t ⋯ ⦅ x/t ⦆ ⋯ ϕ                  ≡⟨ ⋯-assoc t ⦅ x/t ⦆ ϕ ⟩
        t ⋯ (⦅ x/t ⦆ ·ₘ ϕ)               ≡⟨ cong (t ⋯_) (~-ext (dist-↑-⦅⦆ x/t ϕ)) ⟩
        t ⋯ ((ϕ ↑ _) ·ₘ ⦅ (x/t &/⋯ ϕ) ⦆) ≡⟨ sym (⋯-assoc t (ϕ ↑ _) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
        t ⋯ (ϕ ↑ _) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆    ∎

      --! TypeModes
      record Types : Set₁ where
        field
          ↑ᵗ : ∀ {t} → Mode t → ∃[ t ] Mode t

        --! Types
        _∶⊢_ : ∀ {t} → List (Mode Var) → Mode t → Set
        µ ∶⊢ m = µ ⊢ proj₂ (↑ᵗ m)

        --! ContextHelper {
        depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
        depth (here px) = zero
        depth (there x) = suc (depth x)

        -- We need to drop one extra using `suc`, because otherwise the types in a
        -- context are allowed to use themselves.
        drop-∈ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
        drop-∈ e xs = drop (suc (depth e)) xs
        --! }

        --! Contexts {
        Ctx : List (Mode Var) → Set
        Ctx µ = ∀ m → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m

        -- []ₜ : Ctx []
        -- []ₜ _ ()

        _∷ₜ_ : ∀ {µ m} → µ ∶⊢ m → Ctx µ → Ctx (m ∷ µ)
        (t ∷ₜ Γ) _ (here refl) = t
        (t ∷ₜ Γ) _ (there x)   = Γ _ x
        --! }

        --! ContextLookup {
        wk-drop-∈ : ∀ {µ m t} {m' : Mode t} → (x : µ ∋ m) → drop-∈ x µ ⊢ m' → µ ⊢ m'
        wk-drop-∈ (here _)  t = t ⋯ weakenᵣ _
        wk-drop-∈ (there x) t = wk-drop-∈ x t ⋯ weakenᵣ _

        wk-telescope : ∀ {µ m} → Ctx µ → µ ∋ m → µ ∶⊢ m
        wk-telescope Γ x = wk-drop-∈ x (Γ _ x)
        --! }

        --! VariableTyping
        infix   4  _∋_∶_
        _∋_∶_ : ∀ {µ m} → Ctx µ → µ ∋ m → µ ∶⊢ m → Set
        Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

        --! Typing {
        record Typing : Set₁ where
          infix   4  _⊢_∶_
          field
            _⊢_∶_ : ∀ {µ t} {m : Mode t} → Ctx µ → µ ⊢ m → µ ∶⊢ m → Set

            ⊢` : ∀ {µ m} {Γ : Ctx µ} {x : µ ∋ m} {t} →
                Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t
        --! }

          --! TypingKit {
          record TypingKit (K : Kit _∋/⊢_) (W : WkKit K) (C₁ : ComposeKit K Kᵣ K) (C₂ : ComposeKit K K K) : Set₁ where
            infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
            infixl  6  _∋↑/⊢↑_

            private instance _ = K; _ = W; _ = C₁; _ = C₂

            field
              -- Variable/Term Typing
              _∋/⊢_∶_ : ∀ {µ m} → Ctx µ → µ ∋/⊢ m → µ ∶⊢ m → Set

              ∋/⊢∶-lookup : ∀ {µ} {Γ : Ctx µ} {m} (x : µ ∋ m)
                            → Γ ∋/⊢ id/` x ∶ wk-telescope Γ x

              -- Conditional Applications of Variable-Typing-Rule
              id/⊢` : ∀ {µ m} {x : µ ∋ m} {t : µ ∶⊢ m} {Γ : Ctx µ}
                      → Γ ∋ x ∶ t
                      →  Γ ∋/⊢ id/` x ∶ t
              ⊢`/id : ∀ {µ m} {e : µ ∋/⊢ m} {t : µ ∶⊢ m} {Γ : Ctx µ}
                      → Γ ∋/⊢ e ∶ t
                      → Γ ⊢ `/id e ∶ t

              -- Weakening preserveres variable/term typings.
              ∋wk/⊢wk  : ∀ {µ m m'} (Γ : Ctx µ) (t' : µ ∶⊢ m) (e : µ ∋/⊢ m') (t : µ ∶⊢ m')
                        → Γ ∋/⊢ e ∶ t
                        → (t' ∷ₜ Γ) ∋/⊢ wk _ e ∶ (t ⋯ weakenᵣ _)
          --! }

            --! MapTyping
            _∋*/⊢*_∶_ : ∀ {µ₁ µ₂} → Ctx µ₂ → µ₁ –[ K ]→ µ₂ → Ctx µ₁ → Set
            _∋*/⊢*_∶_ {µ₁} {µ₂} Γ₂ ϕ Γ₁ =
              ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ∶⊢ m₁) (⊢x : Γ₁ ∋ x ∶ t)
              → Γ₂ ∋/⊢ (x & ϕ) ∶ (t ⋯ ϕ)

            --! LiftTyping
            _∋↑/⊢↑_ : ∀ {µ₁} {µ₂} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {ϕ : µ₁ –[ K ]→ µ₂} {m} →
              Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
              (t : µ₁ ∶⊢ m) →
              ((t ⋯ ϕ) ∷ₜ Γ₂) ∋*/⊢* (ϕ ↑ m) ∶ (t ∷ₜ Γ₁)
            _∋↑/⊢↑_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {m} ⊢ϕ t {mx} x@Z _ refl =
              subst (((t ⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (K Kit.& Z) (ϕ ↑ m) ∶_)
                    (t ⋯ ϕ ⋯ weakenᵣ m                  ≡⟨ ⋯-↑-wk t ϕ m ⟩
                     t ⋯ weakenᵣ m ⋯ (ϕ ↑ m)            ≡⟨⟩
                     wk-telescope (t ∷ₜ Γ₁) Z ⋯ (ϕ ↑ m) ∎)
                    (id/⊢` {x = here refl} {Γ = (t ⋯ ϕ) ∷ₜ Γ₂} refl)
            _∋↑/⊢↑_ {µ₁} {µ₂} {Γ₁} {Γ₂} {ϕ} {m} ⊢ϕ t {mx} x@(S y) _ refl =
              subst (((t ⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (K Kit.& S y) (ϕ ↑ m) ∶_)
                    (wk-telescope Γ₁ y ⋯ ϕ ⋯ weakenᵣ m       ≡⟨ ⋯-↑-wk _ ϕ m ⟩
                     wk-telescope Γ₁ y ⋯ weakenᵣ m ⋯ (ϕ ↑ m) ≡⟨⟩
                     wk-telescope (t ∷ₜ Γ₁) (S y) ⋯ (ϕ ↑ m)  ∎)
                    (∋wk/⊢wk _ _ _ _ (⊢ϕ y _ refl))

            --! SingleTyping
            ⊢⦅_⦆ : ∀ {m µ} {Γ : Ctx µ} {t : µ ∋/⊢ m} {T : µ ∶⊢ m}
              → Γ ∋/⊢ t ∶ T 
              → Γ ∋*/⊢* ⦅ t ⦆ ∶ (T ∷ₜ Γ)
            ⊢⦅_⦆ {m} {µ} {Γ} {t} {T} ⊢x/t x@Z _ refl =
              subst (Γ ∋/⊢ t ∶_)
                    (T                               ≡⟨ sym (wk-cancels-⦅⦆-⋯ T t) ⟩
                     T ⋯ weakenᵣ _ ⋯ ⦅ t ⦆           ≡⟨⟩
                     wk-telescope (T ∷ₜ Γ) Z ⋯ ⦅ t ⦆ ∎)
                    ⊢x/t
            ⊢⦅_⦆ {m} {µ} {Γ} {t} {T} ⊢x/t x@(S y) _ refl =
              subst (Γ ∋/⊢ id/` y ∶_)
                    (wk-telescope Γ y                     ≡⟨ sym (wk-cancels-⦅⦆-⋯ _ t) ⟩
                     wk-telescope Γ y ⋯ weakenᵣ _ ⋯ ⦅ t ⦆ ≡⟨⟩
                     wk-telescope (T ∷ₜ Γ) (S y) ⋯ ⦅ t ⦆  ∎)
                    (id/⊢` refl)

          --! TypingNotation {
          open TypingKit ⦃ … ⦄ public

          infixl  5  _∋*/⊢*[_]_∶_
          _∋*/⊢*[_]_∶_ :
            ∀ {K : Kit _∋/⊢_} {W : WkKit K}
              {C₁ : ComposeKit K Kᵣ K} {C₂ : ComposeKit K K K}
              {µ₁ µ₂}
            → Ctx µ₂ → TypingKit K W C₁ C₂ → µ₁ –[ K ]→ µ₂ → Ctx µ₁ → Set
          Γ₂ ∋*/⊢*[ TK ] f ∶ Γ₁ = Γ₂ ∋*/⊢* f ∶ Γ₁ where instance _ = TK
          --! }

          --! TypingTraversal {
          record TypingTraversal : Set₁ where
            infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_

            field
              _⊢⋯_ :
                ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
                  ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
                  ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
                  ⦃ TK : TypingKit K W C₁ C₂ ⦄
                  {µ₁ µ₂ mt} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {m : Mode mt}
                  {e : µ₁ ⊢ m} {t : µ₁ ∶⊢ m} {ϕ : µ₁ –[ K ]→ µ₂} →
                Γ₁ ⊢ e ∶ t →
                Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
                Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
          --! }

            --! TypingInstances {
            instance
              TKᵣ : TypingKit Kᵣ Wᵣ Cᵣ Cᵣ
              TKᵣ = record
                { _∋/⊢_∶_     = _∋_∶_
                ; ∋/⊢∶-lookup = λ x → refl
                ; id/⊢`       = λ ⊢x → ⊢x
                ; ⊢`/id       = ⊢`
                ; ∋wk/⊢wk     = λ { Γ t' x t refl → refl }
                }

              TKₛ : TypingKit Kₛ Wₛ Cₛ Cₛ
              TKₛ = record
                { _∋/⊢_∶_     = _⊢_∶_
                ; ∋/⊢∶-lookup = λ x → ⊢` refl
                ; id/⊢`       = ⊢`
                ; ⊢`/id       = λ ⊢x → ⊢x
                ; ∋wk/⊢wk     = λ Γ t' e t ⊢e → ⊢e ⊢⋯ ∋wk/⊢wk Γ t'
                }
            --! }

            --! TypingTraversalNotation {
            open TypingKit TKᵣ public using () renaming (∋wk/⊢wk to ⊢wk; _∋*/⊢*_∶_ to _∋*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
            open TypingKit TKₛ public using () renaming (∋wk/⊢wk to ∋wk; _∋*/⊢*_∶_ to _⊢*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

            -- Renaming preserves typing

            _⊢⋯ᵣ_ : ∀ {µ₁ µ₂ mt} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {m : Mode mt}
                      {e : µ₁ ⊢ m} {t : µ₁ ∶⊢ m} {ρ : µ₁ →ᵣ µ₂} →
                    Γ₁ ⊢ e ∶ t →
                    Γ₂ ∋* ρ ∶ Γ₁ →
                    Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
            _⊢⋯ᵣ_ = _⊢⋯_

            -- Substitution preserves typing

            _⊢⋯ₛ_ : ∀ {µ₁ µ₂ mt} {Γ₁ : Ctx µ₁} {Γ₂ : Ctx µ₂} {m : Mode mt}
                      {e : µ₁ ⊢ m} {t : µ₁ ∶⊢ m} {σ : µ₁ →ₛ µ₂} →
                    Γ₁ ⊢ e ∶ t →
                    Γ₂ ⊢* σ ∶ Γ₁ →
                    Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
            _⊢⋯ₛ_ = _⊢⋯_
            --! }
