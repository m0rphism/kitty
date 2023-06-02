module Kitty.Examples.SystemF-Paper.Kits where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.Any public using (here; there)
open import Data.List.Relation.Unary.All as All public using (All; []; _∷_)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

infix  4  _∋_

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set _
xs ∋ x = x ∈ xs

pattern Z = here refl
pattern S x = there x

data ModeTy : Set where
  Var Term : ModeTy

record Terms : Set₁ where
  field
    Mode        : ModeTy → Set
    _⊢_         : ∀ {t} → List (Mode Var) → Mode t → Set
    `_          : ∀ {µ} {m : Mode Var} → µ ∋ m → µ ⊢ m
    `-injective : ∀ {µ m} {x₁ x₂ : µ ∋ m} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂

  Scoped : Set₁
  Scoped = List (Mode Var) → Mode Var → Set

  variable _∋/⊢_ _∋/⊢₁_  _∋/⊢₂_ : Scoped

  record Kit (_∋/⊢_ : List (Mode Var) → Mode Var → Set) : Set where
    field
      id/`            : ∀ {µ m} → µ ∋ m → µ ∋/⊢ m
      `/id            : ∀ {µ m} → µ ∋/⊢ m → µ ⊢ m
      id/`/id         : ∀ {µ m} (x : µ ∋ m) → `/id (id/` x) ≡ ` x

      id/`-injective  : ∀ {µ m} {x₁ x₂ : µ ∋ m} → id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
      `/id-injective  : ∀ {µ m} {x/t₁ x/t₂ : µ ∋/⊢ m} → `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂

      wk              : ∀ {µ m} m' → µ ∋/⊢ m → (m' ∷ µ) ∋/⊢ m
      wk-id/`         : ∀ {µ m} m' (x : µ ∋ m) → wk m' (id/` x) ≡ id/` (there x)

    Map : (µ₁ µ₂ : List (Mode Var)) → Set
    Map µ₁ µ₂ = ∀ m → µ₁ ∋ m → µ₂ ∋/⊢ m

    infixl  8  _&_
    _&_ : ∀ {µ₁ µ₂ m} → µ₁ ∋ m → Map µ₁ µ₂ → µ₂ ∋/⊢ m
    x & f = f _ x 

    wkm : ∀ {µ₁ µ₂} m → Map µ₁ µ₂ → Map µ₁ (m ∷ µ₂)
    wkm m f _ x = wk m (f _ x)

    _∷ₘ_ : ∀ {µ₁ µ₂ m} → µ₂ ∋/⊢ m → Map µ₁ µ₂ → Map (m ∷ µ₁) µ₂
    (x/t ∷ₘ f) _ Z     = x/t
    (x/t ∷ₘ f) _ (S x) = f _ x

    _↑_ : ∀ {µ₁ µ₂} → Map µ₁ µ₂ → ∀ m → Map (m ∷ µ₁) (m ∷ µ₂)
    f ↑ m = id/` (here refl) ∷ₘ wkm m f
      
    id : ∀ {µ} → Map µ µ
    id m x = id/` x

    weaken : ∀ {µ} m → Map µ (m ∷ µ)
    weaken m = wkm m id

  _∋/⊢[_]_ : ∀ {_∋/⊢_ : Scoped} → List (Mode Var) → Kit _∋/⊢_ → Mode Var → Set
  _∋/⊢[_]_ {_∋/⊢_} µ K m = µ ∋/⊢ m

  _–[_]→_ : ∀ {_∋/⊢_ : Scoped} → List (Mode Var) → Kit _∋/⊢_ → List (Mode Var) → Set
  µ₁ –[ K ]→ µ₂ = Map µ₁ µ₂ where open Kit K

  open Kit ⦃ … ⦄ public

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

  record Traversal : Set₁ where
    infixl   5  _⋯_

    field
      _⋯_   :
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂ t} {m : Mode t} 
        → µ₁ ⊢ m → µ₁ –[ K ]→ µ₂ → µ₂ ⊢ m

      ⋯-var :
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} {m : Mode Var} 
          (x : µ₁ ∋ m) (ϕ : µ₁ –[ K ]→ µ₂)
        → (` x) ⋯ ϕ ≡ `/id (x & ϕ)

      ⋯-id :
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ t} {m : Mode t} 
          (t : µ ⊢ m)
        → t ⋯ id ⦃ K ⦄ ≡ t

    instance _ = Kᵣ

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

    instance _ = Kₛ

    _~_ :
      ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂}
      → (ϕ₁ ϕ₂ : µ₁ –[ K ]→ µ₂)
      → Set
    _~_ {µ₁ = µ₁} ϕ₁ ϕ₂ = ∀ m (x : µ₁ ∋ m) → ϕ₁ m x ≡ ϕ₂ m x

    postulate
      -- ~-cong-⋯ : 
      --   ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} {ϕ₁ ϕ₂ : µ₁ –[ K ]→ µ₂}
      --   → ϕ₁ ~ ϕ₂
      --   → t ⋯ ϕ₁ ≡ t ⋯ ϕ₂
      ~-ext : 
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ {µ₁ µ₂} {ϕ₁ ϕ₂ : µ₁ –[ K ]→ µ₂}
        → ϕ₁ ~ ϕ₂
        → ϕ₁ ≡ ϕ₂

    -- Counterpart to wk-id/`
    record WkKit {_∋/⊢_ : Scoped} (K : Kit _∋/⊢_): Set₁ where
      private instance _ = K
      field
        wk-`/id :
          ∀ m {µ m'} (x/t : µ ∋/⊢ m')
          → `/id x/t ⋯ weaken ⦃ Kᵣ ⦄ m ≡ `/id (wk m x/t)

    instance
      Wᵣ : WkKit Kᵣ
      Wᵣ = record { wk-`/id = λ m x → ⋯-var x (weaken m) }

      Wₛ : WkKit Kₛ
      Wₛ = record { wk-`/id = λ m t → refl }

    open WkKit ⦃ … ⦄ public

    record ComposeKit {_∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : Scoped} (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) (K₁⊔K₂ : Kit _∋/⊢_) : Set where
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

      _·ₘ_ : ∀ {µ₁ µ₂ µ₃} → µ₁ –[ K₁ ]→ µ₂ → µ₂ –[ K₂ ]→ µ₃ → µ₁ –[ K₁⊔K₂ ]→ µ₃
      (ϕ₁ ·ₘ ϕ₂) _ x = x & ϕ₁ &/⋯ ϕ₂ 

    _·[_]_ :
      ∀ {_∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : Scoped} {K₁ : Kit _∋/⊢₁_} {K₂ : Kit _∋/⊢₂_} {K₁⊔K₂ : Kit _∋/⊢_} {µ₁ µ₂ µ₃}
      → µ₁ –[ K₁ ]→ µ₂ → ComposeKit K₁ K₂ K₁⊔K₂ → µ₂ –[ K₂ ]→ µ₃ → µ₁ –[ K₁⊔K₂ ]→ µ₃
    ϕ₁ ·[ C ] ϕ₂ = ϕ₁ ·ₘ ϕ₂ where open ComposeKit C

    open ComposeKit ⦃ … ⦄ public

    -- TODO: Why is this Set₁?
    record ComposeTraversal : Set₁ where
      field
        ⋯-assoc :
          ∀ {_∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ : Scoped}
            ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
            ⦃ W₁ : WkKit K₁ ⦄
            ⦃ C : ComposeKit K₁ K₂ K ⦄
            {µ₁ µ₂ µ₃ t} {m : Mode t}
            (t : µ₁ ⊢ m) (ϕ₁ : µ₁ –[ K₁ ]→ µ₂) (ϕ₂ : µ₂ –[ K₂ ]→ µ₃)
          → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₘ ϕ₂)

      ↑-wk :
        ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ C : ComposeKit K Kᵣ K ⦄ 
          {µ₁ µ₂} (ϕ : µ₁ –[ K ]→ µ₂) m
        → (ϕ ·ₘ weaken m) ~ (λ _ x → (x & weaken m) & (ϕ ↑ m))
      ↑-wk {µ₁} {µ₂} ϕ m mx x =
          (ϕ ·ₘ weaken m) mx x   ≡⟨⟩
          x & ϕ &/⋯ weaken m     ≡⟨ `/id-injective (
            `/id (x & ϕ &/⋯ weaken m)     ≡⟨ &/⋯-⋯ (x & ϕ) (weaken m) ⟩
            `/id (x & ϕ) ⋯ weaken m       ≡⟨ wk-`/id m (x & ϕ) ⟩
            `/id (wk m (x & ϕ))           ∎
            )
          ⟩
          wk m (x & ϕ)           ≡⟨⟩
          x & weaken m & (ϕ ↑ m) ∎

      instance
        Cᵣ : ∀ {_∋/⊢_ : Scoped} ⦃ K₂ : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K₂ K₂
        Cᵣ = record
          { _&/⋯_ = _&_
          ; &/⋯-⋯ = λ x ϕ →
            `/id (x & ϕ) ≡⟨ sym (⋯-var x ϕ) ⟩
            (` x) ⋯ ϕ    ∎
          ; &/⋯-wk-↑ = λ x ϕ →
            wk _ (x & ϕ)  ≡⟨⟩
            S x & (ϕ ↑ _) ∎
          }

        Cₛ : ∀ {_∋/⊢_ : Scoped} ⦃ K₂ : Kit _∋/⊢_ ⦄ ⦃ W₂ : WkKit K₂ ⦄ ⦃ C : ComposeKit K₂ Kᵣ K₂ ⦄ → ComposeKit Kₛ K₂ Kₛ
        Cₛ ⦃ C = C ⦄ = record
          { _&/⋯_    = _⋯_
          ; &/⋯-⋯    = λ t ϕ → refl
          ; &/⋯-wk-↑ = λ t ϕ →
            wk _ (t ⋯ ϕ)                   ≡⟨⟩
            t ⋯ ϕ ⋯ weaken _               ≡⟨ ⋯-assoc t ϕ (weaken _) ⟩
            t ⋯ (ϕ ·[ C ] weaken _)        ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ _)) ⟩
            t ⋯ (weaken _ ·[ Cᵣ ] (ϕ ↑ _)) ≡⟨ sym (⋯-assoc t (weaken _) (ϕ ↑ _)) ⟩
            t ⋯ weaken _ ⋯ (ϕ ↑ _)         ≡⟨⟩
            wk _ t ⋯ (ϕ ↑ _)               ∎
          }

      Cᵣᵣ : ComposeKit Kᵣ Kᵣ Kᵣ
      Cᵣᵣ = Cᵣ

      Cᵣₛ : ComposeKit Kᵣ Kₛ Kₛ
      Cᵣₛ = Cᵣ

      Cₛᵣ : ComposeKit Kₛ Kᵣ Kₛ
      Cₛᵣ = Cₛ

      Cₛₛ : ComposeKit Kₛ Kᵣ Kₛ
      Cₛₛ = Cₛ

      record Types : Set₁ where
        field
          ↑ᵗ : ∀ {t} → Mode t → ∃[ t ] Mode t

        _∶⊢_ : ∀ {t} → List (Mode Var) → Mode t → Set
        µ ∶⊢ m = µ ⊢ proj₂ (↑ᵗ m)

        depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
        depth (here px) = zero
        depth (there x) = suc (depth x)

        -- We need to drop one extra using `suc`, because otherwise the types in a
        -- context are allowed to use themselves.
        drop-∈ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → List A → List A
        drop-∈ e xs = drop (suc (depth e)) xs

        Ctx : List (Mode Var) → Set
        Ctx µ = ∀ m → (x : µ ∋ m) → drop-∈ x µ ∶⊢ m

        -- []ₜ : Ctx []
        -- []ₜ _ ()

        _∷ₜ_ : ∀ {µ m} → µ ∶⊢ m → Ctx µ → Ctx (m ∷ µ)
        (t ∷ₜ Γ) _ (here refl) = t
        (t ∷ₜ Γ) _ (there x)   = Γ _ x

        wk-drop-∈ : ∀ {µ m t} {m' : Mode t} → (x : µ ∋ m) → drop-∈ x µ ⊢ m' → µ ⊢ m'
        wk-drop-∈ (here _)  t = t ⋯ weaken ⦃ Kᵣ ⦄ _
        wk-drop-∈ (there x) t = wk-drop-∈ x t ⋯ weaken ⦃ Kᵣ ⦄ _

        -- Our context is defined as a telescope.
        -- This function automatically weakens all the types in a `Ctx µ` such that they
        -- refer to `µ` instead of a `µ`-suffix.
        wk-telescope : ∀ {µ m} → Ctx µ → µ ∋ m → µ ∶⊢ m
        wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

        infix   4  _∋_∶_
        _∋_∶_ : ∀ {µ m} → Ctx µ → µ ∋ m → µ ∶⊢ m → Set
        Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

        record Typing : Set₁ where
          infix   4  _⊢_∶_
          field
            _⊢_∶_ : ∀ {µ t} {m : Mode t} → Ctx µ → µ ⊢ m → µ ∶⊢ m → Set

            ⊢` : ∀ {µ m} {Γ : Ctx µ} {x : µ ∋ m} {t} →
                Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

            -- ≡ᶜ-cong-⊢ : ∀ {µ m} {Γ₁ Γ₂ : Ctx µ} {e : µ ⊢ m} {t : µ ⊢ ↑ᵗ m} → 
            --   Γ₁ ≡ᶜ Γ₂ →
            --   Γ₁ ⊢ e ∶ t →
            --   Γ₂ ⊢ e ∶ t

          -- _⊢*_∶_ : ∀ {µ₁ µ₂} → Ctx µ₂ → µ₁ –[ Kₛ ]→ µ₂ → Ctx µ₁ → Set
          -- _⊢*_∶_ {µ₁} {µ₂} Γ₂ ϕ Γ₁ =
          --   ∀ {m₁} (x : µ₁ ∋ m₁) (t : µ₁ ⊢ ↑ᵗ m₁) (⊢x : Γ₁ ∋ x ∶ t)
          --   → Γ₂ ⊢ (x & ϕ) ∶ t ⋯ ϕ

          record TypingKit {_∋/⊢_ : Scoped} (K : Kit _∋/⊢_) (W : WkKit K) (C₁ : ComposeKit K Kᵣ K) (C₂ : ComposeKit K K K) : Set₁ where
            -- infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
            -- infixl  6  _∋↑/⊢↑_

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
                        → (t' ∷ₜ Γ) ∋/⊢ wk _ e ∶ (t ⋯ weaken ⦃ Kᵣ ⦄ _)

          open TypingKit ⦃ … ⦄ public
