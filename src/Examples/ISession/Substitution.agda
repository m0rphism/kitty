module Examples.ISession.Substitution where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import KitTheory.Prelude using (_∋_; _▷_) public
open import KitTheory.Modes using (Modes; Terms)
open import Examples.ISession.Definitions

-- Application of Renamings and Substitutions ----------------------------------

open import KitTheory.Kit 𝕋
open Kit {{...}} public

mutual

  infixl  5  _⋯_

  -- Traverse a term with a renaming or substitution (depending on the kit).
  _⋯_ : ∀ {{𝕂 : Kit}} → Term µ₁ M → µ₁ –[ 𝕂 ]→ µ₂ → Term µ₂ M
  ⟨ t ⟩ ⋯ f                  = ⟨ t ⋯ f ⟩
  (t₁ ∥ t₂) ⋯ f              = (t₁ ⋯ f) ∥ (t₂ ⋯ f)
  (ν[α,x]→ t) ⋯ f            = ν[α,x]→ (t ⋯ (f ↑* _))
  ⟨ t ⟩ᵥ ⋯ f                 = ⟨ t ⋯ f ⟩ᵥ
  (let[x= t₁ ]in t₂) ⋯ f     = let[x= t₁ ⋯ f ]in (t₂ ⋯ (f ↑* _))
  fork t ⋯ f                 = fork (t ⋯ f)
  (t₁ · t₂) ⋯ f              = (t₁ ⋯ f) · (t₂ ⋯ f)
  (send t₁ on t₂) ⋯ f        = send (t₁ ⋯ f) on (t₂ ⋯ f)
  recv t ⋯ f                 = recv (t ⋯ f)
  (select l on t) ⋯ f        = select l on (t ⋯ f)
  case t of[ t₁ , t₂ ] ⋯ f   = case (t ⋯ f) of[ (t₁ ⋯ f) , (t₂ ⋯ f) ]
  close t ⋯ f                = close (t ⋯ f)
  π l t ⋯ f                  = π l (t ⋯ f)
  (t₁ ∙ t₂) ⋯ f              = (t₁ ⋯ f) ∙ (t₂ ⋯ f)
  (`ᵛ x) ⋯ f                 = tm _ (f _ x)
  (λx→ t) ⋯ f                = λx→ (t ⋯ (f ↑ _))
  (Λα→ t) ⋯ f                = Λα→ (t ⋯ (f ↑* _))
  unit ⋯ f                   = unit
  (t₁ ,ᵉ t₂) ⋯ f             = (t₁ ⋯ f) ,ᵉ (t₂ ⋯ f)
  Type ⋯ f                   = Type
  Session ⋯ f                = Session
  State ⋯ f                  = State
  Shape ⋯ f                  = Shape
  Cstr ⋯ f                   = Cstr
  Dom t ⋯ f                  = Dom (t ⋯ f)
  (t₁ ⇒ t₂) ⋯ f              = (t₁ ⋯ f) ⇒ (t₂ ⋯ f)
  Kind ⋯ f                   = Kind
  (`ᵗ x) ⋯ f                 = tm _ (f _ x)
  (t₁ ·ᵗ t₂) ⋯ f             = (t₁ ⋯ f) ·ᵗ (t₂ ⋯ f)
  (λα→ t) ⋯ f                = λα→ (t ⋯ (f ↑ _))
  (∀α[ ℂ ]→ t) ⋯ f           = ∀α[ ℂ ⋯ (f ↑ _) ]→ (t ⋯ (f ↑* _))
  ⟨ Σ₁ ; t₁ –→∃ Γ ; Σ₂ ; t₂ ⟩ ⋯ f = ⟨ (Σ₁ ⋯ f) ; (t₁ ⋯ f) –→∃ (Γ ⋯Ctx'' f) ; (Σ₂ ⋯ (f ↑* _)) ; (t₂ ⋯ (f ↑* _)) ⟩
  Chan t ⋯ f                 = Chan (t ⋯ f)
  Unit ⋯ f                   = Unit
  (t₁ × t₂) ⋯ f              = (t₁ ⋯ f) × (t₂ ⋯ f)
  (![∃α→ Σ₁ ; t₁ ] t) ⋯ f    = ![∃α→ (Σ₁ ⋯ (f ↑ _)) ; (t₁ ⋯ (f ↑ _)) ] (t ⋯ f)
  (?[∃α→ Σ₁ ; t₁ ] t) ⋯ f    = ?[∃α→ (Σ₁ ⋯ (f ↑ _)) ; (t₁ ⋯ (f ↑ _)) ] (t ⋯ f)
  (t₁ ⊕ t₂) ⋯ f              = (t₁ ⋯ f) ⊕ (t₂ ⋯ f)
  (t₁ & t₂) ⋯ f              = (t₁ ⋯ f) & (t₂ ⋯ f)
  End ⋯ f                    = End
  Dual t ⋯ f                 = Dual (t ⋯ f)
  [1] ⋯ f                    = [1]
  (t₁ + t₂) ⋯ f              = (t₁ ⋯ f) + (t₂ ⋯ f)
  (t₁ ,ᵈ t₂) ⋯ f             = (t₁ ⋯ f) ,ᵈ (t₂ ⋯ f)
  πᵈ l t ⋯ f                 = πᵈ l (t ⋯ f)
  [] ⋯ f                     = []
  (t₁ ∶ t₂) ⋯ f              = (t₁ ⋯ f) ∶ (t₂ ⋯ f)
  (t₁ ∶♯ t₂) ⋯ f             = (t₁ ⋯ f) ∶♯ (t₂ ⋯ f)
  (t₁ ,ˢ t₂) ⋯ f             = (t₁ ⋯ f) ,ˢ (t₂ ⋯ f)
  True ⋯ f                   = True
  (t₁ ∧ t₂) ⋯ f              = (t₁ ⋯ f) ∧ (t₂ ⋯ f)
  (t₁ # t₂) ⋯ f              = (t₁ ⋯ f) # (t₂ ⋯ f)

  kit-traversal : KitTraversal
  kit-traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var } where
    -- Applying a renaming or substitution to a variable does the expected thing.
    ⋯-var : ∀ {{𝕂 : Kit}} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) → (` x) ⋯ f ≡ tm _ (f _ x)
    ⋯-var {m = 𝕧} _ _ = refl
    ⋯-var {m = 𝕥} _ _ = refl

  -- kit-type-subst : KitTypeSubst kit-type kit-traversal
  -- kit-type-subst = record {}
  -- open KitTypeSubst kit-type-subst

  drop-∈-▷▷₁ : (x : µ' ∋ m) → drop-∈ x (µ ▷▷ µ') ≡ µ ▷▷ drop-∈ x µ'
  drop-∈-▷▷₁ (here px) = refl
  drop-∈-▷▷₁ {µ' = µ' ▷ m'} {m = m} {µ = µ} (there x) = drop-∈-▷▷₁ x

  infixl  5  _⋯Ctx'_
  _⋯Ctx'_ : ∀ {{𝕂 : Kit}} → Ctx' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx' µ₂ µ'
  _⋯Ctx'_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ f' where
    f' = subst₂
           (λ x y → x –[ 𝕂 ]→ y)
           (sym (drop-∈-▷▷₁ x))
           (sym (drop-∈-▷▷₁ x))
           (f ↑* drop-∈ x µ')

  -- TODO: Provide derived kits for contexts.
  _⋯Ctx''_ : ∀ {{𝕂 : Kit}} → Ctx'' µ₁ µ' → µ₁ –[ 𝕂 ]→ µ₂ → Ctx'' µ₂ µ'
  _⋯Ctx''_ {µ' = µ'} {{𝕂}} Γ f x = Γ x ⋯ (f ↑* drop-∈ x µ')

open KitTraversal kit-traversal public hiding (_⋯_)

instance 𝕂ᵣ = kitᵣ
instance 𝕂ₛ = kitₛ

-- Composition of Renamings and Substitutions ----------------------------------

open import KitTheory.Compose 𝕋 kit-traversal
open ComposeKit {{...}} public

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a₁ a₂ b₁ b₂ c₁ c₂} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
cong₄ f refl refl refl refl = refl

cong₅ : ∀ {A B C D E F : Set} (f : A → B → C → D → E → F) {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f a₁ b₁ c₁ d₁ e₁ ≡ f a₂ b₂ c₂ d₂ e₂
cong₅ f refl refl refl refl refl = refl

open import Axiom.Extensionality.Propositional using (ExtensionalityImplicit)
postulate fun-ext-i : ∀ {ℓ₁ ℓ₂} → ExtensionalityImplicit ℓ₁ ℓ₂

kit-assoc : KitAssoc
kit-assoc = record { ⋯-assoc = ⋯-assoc } where
  ⋯-assoc : ∀ {{𝕂₁ 𝕂₂ 𝕂 : Kit}} {{𝔸 : ComposeKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
              (v : Term µ₁ M) (f : µ₁ –[ 𝕂₂ ]→ µ₂) (g : µ₂ –[ 𝕂₁ ]→ µ₃) →
    (v ⋯ f) ⋯ g ≡ v ⋯ (g ∘ₖ f)
  ⋯-assoc ⟨ t ⟩ f g                  = cong ⟨_⟩ (⋯-assoc t f g)
  ⋯-assoc (t₁ ∥ t₂) f g              = cong₂ _∥_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (ν[α,x]→ t) f g            = cong ν[α,x]→_
    (t ⋯ (f ↑* _) ⋯ (g ↑* _)    ≡⟨ ⋯-assoc t (f ↑* _) (g ↑* _) ⟩
     t ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (t ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
     t ⋯ ((g ∘ₖ f) ↑* _)        ∎)
  ⋯-assoc ⟨ t ⟩ᵥ f g                 = cong ⟨_⟩ᵥ (⋯-assoc t f g)
  ⋯-assoc (let[x= t₁ ]in t₂) f g     = cong₂ let[x=_]in_ (⋯-assoc t₁ f g)
    (t₂ ⋯ (f ↑* _) ⋯ (g ↑* _)    ≡⟨ ⋯-assoc t₂ (f ↑* _) (g ↑* _) ⟩
     t₂ ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (t₂ ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
     t₂ ⋯ ((g ∘ₖ f) ↑* _)       ∎)
  ⋯-assoc (fork t) f g               = cong fork (⋯-assoc t f g)
  ⋯-assoc (t₁ · t₂) f g              = cong₂ _·_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (send t₁ on t₂) f g        = cong₂ send_on_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (recv t) f g               = cong recv (⋯-assoc t f g)
  ⋯-assoc (select l on t) f g        = cong (select l on_) (⋯-assoc t f g)
  ⋯-assoc case t of[ t₁ , t₂ ] f g   = cong₃ case_of[_,_] (⋯-assoc t f g) (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (close t) f g              = cong close (⋯-assoc t f g)
  ⋯-assoc (π l t) f g                = cong (π l) (⋯-assoc t f g)
  ⋯-assoc (t₁ ∙ t₂) f g              = cong₂ _∙_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (`ᵛ x) f g                 = tm-⋯-∘ f g x
  ⋯-assoc (λx→ t) f g                = cong λx→_
    (t ⋯ (f ↑ _) ⋯ (g ↑ _)   ≡⟨ ⋯-assoc t (f ↑ _) (g ↑ _) ⟩
    t ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
    t ⋯ ((g ∘ₖ f) ↑ _)       ∎)
  ⋯-assoc (Λα→ t) f g                = cong Λα→_
    (t ⋯ (f ↑* _) ⋯ (g ↑* _)   ≡⟨ ⋯-assoc t (f ↑* _) (g ↑* _) ⟩
    t ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (t ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
    t ⋯ ((g ∘ₖ f) ↑* _)        ∎)
  ⋯-assoc unit f g                   = refl
  ⋯-assoc (t₁ ,ᵉ t₂) f g             = cong₂ _,ᵉ_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc Type f g                   = refl
  ⋯-assoc Session f g                = refl
  ⋯-assoc State f g                  = refl
  ⋯-assoc Shape f g                  = refl
  ⋯-assoc Cstr f g                   = refl
  ⋯-assoc (Dom t) f g                = cong Dom (⋯-assoc t f g)
  ⋯-assoc (t₁ ⇒ t₂) f g              = cong₂ _⇒_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc Kind f g                   = refl
  ⋯-assoc (`ᵗ x) f g                 = tm-⋯-∘ f g x
  ⋯-assoc (t₁ ·ᵗ t₂) f g             = cong₂ _·ᵗ_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (λα→ t) f g                = cong λα→_
    (t ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc t (f ↑ _) (g ↑ _) ⟩
     t ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     t ⋯ ((g ∘ₖ f) ↑ _)       ∎)
  ⋯-assoc (∀α[ ℂ ]→ t) f g    = cong₂ ∀α[_]→_
    (ℂ ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc ℂ (f ↑ _) (g ↑ _) ⟩
     ℂ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (ℂ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     ℂ ⋯ ((g ∘ₖ f) ↑ _)       ∎)
    (t ⋯ (f ↑* _) ⋯ (g ↑* _)    ≡⟨ ⋯-assoc t (f ↑* _) (g ↑* _) ⟩
     t ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (t ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
     t ⋯ ((g ∘ₖ f) ↑* _)        ∎)
  ⋯-assoc (⟨_;_–→∃_;_;_⟩ {µ' = µ'} Σ₁ t₁ Γ Σ₂ t₂) f g = cong₅ ⟨_;_–→∃_;_;_⟩
    (⋯-assoc Σ₁ f g)
    (⋯-assoc t₁ f g)
    (fun-ext-i (fun-ext (λ x →
      Γ x ⋯ (f ↑* drop-∈ x µ') ⋯ (g ↑* drop-∈ x µ')    ≡⟨ ⋯-assoc (Γ x) _ _ ⟩
      Γ x ⋯ ((g ↑* drop-∈ x µ') ∘ₖ (f ↑* drop-∈ x µ')) ≡⟨ cong (Γ x ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
      Γ x ⋯ ((g ∘ₖ f) ↑* drop-∈ x µ') ∎
    )))
    (Σ₂ ⋯ f ↑* _ ⋯ g ↑* _        ≡⟨ ⋯-assoc Σ₂ (f ↑* _) (g ↑* _) ⟩
     Σ₂ ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (Σ₂ ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
     Σ₂ ⋯ (g ∘ₖ f) ↑* _          ∎)
    (t₂ ⋯ f ↑* _ ⋯ g ↑* _        ≡⟨ ⋯-assoc t₂ (f ↑* _) (g ↑* _) ⟩
     t₂ ⋯ ((g ↑* _) ∘ₖ (f ↑* _)) ≡⟨ cong (t₂ ⋯_) (sym (dist-↑*-∘ _ g f)) ⟩
     t₂ ⋯ (g ∘ₖ f) ↑* _          ∎)
  ⋯-assoc (Chan t) f g               = cong Chan (⋯-assoc t f g)
  ⋯-assoc Unit f g                   = refl
  ⋯-assoc (t₁ × t₂) f g              = cong₂ _×_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (![∃α→ Σ₁ ; t₁ ] t) f g    = cong₃ ![∃α→_;_]_
    (Σ₁ ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc Σ₁ (f ↑ _) (g ↑ _) ⟩
     Σ₁ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (Σ₁ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     Σ₁ ⋯ ((g ∘ₖ f) ↑ _)       ∎)
    (t₁ ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc t₁ (f ↑ _) (g ↑ _) ⟩
     t₁ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t₁ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     t₁ ⋯ ((g ∘ₖ f) ↑ _)       ∎)
    (⋯-assoc t f g)
  ⋯-assoc (?[∃α→ Σ₁ ; t₁ ] t) f g    = cong₃ ?[∃α→_;_]_
    (Σ₁ ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc Σ₁ (f ↑ _) (g ↑ _) ⟩
     Σ₁ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (Σ₁ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     Σ₁ ⋯ ((g ∘ₖ f) ↑ _)       ∎)
    (t₁ ⋯ (f ↑ _) ⋯ (g ↑ _)    ≡⟨ ⋯-assoc t₁ (f ↑ _) (g ↑ _) ⟩
     t₁ ⋯ ((g ↑ _) ∘ₖ (f ↑ _)) ≡⟨ cong (t₁ ⋯_) (sym (dist-↑-∘ _ g f)) ⟩
     t₁ ⋯ ((g ∘ₖ f) ↑ _)       ∎)
    (⋯-assoc t f g)
  ⋯-assoc (t₁ ⊕ t₂) f g              = cong₂ _⊕_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (t₁ & t₂) f g              = cong₂ _&_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc End f g                    = refl
  ⋯-assoc (Dual t) f g               = cong Dual (⋯-assoc t f g)
  ⋯-assoc [1] f g                    = refl
  ⋯-assoc (t₁ + t₂) f g              = cong₂ _+_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (t₁ ,ᵈ t₂) f g             = cong₂ _,ᵈ_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (πᵈ l t) f g               = cong (πᵈ l) (⋯-assoc t f g)
  ⋯-assoc [] f g                     = refl
  ⋯-assoc (t₁ ∶ t₂) f g              = cong₂ _∶_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (t₁ ∶♯ t₂) f g             = cong₂ _∶♯_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (t₁ ,ˢ t₂) f g             = cong₂ _,ˢ_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc True f g                   = refl
  ⋯-assoc (t₁ ∧ t₂) f g              = cong₂ _∧_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)
  ⋯-assoc (t₁ # t₂) f g              = cong₂ _#_ (⋯-assoc t₁ f g) (⋯-assoc t₂ f g)

open KitAssoc kit-assoc public

instance 𝕂ᵣᵣ = kitᵣᵣ
instance 𝕂ᵣₛ = kitᵣₛ
instance 𝕂ₛᵣ = kitₛᵣ
instance 𝕂ₛₛ = kitₛₛ

-- Applying the identity renaming/substitution does nothing.
kit-assoc-lemmas : KitAssocLemmas
kit-assoc-lemmas = record { ⋯-id = ⋯-id } where
  ⋯-id : ∀ {{𝕂 : Kit}} (v : Term µ M) → v ⋯ idₖ {{𝕂}} ≡ v
  ⋯-id ⟨ t ⟩                  = cong ⟨_⟩ (⋯-id t)
  ⋯-id (t₁ ∥ t₂)              = cong₂ _∥_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id {µ = µ} {{𝕂}} (ν[α,x]→ t) rewrite id↑*≡id {{𝕂}} ([] ▷ 𝕥 ▷ 𝕧) µ = cong ν[α,x]→_ (⋯-id t)
  ⋯-id ⟨ t ⟩ᵥ                 = cong ⟨_⟩ᵥ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (let[x=_]in_ {µ' = µ'} t₁ t₂) rewrite id↑*≡id {{𝕂}} (µ' ▷ 𝕧) µ = cong₂ let[x=_]in_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (fork t)               = cong fork (⋯-id t)
  ⋯-id (t₁ · t₂)              = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (send t₁ on t₂)        = cong₂ send_on_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (recv t)               = cong recv (⋯-id t)
  ⋯-id (select l on t)        = cong (select l on_) (⋯-id t)
  ⋯-id case t of[ t₁ , t₂ ]   = cong₃ case_of[_,_] (⋯-id t) (⋯-id t₁) (⋯-id t₂)
  ⋯-id (close t)              = cong close (⋯-id t)
  ⋯-id (π l t)                = cong (π l) (⋯-id t)
  ⋯-id (t₁ ∙ t₂)              = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (`ᵛ x)                 = tm-vr x
  ⋯-id {µ = µ} {{𝕂}} (λx→ t) rewrite id↑≡id {{𝕂}} 𝕧 µ = cong λx→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (Λα→ t) rewrite id↑*≡id {{𝕂}} ([] ▷ 𝕥 ▷ 𝕧) µ = cong Λα→_ (⋯-id t)
  ⋯-id unit                   = refl
  ⋯-id (t₁ ,ᵉ t₂)             = cong₂ _,ᵉ_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id Type                   = refl
  ⋯-id Session                = refl
  ⋯-id State                  = refl
  ⋯-id Shape                  = refl
  ⋯-id Cstr                   = refl
  ⋯-id (Dom t)                = cong Dom (⋯-id t)
  ⋯-id (t₁ ⇒ t₂)              = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id Kind                   = refl
  ⋯-id (`ᵗ α)                 = tm-vr α
  ⋯-id (t₁ ·ᵗ t₂)             = cong₂ _·ᵗ_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id {µ = µ} {{𝕂}} (λα→ t)  rewrite id↑≡id {{𝕂}} 𝕥 µ = cong λα→_ (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (∀α[ ℂ ]→ t)  rewrite id↑*≡id {{𝕂}} ([] ▷ 𝕥 ▷ 𝕧) µ | id↑≡id {{𝕂}} 𝕥 µ = cong₂ ∀α[_]→_ (⋯-id ℂ) (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (⟨_;_–→∃_;_;_⟩ {µ' = µ'} Σ₁ t₁ Γ Σ₂ t₂) rewrite (id↑*≡id {{𝕂}} µ' µ) = cong₅ ⟨_;_–→∃_;_;_⟩
    (⋯-id Σ₁)
    (⋯-id t₁)
    (fun-ext-i (fun-ext (λ x →
      Γ x ⋯ (idₖ ↑* drop-∈ x µ') ≡⟨ cong (Γ x ⋯_) (id↑*≡id (drop-∈ x µ') µ) ⟩
      Γ x ⋯ idₖ                  ≡⟨ ⋯-id (Γ x) ⟩
      Γ x                        ∎
    )))
    (⋯-id Σ₂)
    (⋯-id t₂)
  ⋯-id (Chan t)               = cong Chan (⋯-id t)
  ⋯-id Unit                   = refl
  ⋯-id (t₁ × t₂)              = cong₂ _×_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id {µ = µ} {{𝕂}} (![∃α→ Σ₁ ; t₁ ] t)  rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₃ ![∃α→_;_]_ (⋯-id Σ₁) (⋯-id t₁) (⋯-id t)
  ⋯-id {µ = µ} {{𝕂}} (?[∃α→ Σ₁ ; t₁ ] t)  rewrite id↑≡id {{𝕂}} 𝕥 µ = cong₃ ?[∃α→_;_]_ (⋯-id Σ₁) (⋯-id t₁) (⋯-id t)
  ⋯-id (t₁ ⊕ t₂)              = cong₂ _⊕_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ & t₂)              = cong₂ _&_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id End                    = refl
  ⋯-id (Dual t)               = cong Dual (⋯-id t)
  ⋯-id [1]                    = refl
  ⋯-id (t₁ + t₂)              = cong₂ _+_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ,ᵈ t₂)             = cong₂ _,ᵈ_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (πᵈ l t)               = cong (πᵈ l) (⋯-id t)
  ⋯-id []                     = refl
  ⋯-id (t₁ ∶ t₂)              = cong₂ _∶_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ∶♯ t₂)             = cong₂ _∶♯_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ,ˢ t₂)             = cong₂ _,ˢ_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id True                   = refl
  ⋯-id (t₁ ∧ t₂)              = cong₂ _∧_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ # t₂)              = cong₂ _#_ (⋯-id t₁) (⋯-id t₂)

open KitAssocLemmas kit-assoc-lemmas public

-- Types and Contexts ----------------------------------------------------------

open import KitTheory.OPE 𝕋 kit-traversal kit-assoc kit-assoc-lemmas kit-type public
