module Kitty.Util.Star where

open import Data.Nat  using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; suc-injective)
open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.List.Properties using (++-identityʳ; ++-assoc; length-++)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym; module ≡-Reasoning)
open ≡-Reasoning

-- Star-Lists and Folds --------------------------------------------------------

infixr 5 _∷_
data Star {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) : List B → A → A → Set (ℓ₁ ⊔ ℓ₂) where
  [] : ∀ {a} → Star R [] a a
  _∷_ : ∀ {a₁ a₂ a₃ b bs} → R b a₁ a₂ → Star R bs a₂ a₃ → Star R (b ∷ bs) a₁ a₃

infixr 5 _∷[_]_
pattern _∷[_]_  f b fs = _∷_ {b = b} f fs

flip-R : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (B → A → A → Set) → (B → A → A → Set)
flip-R R b a₁ a₂ = R b a₂ a₁

infixr 5 _++*_
_++*_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {bs₁} {bs₂} {a₁} {a₂} {a₃}
      → Star R bs₁ a₁ a₂
      → Star R bs₂ a₂ a₃
      → Star R (bs₁ ++ bs₂) a₁ a₃
[]        ++* rs₂ = rs₂
(r ∷ rs₁) ++* rs₂ = r ∷ (rs₁ ++* rs₂)

infixl 5 _∷ʳ_
_∷ʳ_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {a₁ a₂ a₃ b bs}
       → Star R bs a₁ a₂ → R b a₂ a₃ → Star R (bs ++ b ∷ []) a₁ a₃
rs ∷ʳ r = rs ++* r ∷ []

revₗ : ∀ {ℓ} {A : Set ℓ} → List A → List A
revₗ [] = []
revₗ (x ∷ xs) = revₗ xs ++ x ∷ []

-- revₗ-++ : ∀ {ℓ} {A : Set ℓ} → (xs ys : List A)
--             → revₗ (xs ++ ys) ≡ revₗ ys ++ revₗ xs
-- revₗ-++ []       ys = sym (++-identityʳ (revₗ ys))
-- revₗ-++ (x ∷ xs) ys =
--   revₗ (xs ++ ys) ++ x ∷ []      ≡⟨ cong (_++ x ∷ []) (revₗ-++ xs ys) ⟩
--   (revₗ ys ++ revₗ xs) ++ x ∷ [] ≡⟨ ++-assoc (revₗ ys) (revₗ xs) (x ∷ []) ⟩
--   revₗ ys ++ (revₗ xs ++ x ∷ []) ∎

-- revₗ-idem : ∀ {ℓ} {A : Set ℓ} → (xs : List A)
--             → revₗ (revₗ xs) ≡ xs
-- revₗ-idem [] = refl
-- revₗ-idem (x ∷ xs) =
--   revₗ (revₗ xs ++ x ∷ []) ≡⟨ revₗ-++ (revₗ xs) (x ∷ []) ⟩
--   x ∷ revₗ (revₗ xs) ≡⟨ cong (x ∷_) (revₗ-idem xs) ⟩
--   x ∷ xs ∎

rev : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {a₁} {a₂} {bs}
      → Star R bs a₁ a₂
      → Star (flip-R R) (revₗ bs) a₂ a₁
rev []       = []
rev (r ∷ rs) = rev rs ++* (r ∷ [])

-- rev-idem : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {bs} → (rs : Star R bs a₁ a₂)
--             → rev (rev rs) ≡ subst (λ ■ → Star R ■ a₁ a₂) (sym (revₗ-idem bs)) rs
-- rev-idem = {!!}

fold-star : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {bs} →
  (∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂) →
  T a₁ → Star R bs a₁ a₂ → T a₂
fold-star f t [] = t
fold-star f t₁ (r₁₂ ∷ rs₂₃) = fold-star f (f _ _ _ t₁ r₁₂) rs₂₃

fold-star' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {bs} →
  (∀ b a₂ a₁ → T a₂ → R b a₁ a₂ → T a₁) →
  T a₂ → Star R bs a₁ a₂ → T a₁
fold-star' f ta [] = ta
fold-star' f ta (rab ∷ rbc) = f _ _ _ (fold-star' f ta rbc) rab

fold-star'-∷ʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {a₃} {b} {bs} →
  (f : ∀ b a₂ a₁ → T a₂ → R b a₁ a₂ → T a₁) →
  (t₃ : T a₃)
  (rs₁₂ : Star R bs a₁ a₂)
  (r₂₃ : R b a₂ a₃)
  → fold-star' f (f _ _ _ t₃ r₂₃) rs₁₂  ≡
    fold-star' f t₃ (rs₁₂ ∷ʳ r₂₃)
fold-star'-∷ʳ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {.a₁} {a₃} {b} {.[]}    f t₃ [] r₂₃ = refl
fold-star'-∷ʳ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {a₂} {a₃} {b} {b' ∷ bs} f t₃ (x ∷ rs₁₂) r₂₃ =
  f b' _ a₁ (fold-star' f (f b a₃ a₂ t₃ r₂₃) rs₁₂) x  ≡⟨ cong (λ ■ → f b' _ a₁ ■ x) (fold-star'-∷ʳ f t₃ rs₁₂ r₂₃) ⟩
  f b' _ a₁ (fold-star' f t₃ (rs₁₂ ++* (r₂₃ ∷ []))) x ∎

fold-star-rev : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {bs} →
  (f : ∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂) →
  (ta : T a₁)
  (rs : Star R bs a₁ a₂)
  → fold-star f ta rs ≡ fold-star' f ta (rev rs)
fold-star-rev {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {.a₁} {.[]}   f t₁ [] = refl
fold-star-rev {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {a₂} {b ∷ bs} f t₁ (r₁₂ ∷ rs₂₃) =
  fold-star f t₁ (r₁₂ ∷ rs₂₃)               ≡⟨⟩
  fold-star f (f _ _ _ t₁ r₁₂) rs₂₃         ≡⟨ fold-star-rev f (f _ _ _ t₁ r₁₂) rs₂₃ ⟩
  fold-star' f (f _ _ _ t₁ r₁₂) (rev rs₂₃)  ≡⟨ fold-star'-∷ʳ f t₁ (rev rs₂₃) r₁₂ ⟩
  fold-star' f t₁ (rev rs₂₃ ++* (r₁₂ ∷ [])) ≡⟨⟩
  fold-star' f t₁ (rev (r₁₂ ∷ rs₂₃)) ∎

fold-star-∷ʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {a₃} {b} {bs} →
  (f : ∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂) →
  (t₃ : T a₁)
  (rs₁₂ : Star R bs a₁ a₂)
  (r₂₃ : R b a₂ a₃)
  → f _ _ _ (fold-star f t₃ rs₁₂) r₂₃  ≡
    fold-star f t₃ (rs₁₂ ∷ʳ r₂₃)
fold-star-∷ʳ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {.a₁} {a₃} {b} {.[]} f t₃ [] r₂₃ = refl
fold-star-∷ʳ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {a₂} {a₃} {b} {b' ∷ bs} f t₃ (x ∷ rs₁₂) r₂₃ =
  f b a₂ a₃ (fold-star f (f b' a₁ _ t₃ x) rs₁₂) r₂₃  ≡⟨ fold-star-∷ʳ f (f b' a₁ _ t₃ x) rs₁₂ r₂₃ ⟩
  fold-star f (f b' a₁ _ t₃ x) (rs₁₂ ++* (r₂₃ ∷ [])) ∎

fold-star-rev' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁} {a₂} {bs} →
  (f : ∀ b a₂ a₁ → T a₂ → R b a₁ a₂ → T a₁) →
  (ta : T a₂)
  (rs : Star R bs a₁ a₂)
  → fold-star' f ta rs ≡ fold-star f ta (rev rs)
fold-star-rev' {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {.a₁} {.[]} f ta [] = refl
fold-star-rev' {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a₁} {a₂} {b ∷ bs} f ta (r₁₂ ∷ rs₂₃) =
  fold-star' f ta (r₁₂ ∷ rs₂₃)       ≡⟨⟩
  f _ _ _ (fold-star' f ta rs₂₃) r₁₂ ≡⟨ cong (λ ■ → f _ _ _ ■ r₁₂) (fold-star-rev' f ta rs₂₃) ⟩
  f _ _ _ (fold-star f ta (rev rs₂₃)) r₁₂ ≡⟨ fold-star-∷ʳ f ta (rev rs₂₃) r₁₂ ⟩
  fold-star f ta (rev rs₂₃ ++* (r₁₂ ∷ [])) ≡⟨⟩
  fold-star f ta (rev (r₁₂ ∷ rs₂₃))  ∎

fold-star→' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁ a₂} {bs} →
  (f : ∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂) →
  (ta : T a₁)
  (rs : Star R bs a₁ a₂)
  → fold-star f ta rs ≡ fold-star' {T = λ a → T a → T a₂} (λ b a₁ a₂ ftx rbyx ty → ftx (f b a₂ a₁ ty rbyx)) (λ tb → tb) rs ta
fold-star→' {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a} {.a} {.[]}     f ta [] = refl
fold-star→' {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a} {b}  {b' ∷ bs} f ta (ray ∷ rsyb) = fold-star→' f (f b' a _ ta ray) rsyb

-- fold-star'→ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a} {b} {bs} →
--   (f : ∀ b x y → T x → R b y x → T y) →
--   (ta : T a)
--   (rs : Star R bs b a)
--   → fold-star' f ta rs ≡ fold-star {T = λ a → T a → T b} (λ b x y ftx rbyx ty → ftx (f b y x ty rbyx)) (λ tb → tb) rs ta
-- fold-star'→ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a} {.a} {.[]} f ta [] = refl
-- fold-star'→ {ℓ₁} {ℓ₂} {A} {B} {R} {T} {a} {b} {b' ∷ bs} f ta (x ∷ rs) =
--   f b' _ b (fold-star' f ta rs) x ≡⟨ cong (λ ■ → f b' _ b ■ x) (fold-star'→ f ta rs) ⟩
--   f b' _ b (fold-star (λ b x y ftx rbyx ty → ftx (f b y x ty rbyx)) (λ tb → tb) rs ta) x ≡⟨ {!!} ⟩
--   fold-star (λ b₂ x₁ y₁ ftx rbyx ty → ftx (f b₂ y₁ x₁ ty rbyx)) (λ ty → f b' _ b ty x) rs ta ∎

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

-- Reversed Star-Lists and Folds -----------------------------------------------

data Starʳ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (R : B → A → A → Set) : List B → A → A → Set (ℓ₁ ⊔ ℓ₂) where
  [] : ∀ {a} → Starʳ R [] a a
  _++[_]by_ : ∀ {a₁ a₂ a₃ b bs bs'} → Starʳ R bs a₁ a₂ → R b a₂ a₃ → bs' ≡ bs ++ b ∷ [] → Starʳ R bs' a₁ a₃

fold-starʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁ a₂} {bs} →
  (∀ b a₁ a₂ → T a₂ → R b a₁ a₂ → T a₁) →
  T a₂ → Starʳ R bs a₁ a₂ → T a₁
fold-starʳ f ta [] = ta
fold-starʳ f ta (rabs ++[ rbc ]by refl) = fold-starʳ f (f _ _ _ ta rbc) rabs

fold-starʳ' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁ a₂} {bs} →
  (∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂) →
  T a₁ → Starʳ R bs a₁ a₂ → T a₂
fold-starʳ' f ta [] = ta
fold-starʳ' f ta (rabs ++[ rbc ]by refl) = f _ _ _ (fold-starʳ' f ta rabs) rbc

_++*ʳ_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {bs₁} {bs₂} {a₁} {a₂} {a₃}
      → Starʳ R bs₁ a₁ a₂
      → Starʳ R bs₂ a₂ a₃
      → Starʳ R (bs₁ ++ bs₂) a₁ a₃
rs₁ ++*ʳ []                                                = subst (λ ■ → Starʳ _ ■ _ _) (sym (++-identityʳ _)) rs₁
rs₁ ++*ʳ (_++[_]by_ {x} {y} {z} {b} {bs} {bs'} rs₂ r refl) = (rs₁ ++*ʳ rs₂) ++[ r ]by sym (++-assoc _ bs (b ∷ []))

Star→ʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {a₁ a₂} {bs}
  → Star R bs a₁ a₂
  → Starʳ R bs a₁ a₂
Star→ʳ [] = []
Star→ʳ (r ∷ rs) = ([] ++[ r ]by refl) ++*ʳ Star→ʳ rs

data Match-Starʳ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {a₁ a₂} {bs} (rs : Star R bs a₁ a₂) : Set (ℓ₁ ⊔ ℓ₂) where
  Match-[] :
      (eq₁ : [] ≡ bs)
    → (eq₂ : a₁ ≡ a₂)
    → rs ≡ subst₂ (λ ■₁ ■₂ → Star R ■₁ a₁ ■₂) eq₁ eq₂ []
    → Match-Starʳ rs
  Match-++ : ∀ bs' b' a (rs' : Star R bs' a₁ a) (r' : R b' a a₂)
    → (eq₁ : bs' ++ b' ∷ [] ≡ bs)
    → rs ≡ subst (λ ■ → Star R ■ a₁ a₂) eq₁ (rs' ++* (r' ∷ []))
    → length bs ≡ suc (length bs')
    → Match-Starʳ rs

match-Starʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {a₁ a₂} {bs}
  → (rs : Star R bs a₁ a₂)
  → Match-Starʳ rs
match-Starʳ []       = Match-[] refl refl refl
match-Starʳ (_∷_ {b = b} r rs) with match-Starʳ rs
... | Match-[] refl refl refl               = Match-++ [] _ _ [] r refl refl refl
... | Match-++ bs' b' a rs' r' refl refl eq = Match-++ (_ ∷ bs') _ _ (_ ∷ rs') _ refl refl (
    length (b ∷ bs' ++ b' ∷ []) ≡⟨ length-++ (b ∷ bs') ⟩
    length (b ∷ bs') + length (b' ∷ []) ≡⟨⟩
    length (b ∷ bs') + 1 ≡⟨ +-comm (length (b ∷ bs')) 1 ⟩
    suc (length (b ∷ bs'))      ∎
  )

Star-indʳ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set}
         {P : ∀ {bs} {a₁ a₂} → Star R bs a₁ a₂ → Set}
  → (∀ {a₁ a₂} (rs : Star R [] a₁ a₂) → P rs)
  → (∀ {bs} {b} {a₁ a₂ a₃} (rs : Star R bs a₁ a₂) (r : R b a₂ a₃) → P rs → P (rs ∷ʳ r))
  → (∀ {bs} {a₁ a₂} (rs : Star R bs a₁ a₂) → P rs)
Star-indʳ p₀ pₛ rs = indʳ' p₀ pₛ _ refl rs
  where
    -- Induction over `length bs` to make the termination checker happy.
    indʳ' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set}
            {P : ∀ {bs} {a₁ a₂} → Star R bs a₁ a₂ → Set}
      → (∀ {a₁ a₂} (rs : Star R [] a₁ a₂) → P rs)
      → (∀ {bs} {b} {a₁ a₂ a₃} (rs : Star R bs a₁ a₂) (r : R b a₂ a₃) → P rs → P (rs ∷ʳ r))
      → (∀ {bs} n (eq : length bs ≡ n) {a₁ a₂} (rs : Star R bs a₁ a₂) → P rs)
    indʳ' p₀ pₛ zero eq [] = p₀ []
    indʳ' p₀ pₛ (suc n) eq rs with match-Starʳ rs
    indʳ' p₀ pₛ (suc n) () rs | Match-[] refl refl refl
    indʳ' p₀ pₛ (suc n) eq rs | Match-++ bs' b' a rs' r' refl refl eq' =
      let eq'' = suc-injective (
            suc (length bs') ≡⟨ sym eq' ⟩
            length (bs' ++ b' ∷ []) ≡⟨ eq ⟩
            suc n ∎
            )
      in
      pₛ rs' r' (indʳ' p₀ pₛ n eq'' rs')

-- -- fold-lr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {R : B → A → A → Set} {T : A → Set} {a₁ a₂} {bs} →
-- --   (f : ∀ b a₁ a₂ → T a₁ → R b a₁ a₂ → T a₂)
-- --   (t₁ : T a₁)
-- --   (rs₁₂ : Star R bs a₁ a₂)
-- --   → fold-star f t₁ rs₁₂ ≡ fold-starʳ' f t₁ (Star→ʳ rs₁₂)
-- -- fold-lr = {!!}
