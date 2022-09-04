open import KitTheory.Modes

module KitTheory.Generics (𝕄 : Modes) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import KitTheory.Prelude
open Modes 𝕄

private
  variable
    m m₁ m₂ m₃ m' m₁' m₂' m₃' : VarMode
    M M₁ M₂ M₃ M' M₁' M₂' M₃' : TermMode
    µ µ₁ µ₂ µ₃ µ' µ₁' µ₂' µ₃' : List VarMode

Scoped : Set₁
Scoped = List VarMode → TermMode → Set

data Desc : Set₁ where
  `σ : (A : Set) → (A → Desc) → Desc
  `X : List VarMode → TermMode → Desc → Desc
  `■ : TermMode → Desc

⟦_⟧ : Desc → Scoped → Scoped
⟦ `σ A d     ⟧ X µ M = Σ[ a ∈ A ] (⟦ d a ⟧ X µ M)
⟦ `X µ' M' d ⟧ X µ M = X (µ' ++ µ) M' × ⟦ d ⟧ X µ M
⟦ `■ M'      ⟧ X µ M = M ≡ M'

data Tm (d : Desc) : Scoped where
  `var : ∀ {µ m} → µ ∋ m → Tm d µ (m→M m)
  `con : ∀ {µ M} → ⟦ d ⟧ (Tm d) µ M → Tm d µ M

𝕋 : Desc → Terms 𝕄
𝕋 d = record { _⊢_ = Tm d ; `_ = `var }

open import KitTheory.Kit
open Kit {{...}}

mutual
  _⋯_ : ∀ {d} {µ₁ : List VarMode} {M : TermMode} {µ₂ : List VarMode}
      ⦃ 𝕂 : Kit (𝕋 d) ⦄ →
      Tm d µ₁ M → _–[_]→_ (𝕋 d) µ₁ 𝕂 µ₂ → Tm d µ₂ M
  _⋯_ (`var x)  f = tm _ (f _ x)
  _⋯_ (`con e') f = `con (e' ⋯' f)

  _⋯'_ : ∀ {d} {d'} {µ₁ : List VarMode} {M : TermMode} {µ₂ : List VarMode}
      ⦃ 𝕂 : Kit (𝕋 d) ⦄ →
      ⟦ d' ⟧ (Tm d) µ₁ M → _–[_]→_ (𝕋 d) µ₁ 𝕂 µ₂ → ⟦ d' ⟧ (Tm d) µ₂ M
  _⋯'_ {d' = `σ A d'}     ⟨ a , D' ⟩ f = ⟨ a , D' ⋯' f ⟩
  _⋯'_ {d' = `X µ' M' d'} ⟨ e , e' ⟩ f = ⟨ e ⋯ (f ↑* µ') , e' ⋯' f ⟩
  _⋯'_ {d' = `■ M'}       e          f = e

⋯-var : ∀ {d} {µ₁ : List VarMode} {m : VarMode} {µ₂ : List VarMode}
      ⦃ 𝕂 : Kit (𝕋 d) ⦄ (x : µ₁ ∋ m) (ϕ : (𝕂 Kit.–→ µ₁) µ₂) →
      Kit.tm 𝕂 m (ϕ m x) ≡ Kit.tm 𝕂 m (ϕ m x)
⋯-var x ϕ = refl

KT : (d : Desc) → KitTraversal (𝕋 d)
KT d = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

open import KitTheory.Compose
open ComposeKit {{...}}

mutual
  ⋯-assoc : ∀ {d} {µ₁ : List VarMode} {M : TermMode} {µ₂ µ₃ : List VarMode}
        ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit (𝕋 d) ⦄
        ⦃ 𝔸 : ComposeKit (𝕋 d) (KT d) {{𝕂₁}} {{𝕂₂}} {{𝕂}} ⦄
        (e : Tm d µ₁ M)
        (ϕ₁ : _–[_]→_ (𝕋 d) µ₁ 𝕂₂ µ₂)
        (ϕ₂ : _–[_]→_ (𝕋 d) µ₂ 𝕂₁ µ₃) →
        ((e ⋯ ϕ₁) ⋯ ϕ₂) ≡ (e ⋯ (ϕ₂ ∘ₖ ϕ₁))
  ⋯-assoc (`var x)  ϕ₁ ϕ₂ = tm-⋯-∘ ϕ₁ ϕ₂ x
  ⋯-assoc (`con e') ϕ₁ ϕ₂ = cong `con (⋯-assoc' e' ϕ₁ ϕ₂)

  ⋯-assoc' : ∀ {d} {d'} {µ₁ : List VarMode} {M : TermMode} {µ₂ µ₃ : List VarMode}
        ⦃ 𝕂₁ 𝕂₂ 𝕂 : Kit (𝕋 d) ⦄
        ⦃ 𝔸 : ComposeKit (𝕋 d) (KT d) {{𝕂₁}} {{𝕂₂}} {{𝕂}} ⦄
        (e : ⟦ d' ⟧ (Tm d) µ₁ M)
        (ϕ₁ : _–[_]→_ (𝕋 d) µ₁ 𝕂₂ µ₂)
        (ϕ₂ : _–[_]→_ (𝕋 d) µ₂ 𝕂₁ µ₃) →
        ((e ⋯' ϕ₁) ⋯' ϕ₂) ≡ (e ⋯' (ϕ₂ ∘ₖ ϕ₁))
  ⋯-assoc' {d' = `σ A d'}     ⟨ a , D' ⟩  ϕ₁ ϕ₂ = cong ⟨ a ,_⟩ (⋯-assoc' D' ϕ₁ ϕ₂)
  ⋯-assoc' {d' = `X µ' M' d'} ⟨ e₁ , e₂ ⟩ ϕ₁ ϕ₂ = cong₂ ⟨_,_⟩ (trans (⋯-assoc e₁ (ϕ₁ ↑* µ') (ϕ₂ ↑* µ'))
                                                                     (cong (e₁ ⋯_) (sym (dist-↑*-∘ µ' ϕ₂ ϕ₁))) )
                                                              (⋯-assoc' e₂ ϕ₁ ϕ₂)
  ⋯-assoc' {d' = `■ M'}       refl        ϕ₁ ϕ₂ = refl

KA : (d : Desc) → KitAssoc (𝕋 d) (KT d)
KA d = record { ⋯-assoc = ⋯-assoc }

mutual
  ⋯-id : ∀ {d} ⦃ 𝕂 : Kit (𝕋 d) ⦄ {µ : List VarMode} {M : TermMode}
        (e : Tm d µ M) →
        (e ⋯ Kit.idₖ 𝕂) ≡ e
  ⋯-id (`var x) = tm-vr x
  ⋯-id (`con e) = cong `con (⋯-id' e)

  ⋯-id' : ∀ {d} {d'} ⦃ 𝕂 : Kit (𝕋 d) ⦄ {µ : List VarMode} {M : TermMode}
        (e : ⟦ d' ⟧ (Tm d) µ M) →
        (e ⋯' Kit.idₖ 𝕂) ≡ e
  ⋯-id' {d' = `σ A d'}     ⟨ a , D' ⟩  = cong ⟨ a ,_⟩ (⋯-id' D')
  ⋯-id' {d' = `X µ' M' d'} ⟨ e₁ , e₂ ⟩ = cong₂ ⟨_,_⟩ (trans (cong (e₁ ⋯_) (id↑*≡id µ' _)) (⋯-id e₁)) (⋯-id' e₂)
  ⋯-id' {d' = `■ M'}       refl        = refl

KAL : (d : Desc) → KitAssoc.KitAssocLemmas (KA d)
KAL d = record { ⋯-id = ⋯-id }
