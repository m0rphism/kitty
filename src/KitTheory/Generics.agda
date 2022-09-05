open import KitTheory.Modes

module KitTheory.Generics (𝕄 : Modes) where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _$_)

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; proj₁; proj₂; _,_)

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

private mutual
  _⋯_ : ∀ {d} {µ₁ : List VarMode} {M : TermMode} {µ₂ : List VarMode}
      ⦃ 𝕂 : Kit (𝕋 d) ⦄ →
      Tm d µ₁ M → _–[_]→_ (𝕋 d) µ₁ 𝕂 µ₂ → Tm d µ₂ M
  _⋯_ (`var x)  f = tm _ (f _ x)
  _⋯_ (`con e') f = `con (e' ⋯' f)

  _⋯'_ : ∀ {d} {d'} {µ₁ : List VarMode} {M : TermMode} {µ₂ : List VarMode}
      ⦃ 𝕂 : Kit (𝕋 d) ⦄ →
      ⟦ d' ⟧ (Tm d) µ₁ M → _–[_]→_ (𝕋 d) µ₁ 𝕂 µ₂ → ⟦ d' ⟧ (Tm d) µ₂ M
  _⋯'_ {d' = `σ A d'}     (a , D') f = a , D' ⋯' f
  _⋯'_ {d' = `X µ' M' d'} (e , e') f = e ⋯ (f ↑* µ') , e' ⋯' f
  _⋯'_ {d' = `■ M'}       e        f = e

private 
  ⋯-var : ∀ {d} {µ₁ : List VarMode} {m : VarMode} {µ₂ : List VarMode}
        ⦃ 𝕂 : Kit (𝕋 d) ⦄ (x : µ₁ ∋ m) (ϕ : (𝕂 Kit.–→ µ₁) µ₂) →
        Kit.tm 𝕂 m (ϕ m x) ≡ Kit.tm 𝕂 m (ϕ m x)
  ⋯-var x ϕ = refl

KT : (d : Desc) → KitTraversal (𝕋 d)
KT d = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var }

open import KitTheory.Compose
open ComposeKit {{...}}

private mutual
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
  ⋯-assoc' {d' = `σ A d'}     (a , D')  ϕ₁ ϕ₂ = cong (a ,_) (⋯-assoc' D' ϕ₁ ϕ₂)
  ⋯-assoc' {d' = `X µ' M' d'} (e₁ , e₂) ϕ₁ ϕ₂ = cong₂ _,_ (trans (⋯-assoc e₁ (ϕ₁ ↑* µ') (ϕ₂ ↑* µ'))
                                                                 (cong (e₁ ⋯_) (sym (dist-↑*-∘ µ' ϕ₂ ϕ₁))) )
                                                          (⋯-assoc' e₂ ϕ₁ ϕ₂)
  ⋯-assoc' {d' = `■ M'}       refl      ϕ₁ ϕ₂ = refl

KA : (d : Desc) → KitAssoc (𝕋 d) (KT d)
KA d = record { ⋯-assoc = ⋯-assoc }

private mutual
  ⋯-id : ∀ {d} ⦃ 𝕂 : Kit (𝕋 d) ⦄ {µ : List VarMode} {M : TermMode}
        (e : Tm d µ M) →
        (e ⋯ Kit.idₖ 𝕂) ≡ e
  ⋯-id (`var x) = tm-vr x
  ⋯-id (`con e) = cong `con (⋯-id' e)

  ⋯-id' : ∀ {d} {d'} ⦃ 𝕂 : Kit (𝕋 d) ⦄ {µ : List VarMode} {M : TermMode}
        (e : ⟦ d' ⟧ (Tm d) µ M) →
        (e ⋯' Kit.idₖ 𝕂) ≡ e
  ⋯-id' {d' = `σ A d'}     (a , D')  = cong (a ,_) (⋯-id' D')
  ⋯-id' {d' = `X µ' M' d'} (e₁ , e₂) = cong₂ _,_ (trans (cong (e₁ ⋯_) (id↑*≡id µ' _)) (⋯-id e₁)) (⋯-id' e₂)
  ⋯-id' {d' = `■ M'}       refl      = refl

KAL : (d : Desc) → KitAssoc.KitAssocLemmas (KA d)
KAL d = record { ⋯-id = ⋯-id }

open Agda.Primitive using (Level; _⊔_; lsuc)
record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ a → from (to a) ≡ a
    to∘from : ∀ b → to (from b) ≡ b

module FromIso {_⊢_ : Scoped} {d : Desc} (iso : ∀ {µ} {e} → (µ ⊢ e) ≃ Tm d µ e) where 
  open _≃_ 

  open KitTraversal (KT d) hiding (_⋯_)

  terms : Terms 𝕄
  terms = record
    { _⊢_ = _⊢_
    ; `_ = λ x → from iso (`var x)
    }

  Kit→Kit : Kit terms → Kit (𝕋 d)
  Kit→Kit k = record
    { StuffMode = Kit.StuffMode k
    ; _◆_       = Kit._◆_ k
    ; m→SM      = Kit.m→SM k
    ; SM→M      = Kit.SM→M k
    ; vr        = Kit.vr k
    ; tm        = λ m x → to iso (Kit.tm k m x)
    ; wk        = Kit.wk k
    ; m→SM→M    = Kit.m→SM→M k
    ; wk-vr     = Kit.wk-vr k
    ; tm-vr     = λ x → trans (cong (to iso) (Kit.tm-vr k x)) (to∘from iso (`var x))
    }

  kit-traversal : KitTraversal terms
  kit-traversal = record
    { _⋯_ = λ {{𝕂}} e ϕ →
              let instance _ = Kit→Kit 𝕂 in
              from iso (to iso e ⋯ ϕ)
    ; ⋯-var = λ {{𝕂}} x ϕ →
              let instance _ = Kit→Kit 𝕂 in
              trans (cong (λ ■ → from iso (■ ⋯ ϕ)) (to∘from iso _)) (from∘to iso _)
    }

  ↑→↑ : ∀ {{𝕂}} {µ₁} {µ₂} (ϕ : _–[_]→_ (𝕋 d) µ₁ (Kit→Kit 𝕂) µ₂) m →
    Kit._↑_ (Kit→Kit 𝕂) ϕ m ≡ Kit._↑_ 𝕂 ϕ m
  ↑→↑ ϕ m = fun-ext terms λ m → fun-ext terms λ { (here px) → refl ; (there x) → refl }

  CKit→CKit : ∀ {{𝕂₁}} {{𝕂₂}} {{𝕂}}
    → ComposeKit terms kit-traversal {{𝕂₁}} {{𝕂₂}} {{𝕂}}
    → ComposeKit (𝕋 d) (KT d) {{Kit→Kit 𝕂₁}} {{Kit→Kit 𝕂₂}} {{Kit→Kit 𝕂}}
  CKit→CKit {{𝕂₁}} {{𝕂₂}} {{𝕂}} k = record
    { _∘ₖ_     = ComposeKit._∘ₖ_ k
    ; tm-⋯-∘   = λ ϕ₁ ϕ₂ x → trans (sym (to∘from iso _)) (cong (to iso) (ComposeKit.tm-⋯-∘ k ϕ₁ ϕ₂ x))
    ; dist-↑-∘ = dist-↑-∘' {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{k}} 
    } where
      dist-↑-∘' :  ∀ {{𝕂₁}} {{𝕂₂}} {{𝕂}}
          {{k : ComposeKit terms kit-traversal {{𝕂₁}} {{𝕂₂}} {{𝕂}} }}
          {µ₁ µ₂ µ₃ : List VarMode} (m : VarMode)
          (ϕ₁ : _–[_]→_ (𝕋 d) µ₂ (Kit→Kit 𝕂₁) µ₃)
          (ϕ₂ : _–[_]→_ (𝕋 d) µ₁ (Kit→Kit 𝕂₂) µ₂) →
          -- (ϕ₁ ∘ₖ ϕ₂) ↑ m ≡ (ϕ₁ ↑ m) ∘ₖ (ϕ₂ ↑ m)
          Kit._↑_ (Kit→Kit 𝕂) (ComposeKit._∘ₖ_ k ϕ₁ ϕ₂) m ≡
          ComposeKit._∘ₖ_ k (Kit._↑_ (Kit→Kit 𝕂₁) ϕ₁ m) (Kit._↑_ (Kit→Kit 𝕂₂) ϕ₂ m)
      dist-↑-∘' {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{k = k}} m ϕ₁ ϕ₂
        rewrite ↑→↑ ϕ₁ m
              | ↑→↑ ϕ₂ m
              | ↑→↑ (ComposeKit._∘ₖ_ k ϕ₁ ϕ₂) m
              = ComposeKit.dist-↑-∘ k m ϕ₁ ϕ₂

  kit-assoc : KitAssoc terms kit-traversal
  kit-assoc = record
    { ⋯-assoc = λ {{𝕂₁}} {{𝕂₂}} {{𝕂}} {{ℂ}} e ϕ₁ ϕ₂ →
        let instance _ = Kit→Kit 𝕂₁ in
        let instance _ = Kit→Kit 𝕂₂ in
        let instance _ = Kit→Kit 𝕂 in
        let instance _ = CKit→CKit ℂ in
        trans (cong (λ ■ → from iso (■ ⋯ ϕ₂)) (to∘from iso _)) (cong (from iso) (⋯-assoc (to iso e) ϕ₁ ϕ₂))
    }

  open KitAssoc kit-assoc

  kit-assoc-lemmas : KitAssocLemmas
  kit-assoc-lemmas = record
    { ⋯-id = λ {{𝕂}} v →
        let instance _ = Kit→Kit 𝕂 in
        trans (cong (from iso) (⋯-id (to iso v))) (from∘to iso v)
    }

