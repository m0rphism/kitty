open import Kitty.Term.Terms
open import Kitty.Term.Traversal using (Traversal)
open import Kitty.Term.KitHomotopy using (KitHomotopy)
open import Kitty.Term.Sub using (SubWithLaws)
open import Kitty.Term.SubCompose using (SubCompose)
open import Kitty.Term.ComposeTraversal using (ComposeTraversal)

module Kitty.Term.KitX
    {𝕋 : Terms}
    {ℓ} {𝕊 : SubWithLaws 𝕋 ℓ}
    {T : Traversal 𝕋 𝕊}
    {H : KitHomotopy T}
    {𝕊C : SubCompose H}
    (C : ComposeTraversal 𝕊C)
  where

open import Kitty.Term.ComposeKit H
open import Kitty.Term.Kit 𝕋
open import Kitty.Term.KitOrder 𝕋
open import Kitty.Term.KitT T
open import Kitty.Term.Prelude
open import Kitty.Term.Sub 𝕋
open ComposeKit ⦃ … ⦄
open Kit ⦃ … ⦄
open Kitty.Term.Sub.SubWithLaws 𝕊
open Sub SubWithLaws-Sub
open Terms 𝕋
open Traversal T
open _⊑ₖ_ ⦃ … ⦄
open ~-Reasoning
open import Level using () renaming (suc to lsuc)
open SubCompose 𝕊C
open Kitty.Term.ComposeTraversal.ComposeTraversal C

record KitX {_∋/⊢_ : VarScoped} (𝕂 : Kit _∋/⊢_) : Set (lsuc ℓ) where
  field
    ⦃ KitX-KitT         ⦄ : KitT 𝕂
    ⦃ KitX-ComposeKitₖₖ ⦄ : ComposeKit 𝕂 𝕂 𝕂
    ⦃ KitX-ComposeKitₖᵣ ⦄ : ComposeKit 𝕂 kitᵣ 𝕂
    ⦃ KitX-ComposeKitᵣₖ ⦄ : ComposeKit kitᵣ 𝕂 𝕂
    ⦃ KitX-ComposeKitₖₛ ⦄ : ComposeKit 𝕂 kitₛ kitₛ
    ⦃ KitX-ComposeKitₛₖ ⦄ : ComposeKit kitₛ 𝕂 kitₛ

  instance
    KitX-Kit : Kit _∋/⊢_
    KitX-Kit = 𝕂

instance
  kitxᵣ : KitX kitᵣ
  kitxᵣ = record
    { KitX-KitT         = kittᵣ
    ; KitX-ComposeKitₖₖ = ckitᵣ ⦃ kitᵣ ⦄
    ; KitX-ComposeKitₖᵣ = ckitᵣ ⦃ kitᵣ ⦄
    ; KitX-ComposeKitᵣₖ = ckitᵣ ⦃ kitᵣ ⦄
    ; KitX-ComposeKitₖₛ = ckitᵣ ⦃ kitₛ ⦄
    ; KitX-ComposeKitₛₖ = ckitₛᵣ
    }

  kitxₛ : KitX kitₛ
  kitxₛ = record
    { KitX-KitT         = kittₛ
    ; KitX-ComposeKitₖₖ = ckitₛₛ
    ; KitX-ComposeKitₖᵣ = ckitₛᵣ
    ; KitX-ComposeKitᵣₖ = ckitᵣ ⦃ kitₛ ⦄
    ; KitX-ComposeKitₖₛ = ckitₛₛ
    ; KitX-ComposeKitₛₖ = ckitₛₛ
    }
