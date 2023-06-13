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

record KitX {_∋/⊢_ : VarScoped} (K : Kit _∋/⊢_) : Set (lsuc ℓ) where
  field
    ⦃ KitX-KitT         ⦄ : KitT K
    ⦃ KitX-ComposeKitₖₖ ⦄ : ComposeKit K K K
    ⦃ KitX-ComposeKitₖᵣ ⦄ : ComposeKit K Kᵣ K
    ⦃ KitX-ComposeKitᵣₖ ⦄ : ComposeKit Kᵣ K K
    ⦃ KitX-ComposeKitₖₛ ⦄ : ComposeKit K Kₛ Kₛ
    ⦃ KitX-ComposeKitₛₖ ⦄ : ComposeKit Kₛ K Kₛ

  instance
    KitX-Kit : Kit _∋/⊢_
    KitX-Kit = K

instance
  kitxᵣ : KitX Kᵣ
  kitxᵣ = record
    { KitX-KitT         = Wᵣ
    ; KitX-ComposeKitₖₖ = Cᵣ ⦃ Kᵣ ⦄
    ; KitX-ComposeKitₖᵣ = Cᵣ ⦃ Kᵣ ⦄
    ; KitX-ComposeKitᵣₖ = Cᵣ ⦃ Kᵣ ⦄
    ; KitX-ComposeKitₖₛ = Cᵣ ⦃ Kₛ ⦄
    ; KitX-ComposeKitₛₖ = Cₛᵣ
    }

  kitxₛ : KitX Kₛ
  kitxₛ = record
    { KitX-KitT         = Wₛ
    ; KitX-ComposeKitₖₖ = Cₛₛ
    ; KitX-ComposeKitₖᵣ = Cₛᵣ
    ; KitX-ComposeKitᵣₖ = Cᵣ ⦃ Kₛ ⦄
    ; KitX-ComposeKitₖₛ = Cₛₛ
    ; KitX-ComposeKitₛₖ = Cₛₛ
    }
