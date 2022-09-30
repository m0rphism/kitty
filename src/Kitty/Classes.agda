module Kitty.Classes where

open import Kitty.Modes public
open Terms {{...}} public

-- module _ {𝕄 : Modes} {{𝕋 : Terms 𝕄}} where
--   import Kitty.Kit 𝕋 as MKit
--   open MKit public
--   open Kit {{...}} public
--   open KitTraversal {{...}} public

--   module _ {{T : KitTraversal}} where
--     import Kitty.Compose 𝕋 T as MCompose
--     open MCompose public
--     open ComposeKit {{...}} public
--     open KitAssoc {{...}} public
--     open KitAssocLemmas {{...}} public

--     module _ {{A : KitAssoc}} {{AL : KitAssocLemmas}} where
--       import Kitty.Types 𝕋 T A AL as MTypes
--       open MTypes public
--       open KitType {{...}} public

-- instance 𝕂ᵣ = kitᵣ
-- instance 𝕂ₛ = kitₛ
-- instance 𝕂ᵣᵣ = kitᵣᵣ
-- instance 𝕂ᵣₛ = kitᵣₛ
-- instance 𝕂ₛᵣ = kitₛᵣ
-- instance 𝕂ₛₛ = kitₛₛ


import Kitty.Kit     as MKit
import Kitty.Compose as MCompose
import Kitty.Types   as MTypes
import Kitty.OPE     as MOPE

record Subst : Set₁ where
  field
    modes        : Modes
    terms        : Terms modes
    traversal    : MKit.KitTraversal terms
    assoc        : MCompose.KitAssoc terms traversal
    assoc-lemmas : MCompose.KitAssoc.KitAssocLemmas assoc
    types        : MTypes.KitType terms

  open MKit terms public
  open Kit {{...}} public
  open KitTraversal traversal public

  open MCompose terms traversal public
  open ComposeKit {{...}} public
  open KitAssoc assoc public
  open KitAssocLemmas assoc-lemmas public

  open MTypes terms
  open MOPE terms traversal assoc assoc-lemmas types public
  open KitType types public

  instance 𝕂ᵣ = kitᵣ
  instance 𝕂ₛ = kitₛ
  instance 𝕂ᵣᵣ = kitᵣᵣ
  instance 𝕂ᵣₛ = kitᵣₛ
  instance 𝕂ₛᵣ = kitₛᵣ
  instance 𝕂ₛₛ = kitₛₛ
