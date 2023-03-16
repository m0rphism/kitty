{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive where

-- open import Kitty.Derive.Desc   public
-- open import Kitty.Derive.To     public
-- open import Kitty.Derive.From   public
-- open import Kitty.Derive.ToFrom public
-- open import Kitty.Derive.FromTo public
-- open import Kitty.Derive.Iso    public

open import Kitty.Derive.MultiTraversal public renaming (derive-MultiTraversal to derive)

import Kitty.Term.MultiTraversalDerived
module Derived = Kitty.Term.MultiTraversalDerived
