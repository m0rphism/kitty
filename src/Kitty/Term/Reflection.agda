{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Term.Reflection where

open import Kitty.Term.Reflection.MultiTraversal public renaming (derive-MultiTraversal to derive)

import Kitty.Term.MultiTraversalDerived
module Derived = Kitty.Term.MultiTraversalDerived
