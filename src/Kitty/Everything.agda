module Kitty.Everything where

import Kitty

import Kitty.Term.Prelude
import Kitty.Term.Modes
import Kitty.Term.Kit
import Kitty.Term.KitOrder
import Kitty.Term.Sub
import Kitty.Term.Traversal
import Kitty.Term.KitT
import Kitty.Term.KitHomotopy
import Kitty.Term.ComposeKit
import Kitty.Term.SubCompose
import Kitty.Term.ComposeTraversal
import Kitty.Term.MultiSub
import Kitty.Term.MultiTraversal
import Kitty.Term.MultiTraversalDerived
-- import Kitty.Term.Strengthen

import Kitty.Typing.CtxRepr
import Kitty.Typing.IKit
import Kitty.Typing.ITerms
import Kitty.Typing.OPE
import Kitty.Typing.TypeModes

import Kitty.Semantics.ISemantics

import Kitty.Util.Closures
import Kitty.Util.Star
import Kitty.Util.SubstProperties

import Kitty.Derive.Common
import Kitty.Derive.MultiTraversal

-- import Kitty.Experimental.Everything

import Kitty.Examples.SystemF-Derive.Definitions
import Kitty.Examples.SystemF-Derive.SubjectReduction
import Kitty.Examples.SystemF-Derive.Progress

import Kitty.Examples.LambdaPi-Derive.Definitions
import Kitty.Examples.LambdaPi-Derive.Confluence
-- import Kitty.Examples.LambdaPi-Derive.SubjectReduction
-- import Kitty.Examples.LambdaPi-Derive.Progress

import Kitty.Examples.LambdaPi-Derive-Sem.Definitions
import Kitty.Examples.LambdaPi-Derive-Sem.Confluence
-- import Kitty.Examples.LambdaPi-Derive-Sem.SubjectReduction
-- import Kitty.Examples.LambdaPi-Derive-Sem.Progress

import Kitty.Examples.LambdaPi-Derive-Sem-Eta.Definitions
-- import Kitty.Examples.LambdaPi-Derive-Sem-Eta.SubjectReduction
-- import Kitty.Examples.LambdaPi-Derive-Sem-Eta.Progress
-- import Kitty.Examples.LambdaPi-Derive-Sem-Eta.Confluence

-- import Kitty.Examples.LambdaPiPat-Derive-Sem.Definitions
-- import Kitty.Examples.LambdaPiPat-Derive-Sem.SubjectReduction
-- import Kitty.Examples.LambdaPiPat-Derive-Sem.Progress
-- import Kitty.Examples.LambdaPiPat-Derive-Sem.Confluence

import Kitty.Examples.LambdaPiSigma-Derive-Sem.Definitions
import Kitty.Examples.LambdaPiSigma-Derive-Sem.SubjectReduction
-- import Kitty.Examples.LambdaPiSigma-Derive-Sem.Progress
import Kitty.Examples.LambdaPiSigma-Derive-Sem.Confluence

import Kitty.Examples.MutRef-Derive.Definitions
-- import Kitty.Examples.MutRef-Derive.SubjectReduction
-- import Kitty.Examples.MutRef-Derive.Progress

import Kitty.Examples.STLC-Derive.Definitions
import Kitty.Examples.STLC-Derive.SubjectReduction
import Kitty.Examples.STLC-Derive.Progress

-- import Kitty.Examples.STLC-Kits.Definitions
-- import Kitty.Examples.STLC-Kits.SubjectReduction
-- import Kitty.Examples.STLC-Kits.Progress

-- import Kitty.Examples.STLC-Pat-Derive.Definitions
-- import Kitty.Examples.STLC-Pat-Derive.SubjectReduction
-- import Kitty.Examples.STLC-Pat-Derive.Progress
