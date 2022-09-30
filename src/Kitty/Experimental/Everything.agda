module Kitty.Experimental.Everything where

import Kitty.Experimental.Classes

-- Alternative formulation using the agda-stdlib approach.
import Kitty.Experimental.KitAlt
import Kitty.Experimental.KitAltSimple

-- Kits for deriving Substitution-Preserves-Typing for Typing
-- Relations in standard form i.e. `Γ ⊢ e ∶ t`.
import Kitty.Experimental.ITerms
-- import Kitty.Experimental.IKit

-- import Kitty.Experimental.ComposeCat

import Kitty.Experimental.Examples.STLC-CBV.Definitions
import Kitty.Experimental.Examples.STLC-CBV.Normalization
import Kitty.Experimental.Examples.STLC-CBV.Progress
-- import Kitty.Experimental.Examples.STLC-CBV.SemSoundness
import Kitty.Experimental.Examples.STLC-CBV.SubjectReduction

import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Definitions
import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Normalization
import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.Progress
import Kitty.Experimental.Examples.STLC-CBV-NoTySubst.SubjectReduction

import Kitty.Experimental.Examples.STLC-Rec.Definitions
import Kitty.Experimental.Examples.STLC-Rec.SubjectReduction
-- import Kitty.Experimental.Examples.STLC-Rec.LR-Safety-MutRec
-- import Kitty.Experimental.Examples.STLC-Rec.LR-Safety-NoUniv
-- import Kitty.Experimental.Examples.STLC-Rec.LR-Safety.bak
-- import Kitty.Experimental.Examples.STLC-Rec.LR-Safety.bak.post-µ-removal
-- import Kitty.Experimental.Examples.STLC-Rec.LR-Safety

import Kitty.Experimental.Examples.ISession.Definitions
import Kitty.Experimental.Examples.ISession.Substitution
-- import Kitty.Experimental.Examples.ISession.Typing

-- import Kitty.Experimental.Examples.LambdaPi-Kits.Definitions-ValueMode
import Kitty.Experimental.Examples.LambdaPi-Kits.Definitions
import Kitty.Experimental.Examples.LambdaPi-Kits.EvalLemmas
-- import Kitty.Experimental.Examples.LambdaPi-Kits.SubjectReduction

import Kitty.Experimental.Examples.LinearSTLC.Definitions

import Kitty.Experimental.Examples.STLC.Definitions
import Kitty.Experimental.Examples.STLC.Progress
import Kitty.Experimental.Examples.STLC.SubjectReduction

import Kitty.Experimental.Examples.STLCRef.Definitions
-- import Kitty.Experimental.Examples.STLCRef.SubjectReduction

-- import Kitty.Experimental.Examples.SystemF-TypingKits.Definitions
-- import Kitty.Experimental.Examples.SystemF-TypingKits.SubjectReduction
-- import Kitty.Experimental.Examples.SystemF-TypingKits.Progress

import Kitty.Experimental.Examples.SystemFLin-Kits.Definitions
-- import Kitty.Experimental.Examples.SystemFLin-Kits.SubjectReduction
-- import Kitty.Experimental.Examples.SystemFLin-Kits.Progress

import Kitty.Experimental.Examples.SystemF-Kits.Definitions
import Kitty.Experimental.Examples.SystemF-Kits.Definitions-KitAlt
import Kitty.Experimental.Examples.SystemF-Kits.Progress
import Kitty.Experimental.Examples.SystemF-Kits.Soundness-Bigstep
import Kitty.Experimental.Examples.SystemF-Kits.SubjectReduction

import Kitty.Experimental.Examples.SystemF-Kits-Uniform.Definitions
import Kitty.Experimental.Examples.SystemF-Kits-Uniform.Progress
import Kitty.Experimental.Examples.SystemF-Kits-Uniform.SubjectReduction

import Kitty.Experimental.Examples.SystemF-Raw.Definitions
import Kitty.Experimental.Examples.SystemF-Raw.SubjectReduction
