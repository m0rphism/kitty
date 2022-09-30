module Everything where

-- Library ---------------------------------------------------------------------

import Kitty.Prelude
import Kitty.Modes
import Kitty.Kit
import Kitty.Compose
import Kitty.Types
import Kitty.OPE
import Kitty.Generics
import Kitty.GenericsDerive
import Kitty.Generics-Example -- TODO
import Kitty.GenericsDeriveExamples
import Kitty.Classes
import Kitty.Derive.Common
import Kitty.Derive.Desc
import Kitty.Derive.To
import Kitty.Derive.From
import Kitty.Derive.ToFrom
import Kitty.Derive.FromTo
import Kitty.Derive.Iso

-- Alternative formulation using the agda-stdlib approach.
import Kitty.KitAlt
import Kitty.KitAltSimple

-- Kits for deriving Substitution-Preserves-Typing for Typing
-- Relations in standard form i.e. `Γ ⊢ e ∶ t`.
import Kitty.ITerms
-- import Kitty.IKit

-- import Kitty.ComposeCat

-- Examples --------------------------------------------------------------------

import Examples.ISession.Definitions
import Examples.ISession.Substitution
-- import Examples.ISession.Typing

-- import Examples.LambdaPi-Kits.Definitions-ValueMode
import Examples.LambdaPi-Kits.Definitions
import Examples.LambdaPi-Kits.EvalLemmas
-- import Examples.LambdaPi-Kits.SubjectReduction

import Examples.LinearSTLC.Definitions

import Examples.STLC.Definitions
-- import Examples.STLC.Normalization
import Examples.STLC.Progress
import Examples.STLC.SubjectReduction

import Examples.STLC-CBV.Definitions
import Examples.STLC-CBV.Normalization
import Examples.STLC-CBV.Progress
-- import Examples.STLC-CBV.SemSoundness
import Examples.STLC-CBV.SubjectReduction

import Examples.STLC-CBV-NoTySubst.Definitions
import Examples.STLC-CBV-NoTySubst.Normalization
import Examples.STLC-CBV-NoTySubst.Progress
import Examples.STLC-CBV-NoTySubst.SubjectReduction

import Examples.STLC-Rec.Definitions
import Examples.STLC-Rec.SubjectReduction
-- import Examples.STLC-Rec.LR-Safety-MutRec
-- import Examples.STLC-Rec.LR-Safety-NoUniv
-- import Examples.STLC-Rec.LR-Safety.bak
-- import Examples.STLC-Rec.LR-Safety.bak.post-µ-removal
-- import Examples.STLC-Rec.LR-Safety

import Examples.STLCRef.Definitions
-- import Examples.STLCRef.SubjectReduction

import Examples.SystemF-Kits.Definitions
import Examples.SystemF-Kits.Definitions-KitAlt
import Examples.SystemF-Kits.Progress
import Examples.SystemF-Kits.Soundness-Bigstep
import Examples.SystemF-Kits.SubjectReduction

import Examples.SystemF-Kits-Uniform.Definitions
import Examples.SystemF-Kits-Uniform.Progress
import Examples.SystemF-Kits-Uniform.SubjectReduction

import Examples.SystemF-Raw.Definitions
import Examples.SystemF-Raw.SubjectReduction

-- import Examples.SystemF-TypingKits.Definitions
-- import Examples.SystemF-TypingKits.SubjectReduction
-- import Examples.SystemF-TypingKits.Progress

import Examples.SystemFLin-Kits.Definitions
-- import Examples.SystemFLin-Kits.SubjectReduction
-- import Examples.SystemFLin-Kits.Progress
