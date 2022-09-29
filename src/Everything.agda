module Everything where

-- Library ---------------------------------------------------------------------

import KitTheory.Prelude
import KitTheory.Modes
import KitTheory.Kit
import KitTheory.Compose
import KitTheory.Types
import KitTheory.OPE
import KitTheory.Generics
import KitTheory.GenericsDerive
import KitTheory.Generics-Example -- TODO
import KitTheory.GenericsDeriveExamples
import KitTheory.Classes
import KitTheory.Derive.Common
import KitTheory.Derive.Desc
import KitTheory.Derive.To
import KitTheory.Derive.From
import KitTheory.Derive.ToFrom
import KitTheory.Derive.FromTo
import KitTheory.Derive.Iso

-- Alternative formulation using the agda-stdlib approach.
import KitTheory.KitAlt
import KitTheory.KitAltSimple

-- Kits for deriving Substitution-Preserves-Typing for Typing
-- Relations in standard form i.e. `Γ ⊢ e ∶ t`.
import KitTheory.ITerms
-- import KitTheory.IKit

-- import KitTheory.ComposeCat

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
