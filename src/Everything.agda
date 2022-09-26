module Everything where

-- Library ---------------------------------------------------------------------

open import KitTheory.Prelude using ()
open import KitTheory.Modes using ()
open import KitTheory.Kit using ()
open import KitTheory.Compose using ()
open import KitTheory.Types using ()
open import KitTheory.OPE using ()
open import KitTheory.Generics using ()
open import KitTheory.GenericsDerive using ()
open import KitTheory.Generics-Example using () -- TODO
open import KitTheory.GenericsDeriveExamples using ()
open import KitTheory.Classes using ()

-- Alternative formulation using the agda-stdlib approach.
open import KitTheory.KitAlt using ()
open import KitTheory.KitAltSimple using ()

-- Kits for deriving Substitution-Preserves-Typing for Typing
-- Relations in standard form i.e. `Γ ⊢ e ∶ t`.
open import KitTheory.ITerms using ()
-- open import KitTheory.IKit using ()

-- open import KitTheory.ComposeCat using ()

-- Examples --------------------------------------------------------------------

open import Examples.ISession.Definitions using ()
open import Examples.ISession.Substitution using ()
-- open import Examples.ISession.Typing using ()

-- open import Examples.LambdaPi-Kits.Definitions-ValueMode using ()
open import Examples.LambdaPi-Kits.Definitions using ()
open import Examples.LambdaPi-Kits.EvalLemmas using ()
-- open import Examples.LambdaPi-Kits.SubjectReduction using ()

open import Examples.LinearSTLC.Definitions using ()

open import Examples.STLC.Definitions using ()
-- open import Examples.STLC.Normalization using ()
open import Examples.STLC.Progress using ()
open import Examples.STLC.SubjectReduction using ()

open import Examples.STLC-CBV.Definitions using ()
open import Examples.STLC-CBV.Normalization using ()
open import Examples.STLC-CBV.Progress using ()
-- open import Examples.STLC-CBV.SemSoundness using ()
open import Examples.STLC-CBV.SubjectReduction using ()

open import Examples.STLC-CBV-NoTySubst.Definitions using ()
open import Examples.STLC-CBV-NoTySubst.Normalization using ()
open import Examples.STLC-CBV-NoTySubst.Progress using ()
open import Examples.STLC-CBV-NoTySubst.SubjectReduction using ()

open import Examples.STLC-Rec.Definitions using ()
open import Examples.STLC-Rec.SubjectReduction using ()
-- open import Examples.STLC-Rec.LR-Safety-MutRec using ()
-- open import Examples.STLC-Rec.LR-Safety-NoUniv using ()
-- open import Examples.STLC-Rec.LR-Safety.bak using ()
-- open import Examples.STLC-Rec.LR-Safety.bak.post-µ-removal using ()
-- open import Examples.STLC-Rec.LR-Safety using ()

open import Examples.STLCRef.Definitions using ()
-- open import Examples.STLCRef.SubjectReduction using ()

open import Examples.SystemF-Kits.Definitions using ()
open import Examples.SystemF-Kits.Definitions-KitAlt using ()
open import Examples.SystemF-Kits.Progress using ()
open import Examples.SystemF-Kits.Soundness-Bigstep using ()
open import Examples.SystemF-Kits.SubjectReduction using ()

open import Examples.SystemF-Kits-Uniform.Definitions using ()
open import Examples.SystemF-Kits-Uniform.Progress using ()
open import Examples.SystemF-Kits-Uniform.SubjectReduction using ()

open import Examples.SystemF-Raw.Definitions using ()
open import Examples.SystemF-Raw.SubjectReduction using ()

-- open import Examples.SystemF-TypingKits.Definitions using ()
-- open import Examples.SystemF-TypingKits.SubjectReduction using ()
-- open import Examples.SystemF-TypingKits.Progress using ()

open import Examples.SystemFLin-Kits.Definitions using ()
-- open import Examples.SystemFLin-Kits.SubjectReduction using ()
-- open import Examples.SystemFLin-Kits.Progress using ()
