/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Anabelian/Local.lean and Iut/Anabelian/Geometry.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_LocalConditions
import Solutions.Source_TripodCoreModel

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.ReferenceIut.Anabelian (Orbicurve EtalePi1Theory)
open scoped Classical Valued

universe u

/-- The tempered fundamental groups of the model orbicurves and their continuous comparisons
with the specified étale fundamental groups. -/
structure TemperedPi1Theory (Pi1 : EtalePi1Theory.{u}) : Type (u + 1) where
  tempPi1 : {k : Type u} → [Field k] → Orbicurve k → Type u
  tempPi1Group : ∀ {k : Type u} [Field k] (X : Orbicurve k), Group (tempPi1 X)
  tempPi1Topology : ∀ {k : Type u} [Field k] (X : Orbicurve k), TopologicalSpace (tempPi1 X)
  tempToEtale : ∀ {k : Type u} [Field k] (X : Orbicurve k),
    letI := tempPi1Group X; tempPi1 X →* Pi1.pi1 X
  tempToEtale_continuous : ∀ {k : Type u} [Field k] (X : Orbicurve k),
    letI := tempPi1Group X; letI := tempPi1Topology X
    Continuous (tempToEtale X)

/-- The cusp of a canonical generator of the Tate graph quotient, with the cusp of zero as
the default when there is no such generator. -/
noncomputable def canonicalGraphCusp {k : Type u} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
    [CompleteSpace k] (X : Orbicurve k) (S : TateStructure X.E) : X.Cusp :=
  if h : ∃ P : ↥X.torsion, S.IsCanonical X.level P.1 then X.cuspOf (X.toQ h.choose)
  else X.cuspOf 0

/-- The model geometry with the supplied tempered comparison, the Tate graph line condition
for theta-root models, and the corresponding canonical cusp. -/
noncomputable def modelTG (Pi1 : EtalePi1Theory.{u}) (T : TemperedPi1Theory Pi1) :
    TemperedGeometry (modelAG Pi1) where
  tempPi1 := T.tempPi1
  tempPi1Group := T.tempPi1Group
  tempPi1Topology := T.tempPi1Topology
  tempToEtale := T.tempToEtale
  tempToEtale_continuous := T.tempToEtale_continuous
  IsThetaRootModel := (modelAG Pi1).IsTypeOneZModPM
  canonicalGraphCusp := canonicalGraphCusp

end AbcAdaptation.Reference.Iut.Anabelian
