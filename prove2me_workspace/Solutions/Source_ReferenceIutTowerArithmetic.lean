/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Main.lean
-/
import Solutions.Source_ReferenceIutConcreteDifferentDegree
import Solutions.Source_ReferenceIutTowerDifferent
import Solutions.Source_ReferenceIutTowerRamIdx
import Solutions.Source_ReferenceIutTowerStepIIIForTheta

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)

/-- The three tower bounds for the same initial data and distinguished primes. -/
theorem towerArithmetic_of_localFacts (H : TowerLocalFacts D.E D.VBad D.prime)
    (he2 : RelRamIdxModLeTwo D.E D.VBad)
    [IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField]
    (h6 : Module.finrank ↥(fieldOfModuli D.F D.E) ↥D.tripodalField ≤ 6)
    (hF : Module.finrank ℚ D.F ≤ 552960 * Module.finrank ℚ ↥D.tripodalField)
    (hfin : (badPlacesOver D.F D.E D.VBad).Finite)
    (hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p) :
    TowerArithmetic D LT TL where
  ramIdx_bound v hv := ramIdx_bound_of_facts H h6 hF v hv
  step_ii := by
    rw [TL.sum_dst_logDK_eq]
    exact logDifferentDeg_torsionField_le D.prime H hfin
  step_iii := TL.step_iii_of_localFacts H he2 hfin hbad

end AbcAdaptation.Reference.Iut
