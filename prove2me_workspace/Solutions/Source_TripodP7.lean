/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/Main.lean and Iut/Tripod/Tower.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBound
import Solutions.Source_ReferenceIutPointLocalTheta
import Solutions.Source_ReferenceIutTowerArithmetic
import Solutions.Source_TripodCurveInputsFromSource
import Solutions.Source_TripodTowerLocalFacts
import Solutions.Source_TripodTwoTorsion

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut WeierstrassCurve
open scoped Classical

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- For every admissible point and prime, the Legendre curve supplies concrete local theta data
and tower arithmetic on the torsion field of the selected initial data. -/
theorem concreteThetaDataExistence_from_source (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (anab : AnabelianExistence AG TG) :
    ConcreteThetaDataExistence.{0, 0} (AG := AG) (TG := TG)
      (curveInputs_from_source P K d CF hcore hN (legendreHeight P K)
        (twoAdicBound P K)).toCorollary22Inputs := by
  let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
  have htwo (x : tripodTheory.Pt tripodTheory.tripod)
      (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
      2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (CI.curve x hx).E.toAffine.Point ((2 : ℕ) : ℤ)) :=
    two_torsion_curveOf x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  refine CI.concreteThetaDataExistence_of_localArithmetic anab htwo ?_
  intro x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  let X := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  let TL := X.localThetaData (htwo x hx)
  change TowerArithmetic X.data X.localTheory (TL.withBadChars X.qPilotInputs)
  have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
    intro w hw
    have h := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at h
    rwa [dif_pos hw] at h
  letI : IsGalois ↥(fieldOfModuli X.data.F X.data.E) ↥X.data.tripodalField :=
    isGalois_tpd_of_curve P x
  have H : TowerLocalFacts X.data.E X.data.VBad X.data.prime :=
    towerLocalFacts_of_primeData P x hℓ h7 (hsl hx hℓ) hP2'
  refine towerArithmetic_of_localFacts X.data X.localTheory (TL.withBadChars X.qPilotInputs)
    H (relRamIdxModLeTwo_curve P x ℓ) ?_ ?_ X.qPilotInputs.bad_finite
    (TL.exists_badPlace_of_mem_withBadChars X.qPilotInputs)
  · exact finrank_tpd_le_six x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  · let p : Pt := x
    calc
      Module.finrank ℚ (P.curve p).F ≤ 552960 * deg p.1 :=
        deg_le p (P.torsionFinite3 p.1) (P.torsionFinite5 p.1)
          (torsionDegreeBound_three' p) (torsionDegreeBound_five' p)
      _ = 552960 * Module.finrank ℚ (tpd P p) :=
        congrArg (552960 * ·) (finrank_tpd P p).symm

end AbcAdaptation.Tripod
