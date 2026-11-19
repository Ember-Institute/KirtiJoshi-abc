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

/-- The variant data obtained from the point and prime chosen in (P7). -/
def IsSourceP7Variant {K : CompactlyBounded} {d : ℕ}
    (CI : CurveInputs tripodTheory AG K d) (anab : AnabelianExistence AG TG)
    (X : Corollary312VariantData.{0, 0} AG TG) : Prop :=
  ∃ (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)
    (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓ7 : 7 ≤ ℓ)
    (hP2 : ∀ v ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv v)
    (_hP3 : ∀ v ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p v = ℓ →
      ((CI.toCorollary22Inputs.localData x hx).hv v : ℝ) < Real.sqrt (CI.toCorollary22Inputs.h x))
    (hP5 : ∃ v ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p v ≠ 2 ∧
        (CI.toCorollary22Inputs.localData x hx).p v ≠ ℓ)
    (hP6 : CI.toCorollary22Inputs.SL2Image x ℓ),
    let W := CI.pointThetaData anab x hx hxe ℓ hℓp hℓ7 hP2 hP5 hP6
    ∃ htwo : TwoTorsionRational W.data,
      X = concreteVariantData W.data W.localTheory
        ((W.localThetaData htwo).withBadChars W.qPilotInputs) W.qPilotInputs

private theorem sourceP7Existence (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (anab : AnabelianExistence AG TG) :
    let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
    ConcreteThetaDataExistence.{0, 0} (AG := AG) (TG := TG) CI.toCorollary22Inputs ∧
      ThetaDataExistence (IsSourceP7Variant CI anab) CI.toCorollary22Inputs := by
  let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
  have htwo (x : tripodTheory.Pt tripodTheory.tripod)
      (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
      2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (CI.curve x hx).E.toAffine.Point ((2 : ℕ) : ℤ)) :=
    two_torsion_curveOf x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)
  have tower :
      ∀ (x : tripodTheory.Pt tripodTheory.tripod)
        (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)
        (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
        (hP2 : ∀ v ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv v)
        (hP5 : ∃ v ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          (CI.toCorollary22Inputs.localData x hx).p v ≠ 2 ∧
            (CI.toCorollary22Inputs.localData x hx).p v ≠ ℓ)
        (hsl : CI.toCorollary22Inputs.SL2Image x ℓ),
        let W := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
        let TL := W.localThetaData (htwo x hx)
        TowerArithmetic W.data W.localTheory (TL.withBadChars W.qPilotInputs) := by
    intro x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    let X := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    let TL := X.localThetaData (htwo x hx)
    change TowerArithmetic X.data X.localTheory (TL.withBadChars X.qPilotInputs)
    have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
      intro w hw
      have h := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
      change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at h
      rwa [dif_pos hw] at h
    let _ : IsGalois ↥(fieldOfModuli X.data.F X.data.E) ↥X.data.tripodalField :=
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
  refine ⟨CI.concreteThetaDataExistence_of_localArithmetic anab htwo tower, ⟨?_⟩⟩
  intro x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
  let W := CI.pointThetaData anab x hx hxe ℓ hℓp hℓ7 hP2 hP5 hP6
  let TL := (W.localThetaData (htwo x hx)).withBadChars W.qPilotInputs
  let X := concreteVariantData W.data W.localTheory TL W.qPilotInputs
  have hsource : IsSourceP7Variant CI anab X :=
    ⟨x, hx, hxe, ℓ, hℓp, hℓ7, hP2, hP3, hP5, hP6, htwo x hx, rfl⟩
  have TA : TowerArithmetic W.data W.localTheory TL :=
    tower x hx hxe ℓ hℓp hℓ7 hP2 hP5 hP6
  have hseven : 7 ≤ W.data.ℓ := W.prime_eq.symm ▸ hℓ7
  exact ⟨X, TL.invariants W.qPilotInputs, hsource,
    TA.certificate (QI := W.qPilotInputs) hseven, ⟨TA.localEstimate (QI := W.qPilotInputs)⟩,
    W.prime_eq, W.dmod_le, W.logQ_eq, W.logDiff_eq, W.logCond_ge, W.logCond_le⟩

/-- For every admissible point and prime, the Legendre curve supplies concrete local theta data
and tower arithmetic on the torsion field of the selected initial data. -/
theorem concreteThetaDataExistence_from_source (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (anab : AnabelianExistence AG TG) :
    ConcreteThetaDataExistence.{0, 0} (AG := AG) (TG := TG)
      (curveInputs_from_source P K d CF hcore hN (legendreHeight P K)
        (twoAdicBound P K)).toCorollary22Inputs :=
  (sourceP7Existence P K d CF hcore hN anab).1

/-- The (P7) witness produced by the Legendre curve with its source construction recorded. -/
theorem pointThetaDataExistence_from_source (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {TK : ℝ} (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (anab : AnabelianExistence AG TG) :
    let CI := curveInputs_from_source P K d CF hcore hN (legendreHeight P K) (twoAdicBound P K)
    ThetaDataExistence (IsSourceP7Variant CI anab) CI.toCorollary22Inputs :=
  (sourceP7Existence P K d CF hcore hN anab).2

end AbcAdaptation.Tripod
