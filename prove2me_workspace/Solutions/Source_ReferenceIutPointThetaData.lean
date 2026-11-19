/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Tripod/Main.lean
-/
import Solutions.Source_ReferenceIutCurveTateFamily
import Solutions.Source_ReferenceIutQPilot

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

open NumberField
open scoped Classical

universe u

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}

/-- The initial Θ-data of a chosen curve and prime, with the arithmetic identities of P7. -/
structure PointThetaData (CI : CurveInputs.{u} T AG K d)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d) (ℓ : ℕ) where
  data : InitialThetaData AG TG
  qPilotInputs : QPilotInputs data
  prime_eq : data.ℓ = ℓ
  dmod_le : Module.finrank ℚ ↥(fieldOfModuli data.F data.E) ≤ d
  logQ_eq : qPilotInputs.qPilot.logQ = (CI.toCorollary22Inputs.localData x hx).heightOther 2 ℓ
  logDiff_eq : T.logDiff T.tripod x = logDifferentDeg ↥(tripodalFieldOf data.F data.E)
  logCond_ge : logConductorDegOf data.F data.E data.VBad ≤ T.logCond T.tripod x
  logCond_le : T.logCond T.tripod x ≤ logConductorDegOf data.F data.E data.VBad + Real.log (2 * ℓ)

/-- Construct the initial Θ-data at the selected curve and prime so local arithmetic can
use its curve and torsion-field projections. -/
noncomputable def pointThetaData (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
    (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
    (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
        (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
    (hsl : CI.toCorollary22Inputs.SL2Image x ℓ) :
    PointThetaData (TG := TG) CI x hx ℓ := by
  have hcore : OrbicurveDataSection.HasCoreUniversally AG (CI.curve x hx).F
      (CI.curve x hx).E := by
    by_contra h
    exact hxe ⟨hx, h⟩
  have hP2' : ∀ w (hw : w ∈ (CI.curve x hx).badAll), ¬ ℓ ∣ (CI.tate x hx).qOrder w hw := by
    intro w hw
    have h := hP2 w ((CI.arith x hx).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (CI.curve x hx).badAll then (CI.tate x hx).qOrder w h else 0) at h
    rwa [dif_pos hw] at h
  have hP5' : ∃ w ∈ (CI.curve x hx).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (CI.arith x hx).badAll_finite.mem_toFinset.mp hw, h⟩
  let R := CI.modRep x hx ℓ hℓ
  let TF := R.tateFamily hℓ (ne_of_gt ((by decide : 2 < 7).trans_le h7))
  let D := (CI.curve x hx).thetaData (CI.arith x hx) (CI.tate x hx) hℓ h7 R
    (hsl hx hℓ) hP2' hP5' TF anab hcore
  let QI : QPilotInputs D := (CI.curve x hx).qPilotInputs (CI.arith x hx) (CI.tate x hx)
    hℓ h7 R (hsl hx hℓ) hP2' hP5' TF anab hcore
  refine ⟨D, QI, rfl, CI.dmod_le x hx, ?_, CI.logDiff_eq x hx,
    CI.logCond_ge x hx ℓ hℓ h7, CI.logCond_le x hx ℓ hℓ h7⟩
  exact (CI.curve x hx).logQ_eq (CI.arith x hx) (CI.tate x hx) hℓ h7 R
    (hsl hx hℓ) hP2' hP5' TF anab hcore

/-- The initial Θ-data and its arithmetic identities at a point of Corollary 2.2.
The supplied geometry contract produces the orbicurve and dependent local data. -/
theorem exists_initialThetaData (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
    (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
    (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
        (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
    (hsl : CI.toCorollary22Inputs.SL2Image x ℓ) :
    ∃ (D : InitialThetaData AG TG) (QI : QPilotInputs D),
      D.ℓ = ℓ ∧ Module.finrank ℚ ↥(fieldOfModuli D.F D.E) ≤ d ∧
      QI.qPilot.logQ = (CI.toCorollary22Inputs.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = logDifferentDeg ↥(tripodalFieldOf D.F D.E) ∧
      logConductorDegOf D.F D.E D.VBad ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ logConductorDegOf D.F D.E D.VBad + Real.log (2 * ℓ) := by
  let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  exact ⟨P.data, P.qPilotInputs, P.prime_eq, P.dmod_le, P.logQ_eq,
    P.logDiff_eq, P.logCond_ge, P.logCond_le⟩

end AbcAdaptation.Reference.Iut.CurveInputs
