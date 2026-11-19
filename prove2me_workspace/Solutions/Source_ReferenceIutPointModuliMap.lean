import Solutions.Source_ReferenceIutCor312RepresentativeQPilot
import Solutions.Source_ReferenceIutPointLocalTheta

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

open scoped BigOperators

universe u

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}

/-- The stored moduli-field map of the P7 initial data is the composite of the inclusions. -/
theorem pointThetaData_algebraMap_moduli_torsion (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
    (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
    (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
        (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
    (hsl : CI.toCorollary22Inputs.SL2Image x ℓ) :
    let D := (CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl).data
    @algebraMap ↥(fieldOfModuli D.F D.E) ↥D.prime.torsionField _ _ D.algebraModK =
      (algebraMap D.F ↥D.prime.torsionField).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F) :=
  RingHom.ext fun _ => rfl

/-- The signed q-pilot of the P7 variant is the weighted log sum at the chosen places. -/
theorem pointThetaData_qPilot_lhs_eq_sum_section_log_norm (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
    (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
    (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
      (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
        (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
    (hsl : CI.toCorollary22Inputs.SL2Image x ℓ) :
    let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    ∀ htwo : TwoTorsionRational P.data,
      let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
      letI : Algebra ↥(fieldOfModuli P.data.F P.data.E) P.data.Kt := P.data.algebraModK
      (concreteVariantData P.data P.localTheory TL P.qPilotInputs).qPilot.lhs =
        (∑ v ∈ P.qPilotInputs.badModuliFinset,
          Real.log ‖TL.qroot (P.data.localData.sect.sectFin v)‖ /
            (Tripod.relLocalDeg (P.data.localData.sect.sectFin v) v : ℝ)) /
          (Module.finrank ℚ ↥(fieldOfModuli P.data.F P.data.E) : ℝ) := by
  intro P htwo
  let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
  exact TL.qPilot_lhs_eq_sum_section_log_norm P.qPilotInputs
    (CI.pointThetaData_algebraMap_moduli_torsion anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl)

end AbcAdaptation.Reference.Iut.CurveInputs
