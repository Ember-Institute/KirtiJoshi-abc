import Definitions.Def_FermatBelyiConductorExtensionFinitePlaces
import Solutions.Source_ReferenceIutPointModuliMap
import Solutions.Source_TripodRelativeDegreeSum
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

open NumberField
open Tripod.Fermat.Proper.ConductorExtensionSource (placesOver mem_placesOver)
open scoped BigOperators

universe u

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}

/-- The signed q-pilot of the P7 variant with the finite-place weight of IUT III,
Remark 3.1.1(ii). The inner sum includes every moduli place over the rational place `vQ`. -/
theorem pointThetaData_qPilot_lhs_eq_sum_section_log_norm_with_fiber_weight
    (CI : CurveInputs.{u} T AG K d) (anab : AnabelianExistence AG TG)
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
      let M := ↥(fieldOfModuli P.data.F P.data.E)
      letI : Algebra M P.data.Kt := P.data.algebraModK
      (concreteVariantData P.data P.localTheory TL P.qPilotInputs).qPilot.lhs =
        ∑ v ∈ P.qPilotInputs.badModuliFinset,
          let vQ := Tripod.placeUnder (k := ℚ) v
          (1 / ((Tripod.relLocalDeg (P.data.localData.sect.sectFin v) v : ℝ) *
            (∑ u ∈ placesOver M vQ, (Tripod.relLocalDeg u vQ : ℝ)))) *
            Real.log ‖TL.qroot (P.data.localData.sect.sectFin v)‖ := by
  intro P htwo
  let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
  let M := ↥(fieldOfModuli P.data.F P.data.E)
  let _ : Algebra M P.data.Kt := P.data.algebraModK
  change (concreteVariantData P.data P.localTheory TL P.qPilotInputs).qPilot.lhs = _
  rw [CI.pointThetaData_qPilot_lhs_eq_sum_section_log_norm anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    htwo, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  let vQ := Tripod.placeUnder (k := ℚ) v
  have hsum : (∑ u ∈ placesOver M vQ, (Tripod.relLocalDeg u vQ : ℝ)) =
      (Module.finrank ℚ M : ℝ) := by
    rw [← Nat.cast_sum, Tripod.sum_relLocalDeg_liesOver vQ (placesOver M vQ)
      (fun _ => mem_placesOver)]
  change _ = (1 / ((Tripod.relLocalDeg (P.data.localData.sect.sectFin v) v : ℝ) *
    (∑ u ∈ placesOver M vQ, (Tripod.relLocalDeg u vQ : ℝ)))) *
    Real.log ‖TL.qroot (P.data.localData.sect.sectFin v)‖
  rw [hsum, div_div, one_div_mul_eq_div]

end AbcAdaptation.Reference.Iut.CurveInputs
