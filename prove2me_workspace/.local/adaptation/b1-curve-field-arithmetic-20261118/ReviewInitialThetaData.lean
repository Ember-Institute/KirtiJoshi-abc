import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutInitialThetaData

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u

#print axioms AnabelianExistence
#print axioms EllipticCurveData.thetaData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
  (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
  (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (TF : TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ))
  (anab : AnabelianExistence AG TG) (hcore : OrbicurveDataSection.HasCoreUniversally AG C.F C.E)

example :
    let D := C.thetaData CA TI hℓ h7 R hsl hP2 hP5 TF anab hcore
    D.prime.torsionField = R.torsionField ∧
    D.prime.rep = R.rep ∧ D.tate = TF ∧
    (letI := D.algebraModK
     algebraMap ↥(fieldOfModuli C.F C.E) ↥R.torsionField =
       (algebraMap C.F ↥R.torsionField).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact RingHom.ext fun _ => rfl

end AbcAdaptation.Reference.Iut
