import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutCurveTateFamily
import Solutions.Source_ReferenceIutCurveThetaInputs

set_option autoImplicit false

#print axioms AbcAdaptation.Reference.Iut.TateFamily.ofStructures
#print axioms AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData.tateFamily

open AbcAdaptation.Reference.Iut

universe u

noncomputable example (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw) :
    let P := C.primeData CA TI hℓ h7 R hsl hP2
    letI : NumberField ↥P.torsionField := R.numberField_torsionField
    TateFamily C.E P.torsionField P.ℓ (C.VBadOf ℓ) :=
  R.tateFamily hℓ hodd
