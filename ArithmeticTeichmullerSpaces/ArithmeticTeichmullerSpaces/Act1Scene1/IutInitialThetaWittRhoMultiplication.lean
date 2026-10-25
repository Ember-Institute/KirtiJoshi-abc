import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitMultiplication
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoValue

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-MULTIPLICATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
rho-weighted expansions of the bounded period subring.
fidelity: applies the finite-monomial multiplication estimate with the
actual tilt integer ring, and transports it through actual p-power
presentations to the bounded Witt localization. The multiplication bound
is proved, not supplied as a source law. Original proofs.
boundary: Scene1/Derived; multiplicative equality, Frobenius continuity
and Frechet completion remain open. No completed B or BK identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoMultiplication

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem fieldWitt_value_mul_le (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : FieldWitt D w) :
    WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (x * y) ≤
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ x *
        WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y :=
  WittWeightedDigitMultiplication.value_mul_le (Arithmetic.residueChar w.1)
    (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
    (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w)) ρ hρ x y

theorem value_mul_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w ρ (x * y) ≤
      InitialThetaWittRhoValue.value D w ρ x * InitialThetaWittRhoValue.value D w ρ y := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := InitialThetaWittRhoValue.presentation D w x
  let Q := InitialThetaWittRhoValue.presentation D w y
  let m := P.exponent + Q.exponent
  have he : toAmbient D w (x * y) * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) (P.numerator * Q.numerator) := by
    rw [map_mul, map_mul]
    change (toAmbient D w x * toAmbient D w y) *
      (Arithmetic.residueChar w.1 : Ambient D w) ^ (P.exponent + Q.exponent) = _
    rw [pow_add]
    calc
      _ = (toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ P.exponent) *
          (toAmbient D w y * (Arithmetic.residueChar w.1 : Ambient D w) ^ Q.exponent) :=
        mul_mul_mul_comm _ _ _ _
      _ = _ := by rw [P.relation, Q.relation]
  rw [InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop _ m _ he,
    InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop x
      P.exponent P.numerator P.relation,
    InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop y
      Q.exponent Q.numerator Q.relation]
  calc
    _ ≤ (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ P.numerator *
          WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ Q.numerator) / ρ ^ m :=
      mul_le_mul_of_nonneg_right (a := (ρ ^ m)⁻¹)
        (fieldWitt_value_mul_le D w ρ hρ1 P.numerator Q.numerator) bot_le
    _ = _ := by
      simp only [div_eq_mul_inv, ENNReal.inv_pow]
      dsimp only [m]
      rw [pow_add]
      exact mul_mul_mul_comm
        (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ P.numerator)
        (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ Q.numerator)
        ((ρ⁻¹) ^ P.exponent) ((ρ⁻¹) ^ Q.exponent)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoMultiplication
