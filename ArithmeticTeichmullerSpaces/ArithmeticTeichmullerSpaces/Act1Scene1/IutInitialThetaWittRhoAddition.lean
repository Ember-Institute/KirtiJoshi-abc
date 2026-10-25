import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitAddition
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoValue

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-ADDITION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
rho-norm addition estimate for bounded period elements.
fidelity: uses the actual tilt integer ring to control Witt carries, then
passes to common p-power denominators to prove the ultrametric addition
inequality for the actual localization value. No addition law is supplied
by the caller. Original proofs; no reference code copied.
boundary: Scene1/Derived; multiplication estimates and Frechet completion
remain open. No completed period-ring or BK identification is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoAddition

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

theorem fieldWitt_value_add_le_max (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : FieldWitt D w) :
    WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (x + y) ≤
      max (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ x)
        (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y) :=
  WittWeightedDigitAddition.value_add_le_max (Arithmetic.residueChar w.1)
    (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
    (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w)) ρ hρ x y

private theorem extend_presentation (x : InitialThetaBoundedWittLocalization.Ring D w)
    (P : InitialThetaWittRhoValue.Presentation D w x) (k : ℕ) :
    toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ (P.exponent + k) =
      algebraMap (FieldWitt D w) (Ambient D w)
        (P.numerator * (Arithmetic.residueChar w.1 : FieldWitt D w) ^ k) := by
  rw [map_mul, map_pow, map_natCast, pow_add, ← mul_assoc, P.relation]

theorem value_add_le_max (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w ρ (x + y) ≤
      max (InitialThetaWittRhoValue.value D w ρ x) (InitialThetaWittRhoValue.value D w ρ y) := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := InitialThetaWittRhoValue.presentation D w x
  let Q := InitialThetaWittRhoValue.presentation D w y
  let m := P.exponent + Q.exponent
  let a := P.numerator * (Arithmetic.residueChar w.1 : FieldWitt D w) ^ Q.exponent
  let b := Q.numerator * (Arithmetic.residueChar w.1 : FieldWitt D w) ^ P.exponent
  have ha : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) a :=
    extend_presentation D w x P Q.exponent
  have hb : toAmbient D w y * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) b := by
    simpa only [m, Nat.add_comm] using extend_presentation D w y Q P.exponent
  have hs : toAmbient D w (x + y) * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) (a + b) := by
    rw [map_add, add_mul, ha, hb, map_add]
  have hx := InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop x m a ha
  have hy := InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop y m b hb
  rw [InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop _ m (a + b) hs]
  calc
    _ ≤ max (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ a)
          (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ b) / ρ ^ m :=
      mul_le_mul_of_nonneg_right (a := (ρ ^ m)⁻¹)
        (fieldWitt_value_add_le_max D w ρ hρ1 a b) bot_le
    _ = _ := by
      rw [div_eq_mul_inv, max_mul_of_nonneg _ _ (bot_le : (0 : ℝ≥0∞) ≤ (ρ ^ m)⁻¹)]
      simpa only [div_eq_mul_inv] using congrArg₂ max hx.symm hy.symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoAddition
