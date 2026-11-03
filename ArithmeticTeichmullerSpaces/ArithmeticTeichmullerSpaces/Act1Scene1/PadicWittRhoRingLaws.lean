import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoValue
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitAddition
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitMultiplication
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitNegation

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-RING-LAWS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
weighted Teichmuller values on the standard bounded Witt localization.
fidelity: proves the ultrametric addition bound, submultiplicativity and
negation invariance for the independent standard rho value. The proofs
reuse the project's original generic weighted digit laws and localization
presentation arguments, specialized to the standard tilt integer ring.
All declarations depend only on p and its primality instance. Original
proofs; no reference implementation copied.
boundary: Scene1/Derived; a real RingNorm, topology and completed paper B
comparison are separate constructions. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoValue

open PadicBoundedWittExpansion PadicBoundedWittLocalization
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance coefficientFieldRingLaws : Field (PadicTiltField.Carrier p) :=
  (PadicTiltField.carrierNormedField p).toField

theorem fieldWitt_value_add_le_max (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : FieldWitt p) :
    WittWeightedDigits.value p ρ (x + y) ≤
      max (WittWeightedDigits.value p ρ x)
        (WittWeightedDigits.value p ρ y) :=
  WittWeightedDigitAddition.value_add_le_max p
    (LocalGeometricFontaine.integerRing (PadicTiltField.Carrier p))
    (LocalGeometricFontaine.mem_integerRing (PadicTiltField.Carrier p)) ρ hρ x y

private theorem extend_presentation (x : PadicBoundedWittLocalization.Ring p)
    (P : Presentation p x) (k : ℕ) :
    toAmbient p x * (p : Ambient p) ^ (P.exponent + k) =
      algebraMap (FieldWitt p) (Ambient p)
        (P.numerator * (p : FieldWitt p) ^ k) := by
  rw [map_mul, map_pow, map_natCast, pow_add, ← mul_assoc, P.relation]

theorem value_add_le_max (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : PadicBoundedWittLocalization.Ring p) :
    value p ρ (x + y) ≤
      max (value p ρ x) (value p ρ y) := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := presentation p x
  let Q := presentation p y
  let m := P.exponent + Q.exponent
  let a := P.numerator * (p : FieldWitt p) ^ Q.exponent
  let b := Q.numerator * (p : FieldWitt p) ^ P.exponent
  have ha : toAmbient p x * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) a :=
    extend_presentation p x P Q.exponent
  have hb : toAmbient p y * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) b := by
    simpa only [m, Nat.add_comm] using extend_presentation p y Q P.exponent
  have hs : toAmbient p (x + y) * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) (a + b) := by
    rw [map_add, add_mul, ha, hb, map_add]
  have hx := value_eq_of_presentation p ρ hρ0 hρtop x m a ha
  have hy := value_eq_of_presentation p ρ hρ0 hρtop y m b hb
  rw [value_eq_of_presentation p ρ hρ0 hρtop _ m (a + b) hs]
  calc
    _ ≤ max (WittWeightedDigits.value p ρ a)
          (WittWeightedDigits.value p ρ b) / ρ ^ m :=
      mul_le_mul_of_nonneg_right (a := (ρ ^ m)⁻¹)
        (fieldWitt_value_add_le_max p ρ hρ1 a b) bot_le
    _ = _ := by
      rw [div_eq_mul_inv, max_mul_of_nonneg _ _ (bot_le : (0 : ℝ≥0∞) ≤ (ρ ^ m)⁻¹)]
      simpa only [div_eq_mul_inv] using congrArg₂ max hx.symm hy.symm

theorem fieldWitt_value_mul_le (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : FieldWitt p) :
    WittWeightedDigits.value p ρ (x * y) ≤
      WittWeightedDigits.value p ρ x *
        WittWeightedDigits.value p ρ y :=
  WittWeightedDigitMultiplication.value_mul_le p
    (LocalGeometricFontaine.integerRing (PadicTiltField.Carrier p))
    (LocalGeometricFontaine.mem_integerRing (PadicTiltField.Carrier p)) ρ hρ x y

theorem value_mul_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : PadicBoundedWittLocalization.Ring p) :
    value p ρ (x * y) ≤
      value p ρ x * value p ρ y := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := presentation p x
  let Q := presentation p y
  let m := P.exponent + Q.exponent
  have he : toAmbient p (x * y) * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) (P.numerator * Q.numerator) := by
    rw [map_mul, map_mul]
    change (toAmbient p x * toAmbient p y) *
      (p : Ambient p) ^ (P.exponent + Q.exponent) = _
    rw [pow_add]
    calc
      _ = (toAmbient p x * (p : Ambient p) ^ P.exponent) *
          (toAmbient p y * (p : Ambient p) ^ Q.exponent) :=
        mul_mul_mul_comm _ _ _ _
      _ = _ := by rw [P.relation, Q.relation]
  rw [value_eq_of_presentation p ρ hρ0 hρtop _ m _ he,
    value_eq_of_presentation p ρ hρ0 hρtop x
      P.exponent P.numerator P.relation,
    value_eq_of_presentation p ρ hρ0 hρtop y
      Q.exponent Q.numerator Q.relation]
  calc
    _ ≤ (WittWeightedDigits.value p ρ P.numerator *
          WittWeightedDigits.value p ρ Q.numerator) / ρ ^ m :=
      mul_le_mul_of_nonneg_right (a := (ρ ^ m)⁻¹)
        (fieldWitt_value_mul_le p ρ hρ1 P.numerator Q.numerator) bot_le
    _ = _ := by
      simp only [div_eq_mul_inv, ENNReal.inv_pow]
      dsimp only [m]
      rw [pow_add]
      exact mul_mul_mul_comm
        (WittWeightedDigits.value p ρ P.numerator)
        (WittWeightedDigits.value p ρ Q.numerator)
        ((ρ⁻¹) ^ P.exponent) ((ρ⁻¹) ^ Q.exponent)

theorem value_neg (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : PadicBoundedWittLocalization.Ring p) :
    value p ρ (-x) = value p ρ x := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := presentation p x
  have he : toAmbient p (-x) * (p : Ambient p) ^ P.exponent =
      algebraMap (FieldWitt p) (Ambient p) (-P.numerator) := by
    rw [map_neg, neg_mul, P.relation, map_neg]
  rw [value_eq_of_presentation p ρ hρ0 hρtop _ P.exponent _ he,
    WittWeightedDigitNegation.value_neg p
      (LocalGeometricFontaine.integerRing (PadicTiltField.Carrier p))
      (LocalGeometricFontaine.mem_integerRing (PadicTiltField.Carrier p)) ρ hρ1]
  exact (value_eq_of_presentation p ρ hρ0 hρtop x
    P.exponent P.numerator P.relation).symm

end
end JoshiTeich.Act1Scene1.PadicWittRhoValue
