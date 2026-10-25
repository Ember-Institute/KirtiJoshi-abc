import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitNegation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoAddition
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoMultiplication
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-RING-NORM
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the normed
bounded period subring before Frechet completion.
fidelity: proves negation invariance, passes the finite actual localization
value to the reals and constructs a nonarchimedean RingNorm on the original
bounded Witt localization. Its value at p is rho.toReal. All norm fields
come from proved digit and presentation laws. Original proofs.
boundary: Scene1/Derived; this is a submultiplicative RingNorm, not yet a
MulRingNorm. No completed Frechet B, scalar-normalization comparison or BK
identity is asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoNorm

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

theorem value_neg (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w ρ (-x) = InitialThetaWittRhoValue.value D w ρ x := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  let P := InitialThetaWittRhoValue.presentation D w x
  have he : toAmbient D w (-x) * (Arithmetic.residueChar w.1 : Ambient D w) ^ P.exponent =
      algebraMap (FieldWitt D w) (Ambient D w) (-P.numerator) := by
    rw [map_neg, neg_mul, P.relation, map_neg]
  rw [InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop _ P.exponent _ he,
    WittWeightedDigitNegation.value_neg (Arithmetic.residueChar w.1)
      (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
      (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w)) ρ hρ1]
  exact (InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop x
    P.exponent P.numerator P.relation).symm

def realValue (ρ : ℝ≥0∞) (x : InitialThetaBoundedWittLocalization.Ring D w) : ℝ :=
  (InitialThetaWittRhoValue.value D w ρ x).toReal

theorem realValue_nonneg (ρ : ℝ≥0∞) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    0 ≤ realValue D w ρ x := ENNReal.toReal_nonneg

theorem realValue_zero (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) : realValue D w ρ 0 = 0 := by
  exact congrArg ENNReal.toReal
    (InitialThetaWittRhoValue.value_zero D w ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem realValue_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) : realValue D w ρ 1 = 1 := by
  exact congrArg ENNReal.toReal
    (InitialThetaWittRhoValue.value_one D w ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem realValue_neg (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    realValue D w ρ (-x) = realValue D w ρ x :=
  congrArg ENNReal.toReal (value_neg D w ρ hρ0 hρ1 x)

theorem realValue_eq_zero_iff (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) : realValue D w ρ x = 0 ↔ x = 0 := by
  rw [realValue, ENNReal.toReal_eq_zero_iff,
    or_iff_left (InitialThetaWittRhoValue.value_lt_top D w ρ hρ0 hρ1 x).ne,
    InitialThetaWittRhoValue.value_eq_zero_iff D w ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne]

theorem realValue_add_le_max (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    realValue D w ρ (x + y) ≤ max (realValue D w ρ x) (realValue D w ρ y) := by
  have hx := InitialThetaWittRhoValue.value_lt_top D w ρ hρ0 hρ1 x
  have hy := InitialThetaWittRhoValue.value_lt_top D w ρ hρ0 hρ1 y
  have h := ENNReal.toReal_mono (max_lt hx hy).ne
    (InitialThetaWittRhoAddition.value_add_le_max D w ρ hρ0 hρ1 x y)
  simpa only [realValue, ENNReal.toReal_max hx.ne hy.ne] using h

theorem realValue_add_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    realValue D w ρ (x + y) ≤ realValue D w ρ x + realValue D w ρ y :=
  (realValue_add_le_max D w ρ hρ0 hρ1 x y).trans
    (max_le (le_add_of_nonneg_right (realValue_nonneg D w ρ y))
      (le_add_of_nonneg_left (realValue_nonneg D w ρ x)))

theorem realValue_mul_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : InitialThetaBoundedWittLocalization.Ring D w) :
    realValue D w ρ (x * y) ≤ realValue D w ρ x * realValue D w ρ y := by
  have hx := InitialThetaWittRhoValue.value_lt_top D w ρ hρ0 hρ1 x
  have hy := InitialThetaWittRhoValue.value_lt_top D w ρ hρ0 hρ1 y
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hx.ne hy.ne)
    (InitialThetaWittRhoMultiplication.value_mul_le D w ρ hρ0 hρ1 x y)
  simpa only [realValue, ENNReal.toReal_mul] using h

def ringNorm (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    RingNorm (InitialThetaBoundedWittLocalization.Ring D w) where
  toFun := realValue D w ρ
  map_zero' := realValue_zero D w ρ hρ0 hρ1
  add_le' := realValue_add_le D w ρ hρ0 hρ1
  neg' := realValue_neg D w ρ hρ0 hρ1
  mul_le' := realValue_mul_le D w ρ hρ0 hρ1
  eq_zero_of_map_eq_zero' := fun x hx => (realValue_eq_zero_iff D w ρ hρ0 hρ1 x).mp hx

theorem ringNorm_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    ringNorm D w ρ hρ0 hρ1 1 = 1 := realValue_one D w ρ hρ0 hρ1

theorem ringNorm_prime (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    ringNorm D w ρ hρ0 hρ1 (Arithmetic.residueChar w.1) = ρ.toReal :=
  congrArg ENNReal.toReal
    (InitialThetaWittRhoValue.value_prime D w ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem ringNorm_isNonarchimedean (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    IsNonarchimedean (ringNorm D w ρ hρ0 hρ1) := by
  intro x y
  exact realValue_add_le_max D w ρ hρ0 hρ1 x y

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoNorm
