import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoRingLaws
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-RING-NORM
source: Joshi II `se:ff-rings`, the original weighted Teichmuller value on
W(O_F)[1/p,1/[t]] for the independently constructed standard F=C_p^flat.
fidelity: passes the finite standard rho value to the reals and constructs
its nonarchimedean RingNorm from the proved presentation laws. The carrier,
value and norm depend only on p; no actual InitialThetaData is used.
Original proofs using the project's actual rho-norm pattern; no reference
implementation copied. Prologue R5 unchanged.
boundary: this constructs the standard normed bounded ring, not a paper B
or period/BK identity.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoNorm

open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

def realValue (ρ : ℝ≥0∞) (x : PadicBoundedWittLocalization.Ring p) : ℝ :=
  (PadicWittRhoValue.value p ρ x).toReal

theorem realValue_nonneg (ρ : ℝ≥0∞) (x : PadicBoundedWittLocalization.Ring p) :
    0 ≤ realValue p ρ x := ENNReal.toReal_nonneg

theorem realValue_zero (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) : realValue p ρ 0 = 0 := by
  exact congrArg ENNReal.toReal
    (PadicWittRhoValue.value_zero p ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem realValue_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) : realValue p ρ 1 = 1 := by
  exact congrArg ENNReal.toReal
    (PadicWittRhoValue.value_one p ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem realValue_neg (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : PadicBoundedWittLocalization.Ring p) :
    realValue p ρ (-x) = realValue p ρ x :=
  congrArg ENNReal.toReal (PadicWittRhoValue.value_neg p ρ hρ0 hρ1 x)

theorem realValue_eq_zero_iff (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : PadicBoundedWittLocalization.Ring p) : realValue p ρ x = 0 ↔ x = 0 := by
  rw [realValue, ENNReal.toReal_eq_zero_iff,
    or_iff_left (PadicWittRhoValue.value_lt_top p ρ hρ0 hρ1 x).ne,
    PadicWittRhoValue.value_eq_zero_iff p ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne]

theorem realValue_add_le_max (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : PadicBoundedWittLocalization.Ring p) :
    realValue p ρ (x + y) ≤ max (realValue p ρ x) (realValue p ρ y) := by
  have hx := PadicWittRhoValue.value_lt_top p ρ hρ0 hρ1 x
  have hy := PadicWittRhoValue.value_lt_top p ρ hρ0 hρ1 y
  have h := ENNReal.toReal_mono (max_lt hx hy).ne
    (PadicWittRhoValue.value_add_le_max p ρ hρ0 hρ1 x y)
  simpa only [realValue, ENNReal.toReal_max hx.ne hy.ne] using h

theorem realValue_add_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : PadicBoundedWittLocalization.Ring p) :
    realValue p ρ (x + y) ≤ realValue p ρ x + realValue p ρ y :=
  (realValue_add_le_max p ρ hρ0 hρ1 x y).trans
    (max_le (le_add_of_nonneg_right (realValue_nonneg p ρ y))
      (le_add_of_nonneg_left (realValue_nonneg p ρ x)))

theorem realValue_mul_le (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x y : PadicBoundedWittLocalization.Ring p) :
    realValue p ρ (x * y) ≤ realValue p ρ x * realValue p ρ y := by
  have hx := PadicWittRhoValue.value_lt_top p ρ hρ0 hρ1 x
  have hy := PadicWittRhoValue.value_lt_top p ρ hρ0 hρ1 y
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hx.ne hy.ne)
    (PadicWittRhoValue.value_mul_le p ρ hρ0 hρ1 x y)
  simpa only [realValue, ENNReal.toReal_mul] using h

def ringNorm (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    RingNorm (PadicBoundedWittLocalization.Ring p) where
  toFun := realValue p ρ
  map_zero' := realValue_zero p ρ hρ0 hρ1
  add_le' := realValue_add_le p ρ hρ0 hρ1
  neg' := realValue_neg p ρ hρ0 hρ1
  mul_le' := realValue_mul_le p ρ hρ0 hρ1
  eq_zero_of_map_eq_zero' := fun x hx => (realValue_eq_zero_iff p ρ hρ0 hρ1 x).mp hx

theorem ringNorm_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    ringNorm p ρ hρ0 hρ1 1 = 1 := realValue_one p ρ hρ0 hρ1

theorem ringNorm_prime (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    ringNorm p ρ hρ0 hρ1 (p) = ρ.toReal :=
  congrArg ENNReal.toReal
    (PadicWittRhoValue.value_prime p ρ hρ0 (hρ1.trans_lt ENNReal.one_lt_top).ne)

theorem ringNorm_isNonarchimedean (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1) :
    IsNonarchimedean (ringNorm p ρ hρ0 hρ1) := by
  intro x y
  exact realValue_add_le_max p ρ hρ0 hρ1 x y

end
end JoshiTeich.Act1Scene1.PadicWittRhoNorm
