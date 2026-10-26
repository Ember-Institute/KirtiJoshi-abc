import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialSeries
import Mathlib.Data.Nat.Choose.Sum

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-MULTIPLICATION
source: Joshi II `pr:teichmuller-lift-A`, multiplicative-formal-group
periods and their exponential inverse; the binomial and Cauchy products.
fidelity: the actual convergent series satisfies the exponential addition
and natural-multiple laws in each original rho completion. Exponentials
in this domain are actual units, with inverse the negative exponential.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no exp/log inverse or full period representation
is asserted. All convergence domains use the original norm. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialMultiplication

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialCoefficients InitialThetaWittExponentialSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem term_mul (ρ : Radius) (x y : Ring D w ρ) (n k : ℕ) (hk : k ≤ n) :
    term D w ρ x k * term D w ρ y (n - k) =
      completedPadicMap D w ρ (coefficient D w n) *
        (x ^ k * y ^ (n - k) * (n.choose k : Ring D w ρ)) := by
  have h := congrArg (completedPadicMap D w ρ) (coefficient_mul D w n k hk)
  simp only [map_mul, map_natCast] at h
  unfold term
  calc
    _ = (completedPadicMap D w ρ (coefficient D w k) *
        completedPadicMap D w ρ (coefficient D w (n - k))) * (x ^ k * y ^ (n - k)) := by ring
    _ = _ := by rw [h]; ring

theorem sum_term_mul (ρ : Radius) (x y : Ring D w ρ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), term D w ρ x k * term D w ρ y (n - k)) =
      term D w ρ (x + y) n := by
  rw [term, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_mul D w ρ x y n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem norm_add_lt (ρ : Radius) (x y : Ring D w ρ)
    (hx : ‖x‖ < ρ.val.toReal) (hy : ‖y‖ < ρ.val.toReal) : ‖x + y‖ < ρ.val.toReal :=
  (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ x y).trans_lt (max_lt hx hy)

theorem exp_add (ρ : Radius) (x y : Ring D w ρ)
    (hx : ‖x‖ < ρ.val.toReal) (hy : ‖y‖ < ρ.val.toReal) :
    exp D w ρ (x + y) = exp D w ρ x * exp D w ρ y := by
  have h := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_norm_term D w ρ x hx) (summable_norm_term D w ρ y hy)
  simpa only [sum_term_mul, exp] using h.symm

theorem norm_nsmul_le (ρ : Radius) (x : Ring D w ρ) (n : ℕ) : ‖n • x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simpa only [zero_nsmul, norm_zero] using norm_nonneg x
  | succ n ih =>
    rw [succ_nsmul]
    exact (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans (max_le ih le_rfl)

theorem exp_nsmul (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) (n : ℕ) :
    exp D w ρ (n • x) = exp D w ρ x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, exp_zero, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, exp_add D w ρ _ _ ((norm_nsmul_le D w ρ x n).trans_lt hx) hx,
      ih, pow_succ]

theorem exp_mul_exp_neg (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    exp D w ρ x * exp D w ρ (-x) = 1 := by
  rw [← exp_add D w ρ x (-x) hx (by simpa only [norm_neg] using hx), add_neg_cancel, exp_zero]

def expUnit (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) : (Ring D w ρ)ˣ where
  val := exp D w ρ x
  inv := exp D w ρ (-x)
  val_inv := exp_mul_exp_neg D w ρ x hx
  inv_val := (mul_comm _ _).trans (exp_mul_exp_neg D w ρ x hx)

theorem expUnit_val (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    (expUnit D w ρ x hx).val = exp D w ρ x := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialMultiplication
