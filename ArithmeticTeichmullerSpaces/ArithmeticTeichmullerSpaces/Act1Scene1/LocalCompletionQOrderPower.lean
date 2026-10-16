import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra

/-!
source-id: JT-SCENE1-COMPLETION-QORDER-POWER
source: original completion discrete valuation and actual power equations.
fidelity: a base-field n-th root forces n to divide a contracting nonzero
parameter's normalized integer order. Powers multiply that order exactly.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open JoshiTeich.Prologue.Arithmetic WithZero
open scoped Valued
universe u
variable {K : Type u} [Field K] [NumberField K] (w : NumberField.FinitePlace K)

theorem qOrder_dvd_of_power_root (q : completionAt K w) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) (r : completionAt K w) (hr : r ^ n = q) :
    n ∣ completionQOrder w q := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hr
    exact hq0 hr.symm
  have hv : Valued.v r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have h := congrArg Valued.v hr
  rw [map_pow, completionQOrder_valued w q hq0 hq1,
    ← exp_log hv, ← exp_nsmul, exp_inj, nsmul_eq_mul] at h
  have hd : (n : ℤ) ∣ (completionQOrder w q : ℤ) :=
    ⟨-log (Valued.v r), by linear_combination h⟩
  exact_mod_cast hd

theorem qOrder_pow (q : completionAt K w) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : completionQOrder w (q ^ n) = n * completionQOrder w q := by
  have hqn : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 hn.ne'
  have h := completionQOrder_valued w (q ^ n) (pow_ne_zero n hq0) hqn
  rw [map_pow, completionQOrder_valued w q hq0 hq1, ← exp_nsmul, exp_inj,
    nsmul_eq_mul] at h
  have hi : (completionQOrder w (q ^ n) : ℤ) = (n : ℤ) * completionQOrder w q := by
    linear_combination h
  exact_mod_cast hi

end JoshiTeich.Act1Scene1.LocalCompletion
