import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
source-id: JT-SCENE1-ULTRAMETRIC-LOG-TAIL-BOUNDS
source: Joshi II logarithmic Tate periods; the standard first-term
dominance estimate for nonarchimedean logarithm series.
fidelity: proves a uniform polynomial-times-geometric bound for terms
of degree at least two. Proves the norm of an actual summable series
is bounded by any common nonnegative bound on its term norms.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual coefficients and period consumers
must independently supply the hypotheses of these estimates.
-/

namespace JoshiTeich.Act1Scene1.UltrametricLogTailBounds

open scoped Topology

theorem degree_le_two_pow (n : ℕ) : (n + 2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
  have h : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
  exact_mod_cast h

theorem polynomial_geometric_tail_le (k n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hsmall : (2 : ℝ) ^ k * r ≤ 1 / 2) :
    (n + 2 : ℝ) ^ k * r ^ (n + 2) ≤ r / 2 := by
  have hdeg := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n + 2) (degree_le_two_pow n) k
  have hbase : 0 ≤ (2 : ℝ) ^ k * r := mul_nonneg (by positivity) hr
  have hpower : ((2 : ℝ) ^ k * r) ^ (n + 1) ≤ 1 / 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ k * r) ^ 1 :=
        pow_le_pow_of_le_one hbase (hsmall.trans (by norm_num)) (Nat.le_add_left 1 n)
      _ ≤ _ := by simpa only [pow_one] using hsmall
  calc
    _ ≤ ((2 : ℝ) ^ (n + 1)) ^ k * r ^ (n + 2) :=
      mul_le_mul_of_nonneg_right hdeg (pow_nonneg hr _)
    _ = r * ((2 : ℝ) ^ k * r) ^ (n + 1) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm (n + 1) k, show n + 2 = (n + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left hpower hr
    _ = _ := by ring

theorem norm_tsum_le_of_forall_le {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
    {ι : Type*} (f : ι → E) (hf : Summable f) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C) : ‖∑' i, f i‖ ≤ C := by
  apply le_of_tendsto hf.hasSum.norm
  exact Filter.Eventually.of_forall (fun s : Finset ι =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => h i))

end JoshiTeich.Act1Scene1.UltrametricLogTailBounds
