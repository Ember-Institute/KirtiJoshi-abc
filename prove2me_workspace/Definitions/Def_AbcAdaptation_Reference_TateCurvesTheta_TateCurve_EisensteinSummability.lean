/-
Adapted from `TateCurvesTheta/TateCurve/Weierstrass.lean:76` in
`lana-agents/tate-curves-theta` at `ca6c2279d3cea0690cdb01328e727118d5485d68`.
-/
/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Weierstrass

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] (t : TateParameter K)
variable [IsUltrametricDist K]

/-- In a nonarchimedean field, `1 - qⁿ⁺¹` has norm `1`: since `‖qⁿ⁺¹‖ < 1 = ‖1‖`, the
ultrametric "isosceles" law makes the norm of the difference equal to the larger of the two. -/
lemma norm_one_sub_qpow (n : ℕ) : ‖(1 : K) - (t.q : K) ^ (n + 1)‖ = 1 := by
  have hlt : ‖(t.q : K) ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero n)
  have hne : ‖(1 : K)‖ ≠ ‖(t.q : K) ^ (n + 1)‖ := by
    rw [norm_one]; exact (ne_of_lt hlt).symm
  rw [sub_eq_add_neg,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rwa [norm_neg]),
    norm_neg, norm_one, max_eq_left hlt.le]

/-- The factor `1 - qⁿ⁺¹` in the denominator of the Eisenstein series is nonzero. -/
lemma one_sub_qpow_ne_zero (n : ℕ) : (1 : K) - (t.q : K) ^ (n + 1) ≠ 0 :=
  norm_pos_iff.mp (by rw [t.norm_one_sub_qpow n]; exact one_pos)

variable [CompleteSpace K]

/-- The family defining the Eisenstein series `sₖ(q)` is summable: each term has norm
`‖(n + 1 : K)‖ᵏ · ‖q‖ⁿ⁺¹ ≤ ‖q‖ⁿ⁺¹`, dominated by the convergent geometric series `∑ ‖q‖ⁿ⁺¹`. -/
lemma eisenstein_summand_summable (k : ℕ) :
    Summable fun n : ℕ =>
      ((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1)) := by
  have hg : Summable fun n : ℕ => ‖(t.q : K)‖ ^ (n + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  refine hg.of_norm_bounded ?_
  intro n
  rw [norm_div, norm_mul, norm_pow, norm_pow, t.norm_one_sub_qpow n, div_one]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 ^ k * ‖(t.q : K)‖ ^ (n + 1) := by
        gcongr
        exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
    _ = ‖(t.q : K)‖ ^ (n + 1) := by rw [one_pow, one_mul]

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter
