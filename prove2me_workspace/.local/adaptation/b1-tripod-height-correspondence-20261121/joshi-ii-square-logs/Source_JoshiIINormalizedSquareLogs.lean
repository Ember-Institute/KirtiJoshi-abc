import Theorems.Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
The coefficient calculation in Kirti Joshi, Arithmetic Teichmuller Spaces II,
Theorem 9.2.1, proof after `eq:val-rel-main2`. The signed weighted average uses
the same normalized square exponents and works for a finite set of places.
-/

set_option autoImplicit false

namespace AbcAdaptation.JoshiII

open scoped BigOperators

/-- The sum of the squared normalized labels for a positive procession length. -/
theorem sum_normalized_squares (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2) =
      ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / (6 * (m : ℝ)) := by
  have hsum : (∑ j : Fin m, ((j : ℝ) + 1) ^ 2) =
      (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 6 := by
    simpa only [zero_mul, one_mul, zero_add, add_zero] using
      Reference.Iut.sum_affine_quadratic m 0 1 0
  simp_rw [div_pow]
  rw [← Finset.sum_div, hsum]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp [hm0] <;> ring

/-- Substitute the log of a `2ℓ`-th root, where `ℓ = 2m + 1`. -/
theorem sum_normalized_square_root_logs (m : ℕ) (hm : 0 < m) (qLog : ℝ) :
    (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2 *
        (qLog / (2 * (2 * (m : ℝ) + 1)))) =
      (1 / 12 : ℝ) * (1 + 1 / (m : ℝ)) * qLog := by
  rw [← Finset.sum_mul, sum_normalized_squares m hm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hℓ : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  field_simp [hmR.ne', hℓ.ne'] <;> ring

private theorem normalized_square_sum_lt_length {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / (6 * (m : ℝ)) < (m : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  apply (div_lt_iff₀ (mul_pos (by norm_num) hm0)).2
  have hgap : 0 < ((m : ℝ) - 1) * (4 * (m : ℝ) + 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [hgap]

/-- The reference log bound is strict for a negative Tate log and `ℓ ≥ 5` odd. -/
theorem root_log_bound_lt_sum_normalized_square_root_logs {m : ℕ}
    (hm : 2 ≤ m) {qLog : ℝ} (hq : qLog < 0) :
    (m : ℝ) * (qLog / (2 * (2 * (m : ℝ) + 1))) <
      ∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2 *
        (qLog / (2 * (2 * (m : ℝ) + 1))) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hℓ : (0 : ℝ) < 2 * (2 * (m : ℝ) + 1) := by linarith
  rw [← Finset.sum_mul, sum_normalized_squares m hm0]
  exact mul_lt_mul_of_neg_right (normalized_square_sum_lt_length hm) (div_neg_of_neg_of_pos hq hℓ)

/-- A negative signed sum of root logs lies below its normalized square-weighted
average. The place weights are the same on the two sides. -/
theorem weighted_root_log_sum_lt_normalized_average {ι : Type*}
    (s : Finset ι) (weight rootLog : ι → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hnegative : (∑ v ∈ s, weight v * rootLog v) < 0) :
    (∑ v ∈ s, weight v * rootLog v) <
      (∑ j : Fin m, ∑ v ∈ s, weight v * ((((j : ℝ) + 1) / (m : ℝ)) ^ 2 * rootLog v)) /
        (m : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hfactor :
      (∑ j : Fin m, ∑ v ∈ s, weight v * ((((j : ℝ) + 1) / (m : ℝ)) ^ 2 * rootLog v)) =
        (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2) *
          (∑ v ∈ s, weight v * rootLog v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hfactor, sum_normalized_squares m hm0]
  apply (lt_div_iff₀ hmR).2
  rw [mul_comm (∑ v ∈ s, weight v * rootLog v) (m : ℝ)]
  exact mul_lt_mul_of_neg_right (normalized_square_sum_lt_length hm) hnegative

end AbcAdaptation.JoshiII

#print axioms AbcAdaptation.JoshiII.sum_normalized_squares
#print axioms AbcAdaptation.JoshiII.sum_normalized_square_root_logs
#print axioms AbcAdaptation.JoshiII.root_log_bound_lt_sum_normalized_square_root_logs
#print axioms AbcAdaptation.JoshiII.weighted_root_log_sum_lt_normalized_average
