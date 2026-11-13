import Definitions.Def_AbcClassical
import Theorems.Thm_abc_goal_lt_constant_mul_fix

set_option autoImplicit false
open UniqueFactorizationMonoid

namespace AbcAdaptation.RadicalTypingAudit

-- This checks the corrected open statement, not a proof of the conjecture.
example : AbcAdaptation.PlatformABC := abc.goal.lt_constant_mul_fix

set_option pp.all true in
#check abc.goal.lt_constant_mul_fix

theorem real_radical_eq_one (x : ℝ) : radical x = 1 := by
  by_cases hx : x = 0
  · rw [hx, radical_zero]
  · exact radical_of_isUnit (isUnit_iff_ne_zero.mpr hx)

theorem not_legacy_bound (ε : ℝ) :
    ¬ ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
        (c : ℝ) < K * (radical (a * b * c) : ℝ) ^ (1 + ε) := by
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt K
  have hsum : 1 + (n + 1) = n + 2 := by omega
  have hp := AbcAdaptation.pairwise_of_coprime_sum
    (a := 1) (b := n + 1) (c := n + 2) (Nat.coprime_one_left _) hsum
  have hbound := hK 1 (n + 1) (n + 2) (by omega) (by omega) (by omega) hp hsum
  rw [real_radical_eq_one, Real.one_rpow, mul_one] at hbound
  have hle : (n : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n 2
  exact (not_lt_of_ge hle) (hbound.trans hn)

#print axioms real_radical_eq_one
#print axioms not_legacy_bound

end AbcAdaptation.RadicalTypingAudit
