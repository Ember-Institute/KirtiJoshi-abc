import Solutions.Source_ReferenceIutCor312DividedPowerLog
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.DividedPowerLog

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The finite sum for the quotient of the binomial difference by its
positive exponent. The exponent is indexed as the successor of m. -/
def binomialApproximation (γ : ℕ → R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range (m + 1), (m.descFactorial i : R) * γ (i + 1)

theorem succ_mul_binomialApproximation (γ : ℕ → R) {x : R}
    (hγ : ∀ n : ℕ, (n.factorial : R) * γ n = x ^ n) (m : ℕ) :
    ((m + 1 : ℕ) : R) * binomialApproximation γ m = (1 + x) ^ (m + 1) - 1 := by
  have hbin :
      (1 + x) ^ (m + 1) - 1 =
        ∑ i ∈ Finset.range (m + 1), x ^ (i + 1) * ((m + 1).choose (i + 1) : R) := by
    rw [add_comm (1 : R) x, add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right]
  rw [binomialApproximation, Finset.mul_sum, hbin]
  apply Finset.sum_congr rfl
  intro i _
  have hc := congrArg (fun a : ℕ => (a : R)) (Nat.add_one_mul_choose_eq m i)
  simp only [Nat.cast_mul] at hc
  have hf := hγ (i + 1)
  rw [Nat.factorial_succ, Nat.cast_mul] at hf
  calc
    _ = ((((m + 1 : ℕ) : R) * (m.choose i : R)) * ((i.factorial : R) * γ (i + 1))) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      ac_rfl
    _ = ((m + 1).choose (i + 1) : R) *
        ((((i + 1 : ℕ) : R) * (i.factorial : R)) * γ (i + 1)) := by
      rw [hc]
      ring
    _ = _ := by rw [hf, mul_comm]

private theorem cast_descFactorial_of_succ_eq_zero {m i : ℕ}
    (hm : ((m + 1 : ℕ) : R) = 0) (hi : i ≤ m) :
    (m.descFactorial i : R) = (-1 : R) ^ i * (i.factorial : R) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have he : m - i = m + 1 - (i + 1) := by omega
    have hfactor : ((m - i : ℕ) : R) = -((i + 1 : ℕ) : R) := by
      rw [he, Nat.cast_sub (hi.trans (Nat.le_succ m)), hm, zero_sub]
    rw [Nat.descFactorial_succ, Nat.cast_mul, hfactor, ih ((Nat.le_succ i).trans hi),
      Nat.factorial_succ, Nat.cast_mul, pow_succ, ← neg_one_mul (((i + 1 : ℕ) : R))]
    ac_rfl

/-- In a quotient that kills the exponent, the binomial coefficients
give the alternating factorial coefficients of the logarithm. -/
theorem quotient_binomialApproximation_eq_logPartialSum (J : Ideal R) {m : ℕ}
    (hm : Ideal.Quotient.mk J (((m + 1 : ℕ) : R)) = 0) (γ : ℕ → R) :
    Ideal.Quotient.mk J (binomialApproximation γ m) =
      Ideal.Quotient.mk J (logPartialSum γ (m + 1)) := by
  have hm' : ((m + 1 : ℕ) : R ⧸ J) = 0 := by simpa only [map_natCast] using hm
  simp only [binomialApproximation, logPartialSum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [logTerm, map_mul, map_pow, map_neg, map_one, map_natCast]
  exact congrArg (fun a : R ⧸ J => a * Ideal.Quotient.mk J (γ (i + 1)))
    (cast_descFactorial_of_succ_eq_zero hm' hi')

end

end JoshiTeich.Act1Scene1.DividedPowerLog
