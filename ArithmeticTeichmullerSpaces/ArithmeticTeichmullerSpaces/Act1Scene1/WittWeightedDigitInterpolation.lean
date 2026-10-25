import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-INTERPOLATION
source: Joshi II `se:ff-rings`, the family of rho norms defining the
period-ring topology in `pr:teichmuller-lift-A/B`.
fidelity: for a p-power numerator presentation, the weighted digit value
divided by rho^m at an intermediate radius is bounded by the maximum of
its two endpoint values. The proof separates digit indices below and
above the denominator exponent. Original proofs; no reference code copied.
boundary: Scene1/Derived; this is the two-endpoint bound, not a claim
of exact log-convexity or completed period-ring identity.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitInterpolation

open scoped ENNReal
noncomputable section

private theorem powerRatio_of_le {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (n m : ℕ) (h : m ≤ n) : r ^ n / r ^ m = r ^ (n - m) := by
  have he : r ^ n = r ^ (n - m) * r ^ m := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [he, ENNReal.mul_div_cancel_right (pow_ne_zero m hr0) (ENNReal.pow_ne_top hrt)]

private theorem powerRatio_of_ge {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (n m : ℕ) (h : n ≤ m) : r ^ n / r ^ m = 1 / r ^ (m - n) := by
  have he : r ^ m = r ^ n * r ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [he]
  simpa only [mul_one] using
    ENNReal.mul_div_mul_left 1 (r ^ (m - n)) (pow_ne_zero n hr0) (ENNReal.pow_ne_top hrt)

theorem powerRatio_mono_of_le {r s : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hs0 : s ≠ 0) (hst : s ≠ ⊤) (hrs : r ≤ s) (n m : ℕ) (h : m ≤ n) :
    r ^ n / r ^ m ≤ s ^ n / s ^ m := by
  rw [powerRatio_of_le hr0 hrt n m h, powerRatio_of_le hs0 hst n m h]
  exact pow_le_pow_left₀ bot_le hrs _

theorem powerRatio_antitone_of_ge {r s : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hs0 : s ≠ 0) (hst : s ≠ ⊤) (hrs : r ≤ s) (n m : ℕ) (h : n ≤ m) :
    s ^ n / s ^ m ≤ r ^ n / r ^ m := by
  rw [powerRatio_of_ge hr0 hrt n m h, powerRatio_of_ge hs0 hst n m h]
  exact ENNReal.div_le_div le_rfl (pow_le_pow_left₀ bot_le hrs _)

variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

private theorem divided_term_le (r : ℝ≥0∞) (x : WittVector p F) (n m : ℕ) :
    ENNReal.ofReal ‖WittTeichmullerExpansion.digits p x n‖ * (r ^ n / r ^ m) ≤
      WittWeightedDigits.value p r x / r ^ m := by
  rw [← mul_div_assoc]
  exact ENNReal.div_le_div_right (WittWeightedDigits.term_le_value p r x n) _

theorem dividedValue_le_endpoint_max (a r b : ℝ≥0∞)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (har : a ≤ r) (hrb : r ≤ b)
    (x : WittVector p F) (m : ℕ) :
    WittWeightedDigits.value p r x / r ^ m ≤
      max (WittWeightedDigits.value p a x / a ^ m)
        (WittWeightedDigits.value p b x / b ^ m) := by
  rw [WittWeightedDigits.value, ENNReal.iSup_div]
  apply iSup_le
  intro n
  rw [mul_div_assoc]
  by_cases h : m ≤ n
  · exact (mul_le_mul_of_nonneg_left
      (powerRatio_mono_of_le hr0 hrt hb0 hbt hrb n m h) bot_le).trans
      ((divided_term_le p b x n m).trans (le_max_right _ _))
  · exact (mul_le_mul_of_nonneg_left
      (powerRatio_antitone_of_ge ha0 hat hr0 hrt har n m (Nat.le_of_not_ge h)) bot_le).trans
      ((divided_term_le p a x n m).trans (le_max_left _ _))

end
end JoshiTeich.Act1Scene1.WittWeightedDigitInterpolation
