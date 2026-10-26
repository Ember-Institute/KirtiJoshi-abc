import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricDominantTerm
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-MAXIMUM
source: Joshi II `se:ff-rings`, the bounded Gauss norms underlying
`pr:teichmuller-lift-A/B`.
fidelity: the genuine bounded Teichmuller digits have weighted terms
tending to zero at every radius strictly between zero and one. Their
weighted supremum equals an actual digit term, with a least maximizing
index and strict inequalities at all smaller indices.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; multiplicative equality still requires
control of actual Witt carries in products.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitMaximum

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

def realTerm (ρ : ℝ≥0∞) (x : WittVector p F) (n : ℕ) : ℝ :=
  ‖digits p x n‖ * ρ.toReal ^ n

theorem realTerm_nonneg (ρ : ℝ≥0∞) (x : WittVector p F) (n : ℕ) :
    0 ≤ realTerm p ρ x n := mul_nonneg (norm_nonneg _) (pow_nonneg ENNReal.toReal_nonneg n)

theorem term_toReal (ρ : ℝ≥0∞) (x : WittVector p F) (n : ℕ) :
    (ENNReal.ofReal ‖digits p x n‖ * ρ ^ n).toReal = realTerm p ρ x n := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_pow]
  rfl

theorem tendsto_realTerm (ρ : ℝ≥0∞) (hρ : ρ < 1) (x : WittVector p F)
    (C : ℝ) (hC : ∀ n, ‖digits p x n‖ ≤ C) :
    Filter.Tendsto (realTerm p ρ x) Filter.atTop (𝓝 0) := by
  have hr : ρ.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (hρ.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr hρ
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr).const_mul C
  apply squeeze_zero (realTerm_nonneg p ρ x)
    (fun n => mul_le_mul_of_nonneg_right (hC n) (pow_nonneg ENNReal.toReal_nonneg n))
  simpa only [mul_zero] using ht

theorem exists_first_max (ρ : ℝ≥0∞) (hρ : ρ < 1) (x : WittVector p F)
    (C : ℝ) (hC : ∀ n, ‖digits p x n‖ ≤ C) :
    ∃ i, value p ρ x = ENNReal.ofReal ‖digits p x i‖ * ρ ^ i ∧
      (∀ n, realTerm p ρ x n ≤ realTerm p ρ x i) ∧
      ∀ n < i, realTerm p ρ x n < realTerm p ρ x i := by
  obtain ⟨i, hmax, hlt⟩ := GeometricDominantTerm.exists_first_max_of_tendsto_zero
    (realTerm p ρ x) (realTerm_nonneg p ρ x) (tendsto_realTerm p ρ hρ x C hC)
  refine ⟨i, ?_, hmax, hlt⟩
  apply le_antisymm
  · apply iSup_le
    intro n
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (hρ.trans ENNReal.one_lt_top).ne))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (hρ.trans ENNReal.one_lt_top).ne))).mp
    simpa only [term_toReal] using hmax n
  · exact term_le_value p ρ x i

theorem maximizing_digit_ne_zero (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (x : WittVector p F)
    (hx : x ≠ 0) (i : ℕ) (hi : value p ρ x = ENNReal.ofReal ‖digits p x i‖ * ρ ^ i) :
    digits p x i ≠ 0 := by
  intro hd
  apply hx
  apply (value_eq_zero_iff p ρ hρ0 x).mp
  rw [hi, hd, norm_zero, ENNReal.ofReal_zero, zero_mul]

end
end JoshiTeich.Act1Scene1.WittWeightedDigitMaximum
