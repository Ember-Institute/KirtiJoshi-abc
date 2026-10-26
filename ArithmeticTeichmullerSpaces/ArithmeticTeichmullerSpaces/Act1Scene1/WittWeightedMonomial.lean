import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedTruncation
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitMaximum

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-MONOMIAL
source: Joshi II `se:ff-rings`, Teichmuller monomials in the rho norm.
fidelity: computes the actual weighted value of a Teichmuller p-monomial
and its finite head, including exact vanishing above the truncation.
Computes the real weighted value of each digit-product monomial.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; these are monomial identities, not yet the
general multiplicative norm law.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedMonomial

open WittTeichmullerExpansion WittWeightedDigits WittWeightedTruncation
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

def monomial (a : F) (i : ℕ) : WittVector p F :=
  WittVector.teichmuller p a * (p : WittVector p F) ^ i

theorem value_monomial (ρ : ℝ≥0∞) (a : F) (i : ℕ) :
    value p ρ (monomial p a i) = ENNReal.ofReal ‖a‖ * ρ ^ i := by
  rw [monomial, value_mul_prime_pow, value_teichmuller, mul_comm]

theorem value_monomial_ne_top (ρ : ℝ≥0∞) (hρ : ρ ≠ ⊤) (a : F) (i : ℕ) :
    value p ρ (monomial p a i) ≠ ⊤ := by
  rw [value_monomial]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hρ)

theorem init_monomial_of_lt (a : F) (i N : ℕ) (hi : i < N) :
    WittVector.init N (monomial p a i) = monomial p a i := by
  apply WittVector.ext
  intro n
  simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
  split_ifs with hn
  · rfl
  · exact (WittVector.teichmuller_mul_pow_coeff_of_ne a (by omega : n ≠ i)).symm

theorem init_monomial_of_le (a : F) (i N : ℕ) (hi : N ≤ i) :
    WittVector.init N (monomial p a i) = 0 := by
  apply WittVector.ext
  intro n
  simp only [WittVector.init, WittVector.select, WittVector.coeff_mk, WittVector.zero_coeff]
  split_ifs with hn
  · exact WittVector.teichmuller_mul_pow_coeff_of_ne a (by omega : n ≠ i)
  · rfl

theorem headValue_monomial_of_lt (ρ : ℝ≥0∞) (a : F) (i N : ℕ) (hi : i < N) :
    headValue p ρ N (monomial p a i) = value p ρ (monomial p a i) := by
  rw [headValue, init_monomial_of_lt p a i N hi]

theorem headValue_monomial_of_le (ρ : ℝ≥0∞) (a : F) (i N : ℕ) (hi : N ≤ i) :
    headValue p ρ N (monomial p a i) = 0 := by
  rw [headValue, init_monomial_of_le p a i N hi, value_zero]

theorem product_monomial_value_toReal (ρ : ℝ≥0∞) (x y : WittVector p F) (i j : ℕ) :
    (value p ρ (monomial p (digits p x i * digits p y j) (i + j))).toReal =
      WittWeightedDigitMaximum.realTerm p ρ x i * WittWeightedDigitMaximum.realTerm p ρ y j := by
  rw [value_monomial, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_pow, norm_mul, pow_add]
  unfold WittWeightedDigitMaximum.realTerm
  ring

theorem product_monomial_value (ρ : ℝ≥0∞) (x y : WittVector p F) (i j : ℕ)
    (hi : value p ρ x = ENNReal.ofReal ‖digits p x i‖ * ρ ^ i)
    (hj : value p ρ y = ENNReal.ofReal ‖digits p y j‖ * ρ ^ j) :
    value p ρ (monomial p (digits p x i * digits p y j) (i + j)) = value p ρ x * value p ρ y := by
  rw [value_monomial, norm_mul, ENNReal.ofReal_mul (norm_nonneg _), pow_add, hi, hj]
  exact mul_mul_mul_comm _ _ _ _

end
end JoshiTeich.Act1Scene1.WittWeightedMonomial
