import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-FROBENIUS
source: Joshi II `se:ff-rings`, Frobenius on the rho-normed period ring.
fidelity: computes the actual Teichmuller digits under Witt Frobenius
and proves the exact radius-power identity for their weighted supremum.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; localization and completion transport are
proved separately. No paper B or Tate-log eigenspace is assumed.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitFrobenius

open WittTeichmullerExpansion
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

theorem digits_frobenius (x : WittVector p F) (n : ℕ) :
    digits p (WittVector.frobenius x) n = (digits p x n) ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact congrFun (digits_unique p _ _
    (expands_map p (_root_.frobenius F p) x (digits p x) (expands_digits p x))).symm n

theorem value_frobenius (ρ : ℝ≥0∞) (x : WittVector p F) :
    WittWeightedDigits.value p (ρ ^ p) (WittVector.frobenius x) =
      WittWeightedDigits.value p ρ x ^ p := by
  unfold WittWeightedDigits.value
  rw [ENNReal.iSup_pow]
  apply iSup_congr
  intro n
  rw [digits_frobenius, norm_pow, ENNReal.ofReal_pow (norm_nonneg _), mul_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end
end JoshiTeich.Act1Scene1.WittWeightedDigitFrobenius
