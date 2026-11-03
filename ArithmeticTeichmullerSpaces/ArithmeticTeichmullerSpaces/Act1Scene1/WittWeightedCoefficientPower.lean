import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-COEFFICIENT-POWER
source: Joshi II `se:ff-rings` and its rho-weighted Teichmuller expansion.
fidelity: a power comparison of the norms of Witt coefficients implies the
same comparison of Teichmuller digits and of their weighted suprema.
Raising the target value to the positive integer power d changes the
source radius from rho to rho^d. Original proofs; no reference code copied.
boundary: Scene1/Derived; the coefficient norm comparison is an explicit
hypothesis. No coefficient-field ring map, completed B ring, topology,
localization, or completion transport is asserted.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedCoefficientPower

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {F G : Type*}
variable [NormedField F] [CharP F p] [PerfectRing F p]
variable [NormedField G] [CharP G p] [PerfectRing G p]

theorem digits_norm_power (d : ℕ) (x : WittVector p F) (y : WittVector p G)
    (hcoeff : ∀ n : ℕ, ‖y.coeff n‖ ^ d = ‖x.coeff n‖) (n : ℕ) :
    ‖digits p y n‖ ^ d = ‖digits p x n‖ := by
  have hx : ‖digits p x n‖ ^ (p ^ n) = ‖x.coeff n‖ := by
    simpa only [norm_pow] using
      (congrArg (fun z : F => ‖z‖)
        ((expands_iff_coeff p x (digits p x)).mp (expands_digits p x) n)).symm
  have hy : ‖digits p y n‖ ^ (p ^ n) = ‖y.coeff n‖ := by
    simpa only [norm_pow] using
      (congrArg (fun z : G => ‖z‖)
        ((expands_iff_coeff p y (digits p y)).mp (expands_digits p y) n)).symm
  apply (pow_left_inj₀ (pow_nonneg (norm_nonneg _) d) (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
  calc
    (‖digits p y n‖ ^ d) ^ (p ^ n) = (‖digits p y n‖ ^ (p ^ n)) ^ d := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm d (p ^ n)]
    _ = ‖y.coeff n‖ ^ d := by rw [hy]
    _ = ‖x.coeff n‖ := hcoeff n
    _ = ‖digits p x n‖ ^ (p ^ n) := hx.symm

theorem value_pow_of_coeff_norm (d : ℕ) (hd : 0 < d)
    (x : WittVector p F) (y : WittVector p G)
    (hcoeff : ∀ n : ℕ, ‖y.coeff n‖ ^ d = ‖x.coeff n‖) (ρ : ℝ≥0∞) :
    value p ρ y ^ d = value p (ρ ^ d) x := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  unfold value
  calc
    (⨆ n : ℕ, ENNReal.ofReal ‖digits p y n‖ * ρ ^ n) ^ d =
        ⨆ n : ℕ, (ENNReal.ofReal ‖digits p y n‖ * ρ ^ n) ^ d := by
      simpa only [ENNReal.orderIsoRpow_apply, ENNReal.rpow_natCast] using
        (ENNReal.orderIsoRpow (d : ℝ) hdR).map_iSup
          (fun n : ℕ => ENNReal.ofReal ‖digits p y n‖ * ρ ^ n)
    _ = ⨆ n : ℕ, ENNReal.ofReal ‖digits p x n‖ * (ρ ^ d) ^ n := by
      apply iSup_congr
      intro n
      rw [mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _) d,
        digits_norm_power p d x y hcoeff n]
      congr 1
      exact (pow_mul ρ n d).symm.trans
        ((congrArg (fun k : ℕ => ρ ^ k) (Nat.mul_comm n d)).trans (pow_mul ρ d n))

theorem value_pow_of_coeff_norm_function {A : Type*}
    {x : A → WittVector p F} {y : A → WittVector p G}
    (d : ℕ) (hd : 0 < d)
    (hcoeff : ∀ a n, ‖(y a).coeff n‖ ^ d = ‖(x a).coeff n‖) :
    ∀ a ρ, value p ρ (y a) ^ d = value p (ρ ^ d) (x a) :=
  fun a ρ => value_pow_of_coeff_norm p d hd (x a) (y a) (hcoeff a) ρ

end
end JoshiTeich.Act1Scene1.WittWeightedCoefficientPower
