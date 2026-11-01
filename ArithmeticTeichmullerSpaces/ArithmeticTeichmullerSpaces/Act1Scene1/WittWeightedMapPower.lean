import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-MAP-POWER
source: Joshi II `se:ff-rings`, its rho-weighted Teichmuller expansion,
and the local coefficient-field norm-power comparison.
fidelity: proves naturality of the unique digits of actual Witt vectors and
the resulting weighted-supremum comparison for a norm-power preserving ring
map. Raising the target value to the positive integer power d changes the
source radius from rho to rho^d. Original proofs; no reference code copied.
boundary: Scene1/Derived; this is the generic underlying theorem needed by
the standard comparison. It does not identify these values with the paper's
B ring or assert its topology, localization, or completion.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedMapPower

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {F G : Type*}
variable [NormedField F] [CharP F p] [PerfectRing F p]
variable [NormedField G] [CharP G p] [PerfectRing G p]

-- Fix the Witt-ring structures to the same normed-field projections used by value.
def mapEquiv (e : F ≃+* G) := WittRingEquiv.mapEquiv p e

theorem digits_map (e : F →+* G) (x : WittVector p F) (n : ℕ) :
    digits p (WittVector.map e x) n = e (digits p x n) :=
  congrFun (digits_unique p _ _
    (expands_map p e x (digits p x) (expands_digits p x))).symm n

theorem value_map_pow (e : F →+* G) (d : ℕ) (hd : 0 < d)
    (hnorm : ∀ z : F, ‖e z‖ ^ d = ‖z‖)
    (ρ : ℝ≥0∞) (x : WittVector p F) :
    value p ρ (WittVector.map e x) ^ d = value p (ρ ^ d) x := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  unfold value
  calc
    (⨆ n : ℕ, ENNReal.ofReal ‖digits p (WittVector.map e x) n‖ * ρ ^ n) ^ d =
        ⨆ n : ℕ, (ENNReal.ofReal ‖digits p (WittVector.map e x) n‖ * ρ ^ n) ^ d := by
      simpa only [ENNReal.orderIsoRpow_apply, ENNReal.rpow_natCast] using
        (ENNReal.orderIsoRpow (d : ℝ) hdR).map_iSup
          (fun n : ℕ => ENNReal.ofReal ‖digits p (WittVector.map e x) n‖ * ρ ^ n)
    _ = ⨆ n : ℕ, ENNReal.ofReal ‖digits p x n‖ * (ρ ^ d) ^ n := by
      apply iSup_congr
      intro n
      rw [mul_pow, digits_map, ← ENNReal.ofReal_pow (norm_nonneg _) d, hnorm]
      congr 1
      exact (pow_mul ρ n d).symm.trans
        ((congrArg (fun k : ℕ => ρ ^ k) (Nat.mul_comm n d)).trans (pow_mul ρ d n))

theorem value_mapEquiv_pow (e : F ≃+* G) (d : ℕ) (hd : 0 < d)
    (hnorm : ∀ z : F, ‖e z‖ ^ d = ‖z‖) (ρ : ℝ≥0∞) (x : WittVector p F) :
    value p ρ (mapEquiv p e x) ^ d = value p (ρ ^ d) x :=
  value_map_pow p e.toRingHom d hd hnorm ρ x

end
end JoshiTeich.Act1Scene1.WittWeightedMapPower
