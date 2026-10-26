import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricLogTailBounds
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Algebra.Ring.GeomSum

/-!
source-id: JT-SCENE1-ULTRAMETRIC-POWER-SERIES-CONTRACTION
source: Joshi II `pr:teichmuller-lift-A`, the logarithmic evaluation
in the period exact sequence; the ordinary nonarchimedean logarithm.
fidelity: polynomial coefficient growth gives actual series convergence.
On a sufficiently small ball, the degree-at-least-two remainder is a
contraction of factor one half. The original norm and topology are used;
there is no discrete valuation assumption or inverse-series input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the actual logarithm coefficients and period
evaluation are supplied by separately proved consumers.
-/

namespace JoshiTeich.Act1Scene1.UltrametricPowerSeriesContraction

open Filter
open scoped Topology
noncomputable section
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem summable_series (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) (x : K) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => c n * x ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply squeeze_zero_norm (fun n => ?_)
    (tendsto_pow_const_mul_const_pow_of_lt_one k (norm_nonneg x) hx)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hc n) (pow_nonneg (norm_nonneg x) n)

def remainder (c : ℕ → K) (x : K) : K := ∑' n : ℕ, c (n + 2) * x ^ (n + 2)

theorem remainder_zero (c : ℕ → K) : remainder c 0 = 0 := by
  simp [remainder]

theorem norm_pow_sub_le {a b : K} {R : ℝ} (hR : 0 ≤ R)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ R ^ n * ‖a - b‖ := by
  have he : a ^ (n + 1) - b ^ (n + 1) =
      (∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n + 1 - 1 - i)) * (a - b) := by
    rw [geom_sum₂_mul]
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR n) ?_
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [norm_mul, norm_pow, norm_pow]
  calc
    _ ≤ R ^ i * R ^ (n + 1 - 1 - i) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg a) ha i)
        (pow_le_pow_left₀ (norm_nonneg b) hb _) (pow_nonneg (norm_nonneg b) _) (pow_nonneg hR i)
    _ = R ^ n := by
      rw [← pow_add]
      congr 1
      omega

theorem polynomial_geometric_slope_le (k n : ℕ) (R : ℝ) (hR : 0 < R)
    (hs : (2 : ℝ) ^ k * R ≤ 1 / 2) :
    (n + 2 : ℝ) ^ k * R ^ (n + 1) ≤ 1 / 2 := by
  have h := UltrametricLogTailBounds.polynomial_geometric_tail_le k n R hR.le hs
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ] at h
  nlinarith

theorem norm_remainder_term_sub_le (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) {a b : K} {R : ℝ}
    (hR : 0 < R) (hs : (2 : ℝ) ^ k * R ≤ 1 / 2)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (n : ℕ) :
    ‖c (n + 2) * a ^ (n + 2) - c (n + 2) * b ^ (n + 2)‖ ≤
      (1 / 2 : ℝ) * ‖a - b‖ := by
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ (n + 2 : ℝ) ^ k * (R ^ (n + 1) * ‖a - b‖) :=
      mul_le_mul (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hc (n + 2))
        (norm_pow_sub_le hR.le ha hb (n + 1)) (norm_nonneg _) (by positivity)
    _ = ((n + 2 : ℝ) ^ k * R ^ (n + 1)) * ‖a - b‖ := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (polynomial_geometric_slope_le k n R hR hs) (norm_nonneg _)

theorem norm_remainder_sub_le (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) {a b : K} {R : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (hs : (2 : ℝ) ^ k * R ≤ 1 / 2)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖remainder c a - remainder c b‖ ≤ (1 / 2 : ℝ) * ‖a - b‖ := by
  have hsa := (summable_nat_add_iff 2).mpr (summable_series c k hc a (ha.trans_lt hR1))
  have hsb := (summable_nat_add_iff 2).mpr (summable_series c k hc b (hb.trans_lt hR1))
  unfold remainder
  rw [← hsa.tsum_sub hsb]
  exact UltrametricLogTailBounds.norm_tsum_le_of_forall_le _ (hsa.sub hsb) _
    (mul_nonneg (by norm_num) (norm_nonneg _))
      (norm_remainder_term_sub_le c k hc hR hs ha hb)

theorem norm_remainder_le (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) {a : K} {R : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (hs : (2 : ℝ) ^ k * R ≤ 1 / 2) (ha : ‖a‖ ≤ R) :
    ‖remainder c a‖ ≤ (1 / 2 : ℝ) * ‖a‖ := by
  simpa only [remainder_zero, sub_zero] using
    norm_remainder_sub_le c k hc hR hR1 hs ha (b := 0) (by simpa using hR.le)

end
end JoshiTeich.Act1Scene1.UltrametricPowerSeriesContraction
