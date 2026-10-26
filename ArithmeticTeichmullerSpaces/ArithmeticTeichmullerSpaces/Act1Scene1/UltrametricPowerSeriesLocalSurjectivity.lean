import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricPowerSeriesContraction
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.LinearCombination

/-!
source-id: JT-SCENE1-ULTRAMETRIC-POWER-SERIES-LOCAL-SURJECTIVITY
source: Joshi II `pr:teichmuller-lift-A`, logarithmic evaluation in
the period exact sequence; Banach's fixed point theorem.
fidelity: a series with zero constant coefficient, linear coefficient
one and polynomial coefficient bounds maps a proved small closed ball
onto that ball. Constructs a fixed point of y minus the actual series
remainder. Works in the original complete ultrametric normed field,
including fields with nondiscrete value group.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; period consumers must prove their actual
coefficient bounds and use the resulting convergent series.
-/

namespace JoshiTeich.Act1Scene1.UltrametricPowerSeriesLocalSurjectivity

open UltrametricPowerSeriesContraction
open scoped Topology
noncomputable section
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem hasSum_linear_add_remainder (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) (hc0 : c 0 = 0) (hc1 : c 1 = 1)
    (a : K) (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => c n * a ^ n) (a + remainder c a) := by
  apply (hasSum_nat_add_iff' 2).mp
  have h := ((summable_nat_add_iff 2).mpr (summable_series c k hc a ha)).hasSum
  simpa [Finset.sum_range_succ, hc0, hc1, remainder] using h

theorem exists_hasSum_of_norm_le (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) (hc0 : c 0 = 0) (hc1 : c 1 = 1)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) (hs : (2 : ℝ) ^ k * R ≤ 1 / 2)
    (y : K) (hy : ‖y‖ ≤ R) :
    ∃ a : K, ‖a‖ ≤ R ∧ HasSum (fun n : ℕ => c n * a ^ n) y := by
  let T : K → K := fun a => y - remainder c a
  have hT : Set.MapsTo T (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
    calc
      ‖y - remainder c a‖ ≤ max ‖y‖ ‖remainder c a‖ := by
        simpa only [sub_eq_add_neg, norm_neg] using
          IsUltrametricDist.norm_add_le_max y (-remainder c a)
      _ ≤ R := max_le hy ((norm_remainder_le c k hc hR hR1 hs ha).trans (by nlinarith))
  have hcontract : ContractingWith (1 / 2 : NNReal) (hT.restrict T _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have ha : ‖(a : K)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using a.property
    have hb : ‖(b : K)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using b.property
    change ‖(y - remainder c (a : K)) - (y - remainder c (b : K))‖ ≤
      (1 / 2 : ℝ) * ‖(a : K) - (b : K)‖
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact norm_remainder_sub_le c k hc hR hR1 hs ha hb
  obtain ⟨a, ha, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hT hcontract (x := 0)
    (Metric.mem_closedBall_self hR.le) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at ha
  refine ⟨a, ha, ?_⟩
  have he : a + remainder c a = y := by
    have h : y - remainder c a = a := hfix
    linear_combination -h
  rw [← he]
  exact hasSum_linear_add_remainder c k hc hc0 hc1 a (ha.trans_lt hR1)

theorem exists_local_surjectivity (c : ℕ → K) (k : ℕ)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ (n : ℝ) ^ k) (hc0 : c 0 = 0) (hc1 : c 1 = 1) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ y : K, ‖y‖ ≤ R →
      ∃ a : K, ‖a‖ ≤ R ∧ HasSum (fun n : ℕ => c n * a ^ n) y := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  let R : ℝ := (1 / 2) / (2 : ℝ) ^ k
  have hR : 0 < R := div_pos (by norm_num) hp
  have hR1 : R < 1 := (div_lt_iff₀ hp).mpr (by nlinarith)
  have hs : (2 : ℝ) ^ k * R ≤ 1 / 2 := by
    dsimp only [R]
    exact (mul_div_cancel₀ (1 / 2 : ℝ) hp.ne').le
  exact ⟨R, hR, hR1, fun y hy => exists_hasSum_of_norm_le c k hc hc0 hc1 hR hR1 hs y hy⟩

end
end JoshiTeich.Act1Scene1.UltrametricPowerSeriesLocalSurjectivity
