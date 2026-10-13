/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: selected small-ball surjectivity proof; independent namespace,
exact imports, and new normalized image and scalar-ball proofs.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.LinearCombination

/-!
source-id: JT-SCENE1-LOCAL-LOG-BALL
fidelity: constructs the full local unit ball as an image of the normalized
ordinary logarithm, and identifies scalar integral balls. Tensor products,
Bloch-Kato classes and Haar volume are separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog

open Filter Topology
open scoped Valued

universe u
noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CompleteSpace k] {p : ℕ}

/-- **Surjectivity of the logarithm**: every `y` with `‖y‖ ≤ ‖2p‖` is `log (1 + a)` for some
`a` with `‖a‖ ≤ ‖2p‖` (Banach's fixed point theorem for `a ↦ y - (log (1 + a) - a)`). -/
theorem exists_padicLog_eq [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k}
    (hy : ‖y‖ ≤ ‖2 * (p : k)‖) : ∃ a : k, ‖a‖ ≤ ‖2 * (p : k)‖ ∧ padicLog (1 + a) = y := by
  set R := ‖2 * (p : k)‖ with hR
  let T : k → k := fun a => y - logRem a
  have hT : Set.MapsTo T (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
    calc ‖y - logRem a‖ ≤ max ‖y‖ ‖logRem a‖ := by
          rw [sub_eq_add_neg]
          simpa using IsUltrametricDist.norm_add_le_max y (-logRem a)
      _ ≤ R := max_le hy ((norm_logRem_le hp hpk ha).trans
          ((mul_le_of_le_one_left (norm_nonneg _) hpk.le).trans ha))
  have hc : ContractingWith ‖(p : k)‖₊ (hT.restrict T _ _) := by
    refine ⟨by simpa [← NNReal.coe_lt_one] using hpk, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have ha : ‖(a : k)‖ ≤ R := by
      have := a.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hb : ‖(b : k)‖ ≤ R := by
      have := b.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    change ‖(y - logRem (a : k)) - (y - logRem (b : k))‖ ≤ ‖(p : k)‖ * ‖(a : k) - (b : k)‖
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact norm_logRem_sub_le hp hpk ha hb
  obtain ⟨a, ha, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hT hc (x := 0)
    (Metric.mem_closedBall_self (norm_nonneg _)) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at ha
  refine ⟨a, ha, ?_⟩
  have hfix' : y - logRem a = a := hfix
  rw [padicLog_one_add hp hpk (ha.trans_lt (norm_two_mul_lt_one hpk))]
  linear_combination -hfix'


/-- Every integral element has a preimage under the normalized logarithm. -/
theorem exists_normalizedLog_eq [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {y : k} (hy : ‖y‖ ≤ 1) : ∃ x : k, ‖x‖ ≤ 1 ∧ normalizedLog p x = y := by
  have h2p : 2 * (p : k) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk (y := 2 * (p : k) * y)
    (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hy)
  refine ⟨(2 * (p : k))⁻¹ * a, ?_, ?_⟩
  · rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_le_one (norm_pos_iff.mpr h2p)]
    exact ha
  · change (2 * (p : k))⁻¹ * padicLog (1 + (2 * (p : k)) * ((2 * (p : k))⁻¹ * a)) = y
    rw [mul_inv_cancel_left₀ h2p, hlog, inv_mul_cancel_left₀ h2p]

/-- The unit ball is exactly the normalized logarithm image of the unit ball. -/
theorem normalizedLog_image_closedBall [CharZero k] (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) :
    normalizedLog p '' Metric.closedBall (0 : k) 1 = Metric.closedBall (0 : k) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_normalizedLog hp hpk hx]
    exact hx
  · intro hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    obtain ⟨x, hx, hxy⟩ := exists_normalizedLog_eq hp hpk hy
    exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, hxy⟩

/-- The log-shell contains the full unit ball, not only an element of each norm. -/
theorem closedBall_subset_logShell [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Metric.closedBall (0 : k) 1 ⊆ logShell p := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  obtain ⟨x, hx, rfl⟩ := exists_normalizedLog_eq hp hpk hy
  exact normalizedLog_mem_logShell hp hpk hx

/-- A nonzero scalar times the integral unit ball is its full closed norm ball. -/
theorem mul_image_closedBall (z : k) (hz : z ≠ 0) :
    (fun x : k => z * x) '' Metric.closedBall (0 : k) 1 =
      Metric.closedBall (0 : k) ‖z‖ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx
  · intro hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    refine ⟨y / z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_div,
        div_le_one (norm_pos_iff.mpr hz)]
      exact hy
    · exact mul_div_cancel₀ y hz

end
end JoshiTeich.Act1Scene1.LocalPadicLog
