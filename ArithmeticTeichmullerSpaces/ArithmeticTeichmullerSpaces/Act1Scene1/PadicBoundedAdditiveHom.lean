import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Group.Basic

/-!
source-id: JT-SCENE1-PADIC-BOUNDED-ADDITIVE-HOM
source: Joshi II `eq:tate-module-of-lubin-tate`, continuity and integral
scalar compatibility for the rank-one Tate module.
fidelity: a bounded additive map out of Z_p is continuous when natural
p-power multiplication contracts geometrically in its target. A continuous
additive map into a topological Q_p module agrees with scalar multiplication
by its value at one, using the actual dense natural-number inclusion.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; consumers must prove boundedness and contraction.
-/

namespace JoshiTeich.Act1Scene1.PadicBoundedAdditiveHom

open scoped Topology
variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [NormedAddCommGroup E]

theorem continuous_of_bounded (f : PadicInt p →+ E) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hscale : ∀ (n : ℕ) (x : E), ‖(p ^ n) • x‖ ≤ r ^ n * ‖x‖)
    (C : ℝ) (hbound : ∀ a, ‖f a‖ ≤ C) : Continuous f := by
  apply continuous_of_continuousAt_zero f
  rw [Metric.continuousAt_iff]
  intro ε hε
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨(p : ℝ) ^ (-(n : ℤ)), zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _, ?_⟩
  intro a ha
  have hd : (p : PadicInt p) ^ n ∣ a := by
    rw [← Ideal.mem_span_singleton]
    apply (PadicInt.norm_le_pow_iff_mem_span_pow a n).mp
    exact (by simpa only [dist_zero_right] using ha : ‖a‖ < (p : ℝ) ^ (-(n : ℤ))).le
  obtain ⟨b, rfl⟩ := hd
  rw [map_zero, dist_zero_right]
  have he : f ((p : PadicInt p) ^ n * b) = (p ^ n) • f b := by
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul]
  rw [he]
  exact ((hscale n (f b)).trans
    (mul_le_mul_of_nonneg_left (hbound b) (pow_nonneg hr n))).trans_lt hn

theorem map_eq_smul_one [Module (Padic p) E] [ContinuousSMul (Padic p) E]
    (f : PadicInt p →+ E) (hf : Continuous f) (a : PadicInt p) :
    f a = (a : Padic p) • f 1 := by
  refine PadicInt.denseRange_natCast.induction_on a ?_ ?_
  · exact isClosed_eq hf (continuous_subtype_val.smul continuous_const)
  · intro n
    have hn := f.map_nsmul n 1
    simpa only [nsmul_eq_mul, mul_one, PadicInt.coe_natCast, Nat.cast_smul_eq_nsmul] using hn

end JoshiTeich.Act1Scene1.PadicBoundedAdditiveHom
