import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
source-id: JT-SCENE1-CLOSED-FIELD-EMBEDDING-NORM
source: Mathlib equivalence of real absolute values and convergence of powers;
Joshi III relative-degree normalization for local untilt comparisons.
fidelity: a topological field embedding preserves the norm<1 condition.
An explicit nontrivial calibration value determines its norm power law.
Original proofs; no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.ClosedFieldEmbeddingNorm

open scoped Topology
noncomputable section
variable {E F : Type*} [NormedField E] [NormedField F] (f : E →+* F)

def pullback : AbsoluteValue E ℝ where
  toFun x := ‖f x‖
  map_mul' x y := by rw [map_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by rw [norm_eq_zero, map_eq_zero]
  add_le' x y := by rw [map_add]; exact norm_add_le _ _

theorem norm_lt_one_iff (hf : Topology.IsEmbedding f) (x : E) : ‖f x‖ < 1 ↔ ‖x‖ < 1 := by
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  have h := hf.tendsto_nhds_iff (f := fun n : ℕ => x ^ n) (l := Filter.atTop) (y := 0)
  simpa only [Function.comp_def, map_pow, map_zero] using h.symm

theorem norm_eq_pow (hf : Topology.IsEmbedding f) (a : E) (d : ℕ)
    (ha0 : f a ≠ 0) (ha1 : ‖f a‖ < 1) (hcal : ‖a‖ = ‖f a‖ ^ d) (x : E) :
    ‖x‖ = ‖f x‖ ^ d := by
  have hequiv : (pullback f).IsEquiv (pullback (RingHom.id E)) :=
    AbsoluteValue.isEquiv_iff_lt_one_iff.mpr (norm_lt_one_iff f hf)
  obtain ⟨c, _, hc⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hc' : c = (d : ℝ) := by
    apply (Real.rpow_right_inj (norm_pos_iff.mpr ha0) (ne_of_lt ha1)).mp
    have h := congrFun hc a
    change ‖f a‖ ^ c = ‖a‖ at h
    rw [hcal, ← Real.rpow_natCast] at h
    exact h
  have h := congrFun hc x
  change ‖f x‖ ^ c = ‖x‖ at h
  rw [hc', Real.rpow_natCast] at h
  exact h.symm

end
end JoshiTeich.Act1Scene1.ClosedFieldEmbeddingNorm
