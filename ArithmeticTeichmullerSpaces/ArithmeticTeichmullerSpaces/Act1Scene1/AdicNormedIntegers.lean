import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Ultra

/-!
source-id: JT-SCENE1-ADIC-NORMED-INTEGERS-COMPLETENESS
source: Mathlib IsAdic.isPrecomplete_iff and the normed-field unit-ball
completeness criterion; the de Rham period field used in Joshi II.
fidelity: proves completeness in the existing norm topology from explicit
ideal-power balls and an isometric integer inclusion. Original proofs;
no copied reference-engine code or change to Prologue-R5.
-/

namespace JoshiTeich.Act1Scene1.AdicNormedIntegers

open scoped Topology
noncomputable section
variable {R K : Type*} [NormedCommRing R] [NormedField K] [IsUltrametricDist K]
variable (f : R →+* K) (hf : Isometry f) (I : Ideal R) (π : R)
variable (hballs : ∀ n : ℕ, ((I ^ n : Ideal R) : Set R) = f ⁻¹' Metric.closedBall 0 (‖f π‖ ^ n))

include hf hballs in
theorem isAdic (hπ0 : f π ≠ 0) (hπ1 : ‖f π‖ < 1) : IsAdic I := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [hballs]
    exact (IsUltrametricDist.isOpen_closedBall 0
      (pow_ne_zero n (norm_ne_zero_iff.mpr hπ0))).preimage hf.continuous
  · intro S hS
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    refine ⟨n, ?_⟩
    rw [hballs]
    intro x hx
    apply hball
    rw [Metric.mem_ball, ← hf.dist_eq x 0, map_zero, dist_zero_right]
    have hx' : ‖f x‖ ≤ ‖f π‖ ^ n := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hx
    exact hx'.trans_lt hn

include hf hballs in
theorem sourceComplete [IsAdicComplete I R] (hπ0 : f π ≠ 0) (hπ1 : ‖f π‖ < 1) :
    CompleteSpace R :=
  (isAdic f hf I π hballs hπ0 hπ1).isPrecomplete_iff.mp inferInstance

include hf in
omit [IsUltrametricDist K] in
theorem fieldComplete [CompleteSpace R]
    (hrange : Set.range f = Metric.closedBall 0 1) : CompleteSpace K := by
  apply NormedField.completeSpace_iff_isComplete_closedBall.mpr
  rw [← hrange]
  exact hf.isUniformInducing.isComplete_range

end
end JoshiTeich.Act1Scene1.AdicNormedIntegers
