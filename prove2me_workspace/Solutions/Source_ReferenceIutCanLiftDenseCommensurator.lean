/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/Commensurator.lean
-/
import Solutions.Source_ReferenceIutCanLiftDenseCriterion
import Solutions.Source_ReferenceIutCanLiftDiscreteOvergroupIndex
import Solutions.Source_ReferenceIutCanLiftFrickeSquaredTraces

set_option autoImplicit false

open Filter Topology UpperHalfPlane
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- A subgroup is discrete if its identity is isolated. -/
private lemma discreteTopology_of_nhdsWithin_eq_bot {H : Subgroup SL(2, ℝ)}
    (h : 𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ)) = ⊥) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  have hmem : (∅ : Set SL(2, ℝ)) ∈ 𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ)) := by
    rw [h]
    exact Filter.mem_bot
  obtain ⟨U, hUo, h1U, hU⟩ := mem_nhdsWithin.mp hmem
  refine isOpen_induced_iff.mpr ⟨U, hUo, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have : (x : SL(2, ℝ)) ∈ U ∩ ((H : Set SL(2, ℝ)) \ {1}) :=
      ⟨hx, x.2, fun h ↦ hne (Subtype.ext h)⟩
    exact hU this
  · rintro rfl
    exact h1U

namespace Peripheral

open AbcAdaptation.Reference.Heights Generators Fricke

/-- If the lattice generators have infinite index in their commensurator, their commensurator
is dense in `SL(2, ℝ)`. The discrete case is excluded by the covolume of the signed deck group. -/
theorem closure_commensurator_dense_of_relIndex_eq_zero {t : ℍ}
    (U : LatticeComplementCover (periodPair t))
    (hno : (Subgroup.closure {A U, B U}).relIndex (commensurator (Subgroup.closure {A U, B U})) = 0) :
    Dense (commensurator (Subgroup.closure {A U, B U}) : Set SL(2, ℝ)) := by
  let Γ : Subgroup SL(2, ℝ) := Subgroup.closure {A U, B U}
  have hcomm : tr (A U * B U * (A U)⁻¹ * (B U)⁻¹) = -2 := trace_commutator U
  obtain ⟨hA4, hB4, _⟩ := traces_sq_gt_four U
  have hB : tr (B U) ≠ 0 := sq_pos_iff.mp ((by norm_num : (0 : ℝ) < 4).trans hB4)
  have hAΓ : A U ∈ Γ := Subgroup.subset_closure (by simp)
  have hBΓ : B U ∈ Γ := Subgroup.subset_closure (by simp)
  refine SL2R.dense_of_not_discrete (le_commensurator Γ hAΓ) (le_commensurator Γ hBΓ)
    hA4 (by rw [hcomm]; norm_num) hB ?_
  rw [Filter.neBot_iff]
  intro h
  letI : DiscreteTopology (commensurator Γ) := discreteTopology_of_nhdsWithin_eq_bot h
  exact closure_relIndex_commensurator_ne_zero_of_discrete U hno

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
