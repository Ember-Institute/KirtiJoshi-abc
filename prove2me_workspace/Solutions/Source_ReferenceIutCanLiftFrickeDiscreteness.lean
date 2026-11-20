/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/PingPong.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.GroupTheory.FreeGroup.Reduce
import Solutions.Source_ReferenceIutCanLiftFrickePingPong

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Topology
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

section NormalForm

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

include hx hy in
/-- **Ping-pong.** A reduced nonempty word maps `Q°` into the region of its first letter. -/
private lemma pp_word : ∀ (L : List (Fin 2 × Bool)) (s : Fin 2 × Bool), FreeGroup.IsReduced (s :: L) →
    ((s :: L).map (ppGen hz hrel)).prod • ppQ x y z ⊆ ppX x y z s := by
  intro L
  induction L with
  | nil =>
    intro s _
    simpa using pp_stepQ hx hy hz hrel s
  | cons t L ih =>
    intro s hL
    rw [FreeGroup.isReduced_cons_cons] at hL
    rw [List.map_cons, List.prod_cons, mul_smul]
    exact (Set.smul_set_mono (ih t hL.2)).trans (pp_step hx hy hz hrel s t hL.1)

/-- The generator map `Fin 2 → SL(2, ℝ)`. -/
private noncomputable def ppF : Fin 2 → SL(2, ℝ) := ![nA hz hrel, nB hz hrel]

private lemma lift_mk_eq (L : List (Fin 2 × Bool)) :
    FreeGroup.lift (ppF hz hrel) (FreeGroup.mk L) = (L.map (ppGen hz hrel)).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ -
  fin_cases i <;> cases b <;> rfl

include hx hy in
/-- Every nontrivial element moves `Q°` off itself. -/
private theorem pp_disjoint {g : FreeGroup (Fin 2)} (hg : g ≠ 1) :
    Disjoint (FreeGroup.lift (ppF hz hrel) g • ppQ x y z) (ppQ x y z) := by
  obtain ⟨s, L, hL⟩ : ∃ s L, g.toWord = s :: L := by
    rcases h : g.toWord with _ | ⟨s, L⟩
    · exact absurd (FreeGroup.toWord_eq_nil_iff.mp h) hg
    · exact ⟨s, L, rfl⟩
  have hred : FreeGroup.IsReduced (s :: L) := hL ▸ FreeGroup.isReduced_toWord
  rw [← FreeGroup.mk_toWord (x := g), hL, lift_mk_eq]
  exact Set.disjoint_of_subset_left (pp_word hx hy hz hrel L s hred)
    (ppX_disjoint_Q s)

private lemma range_lift_normal :
    (FreeGroup.lift (ppF hz hrel)).range = Subgroup.closure {nA hz hrel, nB hz hrel} := by
  rw [FreeGroup.range_lift_eq_closure]
  congr 1
  ext g
  simp only [ppF, Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

include hx hy in
/-- The Fricke normal-form subgroup of `SL(2, ℝ)` is discrete. -/
theorem discreteTopology_normal :
    DiscreteTopology (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  obtain ⟨w, hw⟩ := ppQ_nonempty hx hy hz
  have hcont : Continuous fun g : SL(2, ℝ) ↦ g • w := continuous_id.smul continuous_const
  refine isOpen_induced_iff.mpr
    ⟨(fun g : SL(2, ℝ) ↦ g • w) ⁻¹' ppQ x y z, ppQ_isOpen.preimage hcont, ?_⟩
  ext γ
  change ((γ : SL(2, ℝ)) • w) ∈ ppQ x y z ↔ γ ∈ ({1} : Set _)
  constructor
  · intro hγw
    have hγ : (γ : SL(2, ℝ)) ∈ (FreeGroup.lift (ppF hz hrel)).range := by
      simpa only [range_lift_normal] using γ.2
    obtain ⟨g, hg⟩ := hγ
    rcases eq_or_ne g 1 with rfl | hg1
    · exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa using hg.symm))
    · have hgw : FreeGroup.lift (ppF hz hrel) g • w ∈ ppQ x y z := hg.symm ▸ hγw
      exact False.elim (Set.disjoint_left.mp (pp_disjoint hx hy hz hrel hg1)
        (Set.smul_mem_smul_set hw) hgw)
  · intro hγ
    rw [Set.mem_singleton_iff] at hγ
    simpa [hγ] using hw

end NormalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
