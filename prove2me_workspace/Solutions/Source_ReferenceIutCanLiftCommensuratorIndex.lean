/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/U2/R3.lean and OrbicurveCores/Fuchsian/Commensurator.lean
-/
import Solutions.Source_ReferenceIutCanLiftUniformizationUnique
import Mathlib.GroupTheory.Commensurable

set_option autoImplicit false

open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Subgroup.Commensurable

/-- A subgroup is contained in its commensurator. -/
theorem le_commensurator {G : Type*} [Group G] (Γ : Subgroup G) : Γ ≤ commensurator Γ := by
  intro g hg
  rw [commensurator_mem_iff, Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hg)]

theorem commensurator_smul {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    commensurator (ConjAct.toConjAct g • H) = ConjAct.toConjAct g • commensurator H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, commensurator_mem_iff, commensurator_mem_iff,
    commensurable_conj (ConjAct.toConjAct g)⁻¹, inv_smul_smul]
  have e : (ConjAct.toConjAct g)⁻¹ • x = g⁻¹ * x * g := by
    rw [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [e, map_mul, map_mul, map_inv, mul_smul, mul_smul]

/-- Commensurable subgroups have finite index in their common commensurator simultaneously. -/
theorem relIndex_commensurator_ne_zero_iff {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : Subgroup.Commensurable H K) :
    H.relIndex (commensurator H) ≠ 0 ↔ K.relIndex (commensurator K) ≠ 0 := by
  rw [← hHK.eq]
  exact ⟨Subgroup.relIndex_ne_zero_trans hHK.2, Subgroup.relIndex_ne_zero_trans hHK.1⟩

namespace IsUniformization

theorem commensurable_closure_pmGroup (A B : SL(2, ℝ)) :
    Subgroup.Commensurable (Subgroup.closure {A, B}) (pmGroup A B) := by
  refine ⟨relIndex_closure_pmGroup_ne_zero A B, ?_⟩
  rw [Subgroup.relIndex_eq_one.mpr (closure_le_pmGroup A B)]
  exact one_ne_zero

theorem relIndex_commensurator_closure_ne_zero_iff_pmGroup (A B : SL(2, ℝ)) :
    (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) ≠ 0 ↔
      (pmGroup A B).relIndex (commensurator (pmGroup A B)) ≠ 0 :=
  relIndex_commensurator_ne_zero_iff (commensurable_closure_pmGroup A B)

variable {W : WeierstrassCurve ℂ} {A B A' B' : SL(2, ℝ)} {π π' : ℂ → ℂ × ℂ}

/-- Finite commensurator index is independent of the uniformization of the affine curve. -/
theorem relIndex_commensurator_ne_zero_iff_of_uniformization [W.IsElliptic]
    (h : IsUniformization W A B π) (h' : IsUniformization W A' B' π') :
    (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) ≠ 0 ↔
      (Subgroup.closure {A', B'}).relIndex (commensurator (Subgroup.closure {A', B'})) ≠ 0 := by
  obtain ⟨g, -, hg⟩ := h.unique h'
  have hconj : ConjAct.toConjAct g • pmGroup A' B' = pmGroup A B := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [ConjAct.toConjAct_smul]
      exact (hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hg _).mpr ?_, ?_⟩
      · rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      · rw [ConjAct.toConjAct_smul]
        group
  rw [relIndex_commensurator_closure_ne_zero_iff_pmGroup A B,
    relIndex_commensurator_closure_ne_zero_iff_pmGroup A' B', ← hconj, commensurator_smul,
    Subgroup.relIndex_pointwise_smul]

end IsUniformization
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
