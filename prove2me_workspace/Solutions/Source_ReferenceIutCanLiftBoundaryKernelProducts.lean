/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/FromProb.lean
Original lines 30–44 and 218–243
-/
import Solutions.Source_ReferenceIutCanLiftM2Setup
import Solutions.Source_ReferenceIutCanLiftThreePoint
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Urysohn

set_option autoImplicit false

/-!
# Boundary kernel products

The square and cube of a Markov kernel on the boundary, with the measurable set
of distinct triples and the product measures under the projective action.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology OnePoint.Proj
open scoped MatrixGroups ENNReal Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

instance polishSpace_onePoint : PolishSpace (OnePoint k) := by
  letI := TopologicalSpace.metrizableSpaceMetric (OnePoint k)
  haveI : CompleteSpace (OnePoint k) := complete_of_compact
  infer_instance

/-- Distinct triples. -/
def D3set : Set (Triple k) := {t | Distinct3 t}

omit [DecidableEq k] in
lemma measurableSet_D3set : MeasurableSet (D3set (k := k)) := isOpen_distinct3.measurableSet

omit [ProperSpace k] in
lemma smul3_preimage_D3set (g : GL (Fin 2) k) : smul3 g ⁻¹' D3set = (D3set (k := k)) := by
  ext t
  simp only [D3set, mem_preimage, mem_setOf_eq, Distinct3, smul3, ne_eq, smul_left_cancel_iff]

/-- The kernel `x ↦ κ(x)²`. -/
noncomputable abbrev kern2 (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] :
    Kernel (OnePoint ℝ) (OnePoint k × OnePoint k) := κ ×ₖ κ

/-- The kernel `x ↦ κ(x)³`. -/
noncomputable abbrev kern3 (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] :
    Kernel (OnePoint ℝ) (Triple k) := κ ×ₖ (κ ×ₖ κ)

lemma measurable_gl_smul (g : GL (Fin 2) k) : Measurable fun y : OnePoint k ↦ g • y :=
  (continuous_gl_smul g).measurable

lemma kern_map (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] {x y : OnePoint ℝ}
    {g : GL (Fin 2) k} (h : κ y = (κ x).map (fun z ↦ g • z)) :
    kern2 κ y = (kern2 κ x).map (Prod.map (fun z ↦ g • z) (fun z ↦ g • z)) ∧
      kern3 κ y = (kern3 κ x).map (smul3 g) := by
  have hm := measurable_gl_smul g
  constructor
  · rw [Kernel.prod_apply, Kernel.prod_apply, h, Measure.map_prod_map _ _ hm hm]
  · rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply, h,
      Measure.map_prod_map _ _ hm hm, Measure.map_prod_map _ _ hm (hm.prodMap hm)]
    rfl

omit [ProperSpace k] [DecidableEq k] in
lemma kern3_apply (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] (x : OnePoint ℝ) :
    kern3 κ x = (κ x).prod ((κ x).prod (κ x)) := by
  rw [Kernel.prod_apply, Kernel.prod_apply]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
