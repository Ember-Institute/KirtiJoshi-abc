/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Solutions.Source_ReferenceIutCanLiftFrickeComplexTraceRationality
import Solutions.Source_ReferenceIutCanLiftFrickePadicTraceBound
import Solutions.Source_ReferenceIutCanLiftFrickeTraceTransport
import Solutions.Source_ReferenceIutCanLiftPadicSquaredTraces

set_option autoImplicit false

open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (tr nA nB)

/-- **Integrality.** For a normal-form group with dense commensurator, all squared traces are
integers. -/
theorem trace_sq_int_of_dense {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ))) :
    ∀ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, ∃ m : ℤ, tr γ ^ 2 = m := by
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := sq_rat_of_dense hz hrel hx hy h1 h2 h3 hdense
  intro γ hγ
  have hγ' := isRatMul_of_mem_normalForm hz hrel hX.symm hY.symm hZ.symm hγ
  refine exists_int_sq_tr_of_padicNorm_le_one hγ'.spec fun p hp ↦ ?_
  letI : Fact p.Prime := ⟨hp⟩
  exact padicNorm_trace_sq_le_one hz hrel hX.symm hY.symm hZ.symm hx hy h1 h2 h3 hdense p hγ hγ'

/-- The normal-form integrality input for the Fricke trace transport. -/
theorem normalFormTraceIntegrality : NormalFormTraceIntegrality := trace_sq_int_of_dense

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
