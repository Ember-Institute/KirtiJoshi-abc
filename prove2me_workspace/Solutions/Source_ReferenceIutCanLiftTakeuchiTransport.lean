/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Transport.lean
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiFourGroups
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelRigidity
import Solutions.Source_ReferenceIutCanLiftUniformizationTransport

set_option autoImplicit false

open Matrix.SpecialLinearGroup (toGL)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- Move the uniformization through the Nielsen generators, sign choices, and simultaneous
conjugacy from the Takeuchi classification. A negative determinant conjugates the curve. -/
theorem uniformizes_takeuchiPair_of_conjugacy (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (A B A' B' : SL(2, ℝ)) (hU : Uniformizes E (A, B))
    (hClosure : Subgroup.closure {A', B'} = Subgroup.closure {A, B})
    (i : Fin 4) (A'' B'' : SL(2, ℝ)) (hA'' : A'' ∈ ({A', -A'} : Set SL(2, ℝ)))
    (hB'' : B'' ∈ ({B', -B'} : Set SL(2, ℝ))) (g : GL (Fin 2) ℝ)
    (hgA : g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1)
    (hgB : g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2) :
    Uniformizes E (takeuchiPair i) ∨ Uniformizes (E.map (starRingEnd ℂ)) (takeuchiPair i) := by
  obtain ⟨π, hπ⟩ := hU
  have hSigned := (hπ.of_closure_eq hClosure).of_signs hA'' hB''
  rcases lt_or_gt_of_ne (show g.det.val ≠ 0 from g.det.ne_zero) with hNeg | hPos
  · exact Or.inr (hSigned.conj_neg hNeg hgA hgB)
  · exact Or.inl (hSigned.conj_pos hPos hgA hgB)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
