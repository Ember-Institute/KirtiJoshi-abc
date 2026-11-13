/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of the finite-exception composition in
Iut/Implication/Corollary23.lean. This file imports only the predicates,
not the file containing the open mathematical children.
-/
import Definitions.Def_TripodStatementIIInputs
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- The two exact children imply the imported concrete `StatementII`.
The zero-degree case is empty. For positive degree, Northcott makes the
low-height exceptional set finite; its discrepancy has a real upper bound.
This proof uses the children only as explicit hypotheses. -/
theorem statementII_of_children
    (hFinite : BoundedDegreeFiniteness)
    (hHigh : HighHeightEstimate) : StatementII := by
  intro d ε hε K
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst d
    refine ⟨0, ?_⟩
    intro x _ hxd
    exact False.elim ((Nat.not_le.mpr (deg_pos x.1)) hxd)
  · obtain ⟨H, C, hgood⟩ := hHigh d hd ε hε K
    let Exc : Set Pt :=
      {x | x ∈ K.set ∧ deg x.1 ≤ d ∧ htCan x ≤ H}
    have hExc : Exc.Finite := by
      apply (hFinite d H).subset
      intro x hx
      exact ⟨hx.2.1, hx.2.2⟩
    -- This also works when `Exc` is empty: no maximum point is chosen.
    obtain ⟨B, hB⟩ :=
      (hExc.image (fun x : Pt =>
        htCan x - (1 + ε) * (logDiff x + logCond x))).bddAbove
    refine ⟨max C B, ?_⟩
    intro x hxK hxd
    by_cases hxH : htCan x ≤ H
    · have hxExc : x ∈ Exc := ⟨hxK, hxd, hxH⟩
      have hxB : htCan x - (1 + ε) * (logDiff x + logCond x) ≤ B :=
        hB (Set.mem_image_of_mem _ hxExc)
      calc
        htCan x ≤ (1 + ε) * (logDiff x + logCond x) + B :=
          (sub_le_iff_le_add').mp hxB
        _ ≤ (1 + ε) * (logDiff x + logCond x) + max C B :=
          add_le_add le_rfl (le_max_right C B)
    · exact (hgood x hxK hxd (lt_of_not_ge hxH)).trans
        (add_le_add le_rfl (le_max_left C B))

end AbcAdaptation.Tripod
