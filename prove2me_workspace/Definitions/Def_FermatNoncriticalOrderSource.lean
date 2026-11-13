/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of complete source proofs in
Belyi/CurveField/{NoncriticalBasic,NoncriticalElem}.lean.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
See source-consumer.json for source hashes, proof boundaries and consumers.
-/
import Definitions.Def_FermatNoncriticalRamificationPositive
import Mathlib.Tactic.Push

set_option autoImplicit false
open Polynomial
namespace AbcAdaptation.Tripod.Fermat.Proper
namespace Place
variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] (P : Place K)

theorem noncritical_ord_eq_zero_of_residue_ne_zero {y : K} (hy : y ∈ P.1)
    (h : P.residue ⟨y, hy⟩ ≠ 0) : P.ord y = 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact h (by rw [show (⟨0, hy⟩ : P.1) = 0 from rfl, map_zero])
  refine le_antisymm ?_ (P.ord_nonneg_of_mem hy)
  by_contra hlt
  push Not at hlt
  exact h ((P.residue_eq_zero_iff).mpr ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, hy⟩) hy0).mp hlt))

theorem noncritical_residue_eq_zero_of_ord_pos {y : K} (hy : 0 < P.ord y) :
    P.residue ⟨y, P.mem_of_ord_nonneg hy.le⟩ = 0 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  exact (P.residue_eq_zero_iff).mpr ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, _⟩) hy0).mp hy)

end Place
end AbcAdaptation.Tripod.Fermat.Proper
