/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Modified adaptation, 2026-11-14: exact concrete Northcott proof from
refer/iut/Iut/Tripod/Northcott.lean. Uses the existing independent tripod
carrier and Mathlib only. Source hashes and revision status: SOURCE_MANIFEST.json.
-/
import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open Polynomial Northcott

/-- Exact source finite-quotient-set composer. No new assumption remains
when the two supplied closed source proofs are applied. -/
theorem boundedDegreeFiniteness_of_northcott_children
    (hRoots : Northcott.FiniteRoots)
    (hWitness : Northcott.PolynomialWitness) : BoundedDegreeFiniteness := by
  classical
  intro d H
  -- the finite set `T` of the quotients `y / n` of the roots `y` of the polynomials of
  -- `polySet d H` by the integers `1 ≤ n ≤ heightBound d H`
  have hTfin : (⋃ n ∈ Finset.Icc 1 ⌊heightBound d H⌋₊, (fun y : Qbar ↦ (n : Qbar)⁻¹ * y) ''
      (⋃ f ∈ polySet d H, ((f.map (Int.castRingHom Qbar)).roots.toFinset : Set Qbar))).Finite :=
    (Finset.finite_toSet _).biUnion fun n _ ↦ (hRoots d H).image _
  refine (hTfin.preimage Subtype.val_injective.injOn).subset fun x ⟨hd, hH⟩ ↦ ?_
  obtain ⟨n, hn0, hnB, p, hp, hpm, hroot⟩ := hWitness hd hH
  have hn' : (n : Qbar) ≠ 0 := by exact_mod_cast hn0
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Finset.mem_Icc,
    Multiset.mem_toFinset, exists_prop]
  refine ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_floor hnB⟩, (n : Qbar) * x.1,
    ⟨p, hp, ?_⟩, inv_mul_cancel_left₀ hn' _⟩
  rw [mem_roots (hpm.map (Int.castRingHom Qbar)).ne_zero, IsRoot.def, eval_map]
  exact hroot


end AbcAdaptation.Tripod
