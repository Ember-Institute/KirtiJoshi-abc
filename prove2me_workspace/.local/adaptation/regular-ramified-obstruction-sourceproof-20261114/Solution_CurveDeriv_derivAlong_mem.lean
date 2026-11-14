/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Complete source proof transport from pinned Belyi
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Canonical node layout; source statements and proof bodies stay unchanged.
See source-consumer.json and private-owners.json for every source copy.
-/
import Definitions.Def_FermatCurveDerivationAdjoin
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_succ_mul_derivAlong_not_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] (O : ValuationSubring K)

theorem solution {π : K} (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
    (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
    (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
    [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
    {x : K} (hx : x ∈ O) : derivAlong π x ∈ O := by
  by_contra h
  obtain ⟨N, hN⟩ := exists_pow_mul_derivAlong_mem ht hQ hπO hirr
  have key : ∀ k : ℕ, ∃ y ∈ O, π ^ k * derivAlong π y ∉ O := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simpa using h⟩
    | succ k ih =>
      obtain ⟨y, hy, hk⟩ := ih
      exact exists_pow_succ_mul_derivAlong_not_mem ht hQ hres hπO hirr hy hk
  obtain ⟨y, hy, hN'⟩ := key N
  exact hN' (hN y hy)

end
