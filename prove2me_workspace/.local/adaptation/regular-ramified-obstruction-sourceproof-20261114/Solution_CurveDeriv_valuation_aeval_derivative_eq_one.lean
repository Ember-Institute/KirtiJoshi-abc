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

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}


theorem solution (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {q : ℚ[X]} (hq : q.Separable) (hv : O.valuation (aeval x q) < 1) :
    O.valuation (aeval x (derivative q)) = 1 := by
  obtain ⟨a, b, hab⟩ := hq
  have h : aeval x a * aeval x q + aeval x b * aeval x (derivative q) = 1 := by
    simpa using congrArg (aeval x) hab
  refine ((O.valuation_le_one_iff _).mpr (aeval_mem hQ hx _)).antisymm (not_lt.mp fun hlt => ?_)
  have h1 : O.valuation (aeval x a * aeval x q) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr
      (aeval_mem hQ hx _))) hv
  have h2 : O.valuation (aeval x b * aeval x (derivative q)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr
      (aeval_mem hQ hx _))) hlt
  have := O.valuation.map_add_lt h1 h2
  rw [h, map_one] at this
  exact lt_irrefl _ this

end
