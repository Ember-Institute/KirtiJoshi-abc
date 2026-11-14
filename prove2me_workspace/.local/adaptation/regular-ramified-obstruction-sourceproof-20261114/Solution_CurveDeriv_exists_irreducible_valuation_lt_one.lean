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
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/- Private proof closure from Definitions/Def_FermatCurveDerivationValuationElementary.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}

private theorem valuation_algebraMap_rat (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {q : ℚ} (hq : q ≠ 0) :
    O.valuation (algebraMap ℚ K q) = 1 := by
  have h1 := (O.valuation_le_one_iff _).mpr (hQ q)
  have h2 := (O.valuation_le_one_iff _).mpr (hQ q⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  have h0 : O.valuation (algebraMap ℚ K q) ≠ 0 := by simpa using hq
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)


variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr





end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}

theorem solution (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {p : ℚ[X]} (hp : p ≠ 0) (hv : O.valuation (aeval x p) < 1) :
    ∃ q : ℚ[X], Irreducible q ∧ O.valuation (aeval x q) < 1 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hp
  | unit u hu =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [aeval_C, valuation_algebraMap_rat hQ hc.ne_zero] at hv
    exact absurd hv (lt_irrefl 1)
  | mul a i ha hi ih =>
    rw [map_mul, map_mul] at hv
    rcases (O.valuation_le_one_iff _).mpr (aeval_mem hQ hx i) |>.lt_or_eq with h | h
    · exact ⟨i, hi, h⟩
    · rw [h, one_mul] at hv
      exact ih ha hv


end
