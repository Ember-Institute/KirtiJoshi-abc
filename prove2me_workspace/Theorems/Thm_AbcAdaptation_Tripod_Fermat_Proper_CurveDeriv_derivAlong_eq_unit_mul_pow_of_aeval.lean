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
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one

/- Private proof closure from Definitions/Def_FermatCurveDerivationValuationElementary.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}



variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr


omit [CharZero K] in
private theorem valuation_lt_one_of_irreducible : O.valuation π < 1 := by
  have := (O.valuation_lt_one_iff ⟨π, hπO⟩).mp
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr ▸
      Ideal.mem_span_singleton_self _)
  simpa using this



end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

theorem derivAlong_eq_unit_mul_pow_of_aeval {t : K} (htO : t ∈ O) {m : ℚ[X]}
    (hm : m.Separable) {u : K} (hu : O.valuation u = 1) {e : ℕ} (he : 1 ≤ e)
    (hmt : aeval t m = u * π ^ e) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π t = w * π ^ (e - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hπ1 := valuation_lt_one_of_irreducible hπO hirr
  have hv : O.valuation (aeval t m) < 1 := by
    rw [hmt, map_mul, hu, one_mul, map_pow]
    exact pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero k)
  have hm' := valuation_aeval_derivative_eq_one hQ htO hm hv
  have hne : aeval t (derivative m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hm'
    exact zero_ne_one hm'
  obtain ⟨w₀, hw₀, hD⟩ := derivAlong_unit_mul_pow ht hQ hres hπO hirr hu k
  refine ⟨(aeval t (derivative m))⁻¹ * w₀, by rw [map_mul, map_inv₀, hm', hw₀]; simp, ?_⟩
  have := (derivAlong π).map_aeval m t
  rw [hmt, hD, smul_eq_mul] at this
  rw [Nat.add_sub_cancel, mul_assoc, this, inv_mul_cancel_left₀ hne]

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
