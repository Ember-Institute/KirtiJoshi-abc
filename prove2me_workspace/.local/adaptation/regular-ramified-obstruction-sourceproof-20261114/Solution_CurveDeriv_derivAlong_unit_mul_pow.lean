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
import Mathlib.Tactic.Positivity
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_mem

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


omit [CharZero K] in
private theorem valuation_lt_one_of_irreducible : O.valuation π < 1 := by
  have := (O.valuation_lt_one_iff ⟨π, hπO⟩).mp
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr ▸
      Ideal.mem_span_singleton_self _)
  simpa using this



end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Private proof closure from Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_curveDerivationUniqueness.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct



end Extension

variable {K : Type*} [Field K] [CharZero K] {t : K}

@[simp]
private theorem derivAlong_self (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t t = 1 := by
  simpa using derivAlong_aeval ht X





end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

theorem solution {u : K} (hu : O.valuation u = 1) (k : ℕ) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π (u * π ^ (k + 1)) = w * π ^ k := by
  have huO : u ∈ O := (O.valuation_le_one_iff u).mp hu.le
  have hDu := derivAlong_mem O ht hQ hres hπO hirr huO
  refine ⟨((k + 1 : ℕ) : K) * u + π * derivAlong π u, ?_, ?_⟩
  · have h1 : O.valuation (((k + 1 : ℕ) : K) * u) = 1 := by
      rw [map_mul, hu, mul_one, ← map_natCast (algebraMap ℚ K)]
      exact valuation_algebraMap_rat hQ (by positivity)
    have h2 : O.valuation (π * derivAlong π u) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr hDu))
        (valuation_lt_one_of_irreducible hπO hirr)
    rw [add_comm, Valuation.map_add_eq_of_lt_right _ (h1 ▸ h2), h1]
  · rw [Derivation.leibniz, Derivation.leibniz_pow, derivAlong_self ht]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_one]
    push_cast
    ring

end
