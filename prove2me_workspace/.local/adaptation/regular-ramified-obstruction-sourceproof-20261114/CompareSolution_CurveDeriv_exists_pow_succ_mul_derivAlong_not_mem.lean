import Lean
import Definitions.Def_FermatCurveFieldUniformizer
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_irreducible_valuation_lt_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_succ_mul_derivAlong_not_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_eq_div
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem_integralClosure
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_irreducible_valuation_lt_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one

/- Private proof closure from Definitions/Def_FermatCurveDerivationValuationElementary.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}


omit [CharZero K] in
private theorem inv_mem_of_valuation_eq_one {u : K} (hu : O.valuation u = 1) : u⁻¹ ∈ O := by
  rw [← O.valuation_le_one_iff, map_inv₀, hu, inv_one]

variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr

omit [CharZero K] [IsDiscreteValuationRing O] in
private theorem ne_zero_of_irreducible : π ≠ 0 := fun h =>
  hirr.ne_zero (Subtype.ext h)


omit [CharZero K] in
private theorem mul_inv_mem_of_valuation_lt_one {y : K} (hy : y ∈ O) (hv : O.valuation y < 1) :
    y * π⁻¹ ∈ O := by
  have hm : (⟨y, hy⟩ : O) ∈ IsLocalRing.maximalIdeal O := (O.valuation_lt_one_iff _).mpr hv
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨g, hg⟩ := hm
  have hg' : (g : K) * π = y := congrArg Subtype.val hg
  rw [← hg', mul_assoc, mul_inv_cancel₀ (ne_zero_of_irreducible hπO hirr), mul_one]
  exact g.2


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
  (ht : Transcendental ℚ π) [Algebra.IsAlgebraic ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

theorem solution {k : ℕ} {x : K} (hx : x ∈ O)
    (hk : π ^ k * derivAlong π x ∉ O) : ∃ y ∈ O, π ^ (k + 1) * derivAlong π y ∉ O := by
  obtain ⟨p, hp0, hp⟩ := hres x hx
  obtain ⟨q, hq, hqv⟩ := exists_irreducible_valuation_lt_one hQ hx hp0 hp
  have hq' := valuation_aeval_derivative_eq_one hQ hx hq.separable hqv
  have hgO : aeval x q * π⁻¹ ∈ O :=
    mul_inv_mem_of_valuation_lt_one hπO hirr (aeval_mem hQ hx q) hqv
  refine ⟨aeval x q * π⁻¹, hgO, fun hmem => hk ?_⟩
  have hπ0 := ne_zero_of_irreducible hπO hirr
  set g := aeval x q * π⁻¹ with hg
  have hqx : aeval x q = π * g := by rw [hg]; field_simp
  have hD : aeval x (derivative q) * derivAlong π x = g + π * derivAlong π g := by
    have := (derivAlong π).map_aeval q x
    rw [smul_eq_mul] at this
    rw [← this, hqx, Derivation.leibniz, derivAlong_self ht, smul_eq_mul, smul_eq_mul]
    ring
  have hne : aeval x (derivative q) ≠ 0 := by
    intro h
    rw [h, map_zero] at hq'
    exact zero_ne_one hq'
  have : π ^ k * derivAlong π x =
      (aeval x (derivative q))⁻¹ * (π ^ k * g + π ^ (k + 1) * derivAlong π g) := by
    rw [eq_inv_mul_iff_mul_eq₀ hne]
    linear_combination (π ^ k) * hD
  rw [this]
  exact mul_mem (inv_mem_of_valuation_eq_one hq') (add_mem (mul_mem (pow_mem hπO k) hgO) hmem)

end

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_succ_mul_derivAlong_not_mem
  let c ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"
