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
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_eq_div
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem_integralClosure

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


omit [CharZero K] in
private theorem valuation_lt_one_of_irreducible : O.valuation π < 1 := by
  have := (O.valuation_lt_one_iff ⟨π, hπO⟩).mp
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr ▸
      Ideal.mem_span_singleton_self _)
  simpa using this



end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Private proof closure from Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_curveDerivationIntegralClosureQuotient.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}

open scoped IntermediateField.algebraAdjoinAdjoin
set_option quotPrecheck false in
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K

private theorem mem_of_isIntegral (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O) {x : K}
    (hx : IsIntegral (Algebra.adjoin ℚ {π}) x) : x ∈ O := by
  let f : Algebra.adjoin ℚ {π} →+* O :=
    ((Algebra.adjoin ℚ {π}).val.toRingHom).codRestrict O
      (fun a => mem_of_mem_adjoin hQ hπO a.2)
  letI : Algebra (Algebra.adjoin ℚ {π}) O := f.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin ℚ {π}) O K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := O))
  rw [← hy]
  exact y.2


variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO


end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}

open scoped IntermediateField.algebraAdjoinAdjoin
set_option quotPrecheck false in
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K

variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO

variable [IsDiscreteValuationRing O] (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr

theorem solution :
    ∃ N : ℕ, ∀ x ∈ O, π ^ N * derivAlong π x ∈ O := by
  obtain ⟨N, hN⟩ := exists_pow_mul_derivAlong_mem_integralClosure ht hQ hπO hirr
  refine ⟨N, fun x hx => ?_⟩
  obtain ⟨b, s, hs, rfl⟩ :=
    exists_eq_div ht hQ hπO (valuation_lt_one_of_irreducible hπO hirr) hx
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have : π ^ N * ((s : K)⁻¹ ^ 2 * ((s : K) * derivAlong π b - b * derivAlong π s)) =
      (s : K)⁻¹ ^ 2 * ((s : K) * (π ^ N * derivAlong π b) - b * (π ^ N * derivAlong π s)) := by
    ring
  rw [this]
  exact mul_mem (pow_mem (inv_mem_of_valuation_eq_one hs) 2)
    (sub_mem (mul_mem (hBO s) (hN b)) (mul_mem (hBO b) (hN s)))

end
