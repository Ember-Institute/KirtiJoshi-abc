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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Tactic.FieldSimp

/- Private proof closure from Definitions/Def_FermatCurveDerivationValuationElementary.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}



variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr

omit [CharZero K] [IsDiscreteValuationRing O] in
private theorem ne_zero_of_irreducible : π ≠ 0 := fun h =>
  hirr.ne_zero (Subtype.ext h)



omit [CharZero K] in
private theorem exists_pow_mul_mem (y : K) : ∃ n : ℕ, π ^ n * y ∈ O := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  by_cases hyO : y ∈ O
  · exact ⟨0, by simpa using hyO⟩
  have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hyO
  have hne : (⟨y⁻¹, hyi⟩ : O) ≠ 0 := fun h => hy (inv_eq_zero.mp (congrArg Subtype.val h))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
  refine ⟨n, ?_⟩
  have hu' : y⁻¹ = (u : O) * π ^ n := congrArg Subtype.val hu
  have hinv : (((u⁻¹ : Oˣ) : O) : K) * ((u : O) : K) = 1 := by
    exact_mod_cast congrArg Subtype.val u.inv_mul
  have hπ0 := ne_zero_of_irreducible hπO hirr
  have hy' : y = ((u : O) : K)⁻¹ * (π ^ n)⁻¹ := by rw [← mul_inv, ← hu', inv_inv]
  have : π ^ n * y = ((u⁻¹ : Oˣ) : O) := by
    rw [hy', eq_inv_of_mul_eq_one_left hinv]
    field_simp
  rw [this]
  exact SetLike.coe_mem _


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

private theorem isPrincipalIdealRing_adjoin (ht : Transcendental ℚ π) :
    IsPrincipalIdealRing (Algebra.adjoin ℚ {π}) :=
  IsPrincipalIdealRing.of_surjective
    ((Polynomial.algEquivOfTranscendental ℚ π ht : ℚ[X] ≃ₐ[ℚ] _) : ℚ[X] →+* _)
    (Polynomial.algEquivOfTranscendental ℚ π ht).surjective

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
    ∃ N : ℕ, ∀ b : 𝓑, π ^ N * derivAlong π b ∈ O := by
  haveI := isPrincipalIdealRing_adjoin ht
  letI : Algebra (Algebra.adjoin ℚ {π}) 𝓑 :=
    (integralClosure (Algebra.adjoin ℚ {π}) K).algebra'
  letI : Module (Algebra.adjoin ℚ {π}) 𝓑 := Algebra.toModule
  haveI : Module.Finite (Algebra.adjoin ℚ {π}) 𝓑 :=
    IsIntegralClosure.finite (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Algebra.adjoin ℚ {π}) (M := 𝓑)
  choose n hn using fun i : 𝓑 => exists_pow_mul_mem hπO hirr (derivAlong π (i : K))
  refine ⟨S.sup n, fun b => ?_⟩
  have hb : b ∈ Submodule.span (Algebra.adjoin ℚ {π}) (S : Set 𝓑) := hS ▸ Submodule.mem_top
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  induction hb using Submodule.span_induction with
  | mem i hi =>
    have : π ^ S.sup n = π ^ (S.sup n - n i) * π ^ n i := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := n) hi)]
    rw [this, mul_assoc]
    exact mul_mem (pow_mem hπO _) (hn i)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add, mul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    have hax : ((a • x : 𝓑) : K) = (a : K) * x := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]; rfl
    rw [hax, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
    refine add_mem ?_ ?_
    · rw [mul_left_comm]
      exact mul_mem (mem_of_mem_adjoin hQ hπO a.2) hx
    · rw [← mul_assoc]
      exact mul_mem (mul_mem (pow_mem hπO _) (hBO x))
        (derivAlong_mem_of_mem_adjoin ht hQ hπO a.2)

end

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_mul_derivAlong_mem_integralClosure
  let c ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"
