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
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.LinearCombination

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

theorem solution (hπ1 : O.valuation π < 1) {x : K} (hx : x ∈ O) :
    ∃ b s : 𝓑, O.valuation (s : K) = 1 ∧ x = b / s := by
  haveI := isPrincipalIdealRing_adjoin ht
  haveI : IsDedekindDomain 𝓑 :=
    IsIntegralClosure.isDedekindDomain (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  haveI : IsFractionRing 𝓑 K :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  let fB : 𝓑 →+* O := ((integralClosure (Algebra.adjoin ℚ {π}) K).val.toRingHom).codRestrict O
    (fun b => hBO b)
  let 𝔭 : Ideal 𝓑 := Ideal.comap fB (IsLocalRing.maximalIdeal O)
  have hmem : ∀ b : 𝓑, b ∈ 𝔭 ↔ O.valuation (b : K) < 1 := fun b =>
    O.valuation_lt_one_iff (fB b)
  have hle : ∀ b : 𝓑, O.valuation (b : K) ≤ 1 := fun b => (O.valuation_le_one_iff _).mpr (hBO b)
  -- `𝔭` is a nonzero prime: it contains `π`
  have hπB : IsIntegral (Algebra.adjoin ℚ {π}) π :=
    isIntegral_algebraMap (x := (⟨π, Algebra.self_mem_adjoin_singleton ℚ π⟩ :
      Algebra.adjoin ℚ {π}))
  have hπ0 : π ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have h𝔭 : 𝔭 ≠ ⊥ := by
    intro h
    have : (⟨π, hπB⟩ : 𝓑) ∈ 𝔭 := (hmem _).mpr hπ1
    rw [h, Ideal.mem_bot] at this
    exact hπ0 (congrArg Subtype.val this)
  let Loc := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain 𝓑 h𝔭 Loc
  have hinj : Function.Injective (algebraMap 𝓑 Loc) :=
    IsLocalization.injective Loc (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := 𝓑) x
  change (b : K) / (c : K) = x at hbc
  have hc0 : (c : K) ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hc (Subtype.ext h)
  have hunit : ∀ s : 𝓑, s ∉ 𝔭 → O.valuation (s : K) = 1 := fun s hs =>
    (hle s).antisymm (not_lt.mp fun h => hs ((hmem s).mpr h))
  have hne0 : ∀ s : 𝓑, s ∉ 𝔭 → (s : K) ≠ 0 := fun s hs h => by
    have := hunit s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hLoc : ValuationRing Loc := of_isDiscreteValuationRing Loc
  obtain ⟨z, hz⟩ := @ValuationRing.cond Loc _ hLoc.toPreValuationRing
    (algebraMap 𝓑 Loc b) (algebraMap 𝓑 Loc c)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
  simp only [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul,
    ← map_mul] at hz
  have hs := hne0 s s.2
  rcases hz with hz | hz
  · -- `b * r = c * s`
    have hz' : (b : K) * r = c * s := by exact_mod_cast congrArg Subtype.val (hinj hz)
    by_cases hr : r ∈ 𝔭
    · refine absurd ((hmem s).mpr ?_) s.2
      have : (s : K) = x * r := by
        rw [← hbc]; field_simp; linear_combination -hz'
      rw [this, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr hx))
        ((hmem r).mp hr)
    · refine ⟨s, r, hunit r hr, ?_⟩
      rw [← hbc, div_eq_div_iff hc0 (hne0 r hr)]
      linear_combination hz'
  · -- `c * r = b * s`
    have hz' : (c : K) * r = b * s := by exact_mod_cast congrArg Subtype.val (hinj hz)
    refine ⟨r, s, hunit s s.2, ?_⟩
    rw [← hbc, div_eq_div_iff hc0 hs]
    linear_combination -hz'

end
