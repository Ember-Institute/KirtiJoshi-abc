/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Riemann.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannLocalDimension
import Mathlib.FieldTheory.Minpoly.Field

set_option autoImplicit false

open Polynomial IsLocalRing

namespace AbcAdaptation.Tripod.Fermat.Proper.RiemannApproximation

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
variable [hCurve : IsCurveField M.K]
include M hDVR hCurve

local notation "L" => riemannRochSpace M hDVR
local notation "pdiv" => functionDivisor M hDVR
local notation "pole" => functionPoleDivisor M hDVR

/-- The existing principal divisor respects division of nonzero functions. -/
theorem principalDivisor_div {f g : M.K} (hf : f ≠ 0) (hg : g ≠ 0) :
    pdiv (f / g) = pdiv f - pdiv g := by
  ext P
  simp only [functionDivisor_apply, Finsupp.coe_sub, Pi.sub_apply, ord_eq_placeOrd]
  exact P.ord_div hf hg

/-- Source Riemann.lean:54-59. -/
theorem pow_mem_L (x : M.K) (k : ℕ) : x ^ k ∈ L (k • pole x) := by
  rw [RiemannDimension.mem_L M hDVR]
  refine Or.inr fun P => ?_
  simp only [Finsupp.coe_smul, Pi.smul_apply, functionPoleDivisor_apply,
    ord_eq_placeOrd, nsmul_eq_mul, Place.ord_pow]
  have h1 := le_max_right 0 (-P.ord x)
  have h2 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  nlinarith

/-- Source Riemann.lean:62-67, using the actual polynomial evaluation. -/
theorem aeval_mem_L (x : M.K) (p : ℚ[X]) :
    aeval x p ∈ L (p.natDegree • pole x) := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (riemannRochSpace_mono M hDVR ?_ (pow_mem_L M hDVR x i))
  exact nsmul_le_nsmul_left (functionPoleDivisor_nonneg M hDVR x)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- Source Riemann.lean:70-90. The polynomial is the actual residue minpoly. -/
theorem exists_aeval_ord_pos {x : M.K} (hx : Transcendental ℚ x)
    (P : Place M.K) (hxP : x ∈ P.1) :
    ∃ p : ℚ[X], aeval x p ≠ 0 ∧ 0 < P.ord (aeval x p) := by
  set r := P.residue ⟨x, hxP⟩
  have hint : IsIntegral ℚ r := Algebra.IsIntegral.isIntegral r
  set p := minpoly ℚ r
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hy0 : aeval x p ≠ 0 := fun h => hx ⟨p, hp0, h⟩
  refine ⟨p, hy0, ?_⟩
  set e : P.1 := p.eval₂ P.ratHom ⟨x, hxP⟩
  have hcomp : P.1.subtype.comp P.ratHom = algebraMap ℚ M.K := by
    ext q; simp [ValuationSubring.subtype]
  have he : (e : M.K) = aeval x p := by
    rw [aeval_def, ← hcomp]
    exact Polynomial.hom_eval₂ p P.ratHom P.1.subtype ⟨x, hxP⟩
  have hcomp' : P.residue.comp P.ratHom = algebraMap ℚ P.ResidueField := by
    ext q; simp
  have hres : P.residue e = 0 := by
    rw [Polynomial.hom_eval₂, hcomp', ← aeval_def]
    exact minpoly.aeval ℚ r
  rw [← he]
  refine (P.ord_pos_iff_mem_maximalIdeal (a := e) (by rw [he]; exact hy0)).mpr ?_
  exact P.residue_eq_zero_iff.mp hres

section Reduction

variable {x : M.K} (hx : Transcendental ℚ x)
include hx

omit hx in
/-- Source Riemann.lean:101-107. Every actual pole contains one copy of P. -/
theorem single_le_polarDivisor {P : Place M.K} (hP : P.ord x < 0) :
    Finsupp.single P 1 ≤ pole x := by
  classical
  intro Q
  by_cases hQ : P = Q
  · subst hQ
    simp only [Finsupp.single_eq_same, functionPoleDivisor_apply, ord_eq_placeOrd]
    omega
  · rw [Finsupp.single_apply, if_neg hQ]
    exact functionPoleDivisor_nonneg M hDVR x Q

/-- Source Riemann.lean:109-131. -/
theorem exists_add_single_add_div_le {A : Divisor M} (P : Place M.K)
    (h : ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ, A + pdiv z ≤ l • pole x) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + Finsupp.single P 1 + pdiv z ≤ l • pole x := by
  classical
  obtain ⟨z, hz, l, hl⟩ := h
  by_cases hP : P.ord x < 0
  · refine ⟨z, hz, l + 1, ?_⟩
    rw [succ_nsmul, show A + Finsupp.single P 1 + pdiv z =
      (A + pdiv z) + Finsupp.single P 1 by abel]
    exact add_le_add hl (single_le_polarDivisor M hDVR hP)
  obtain ⟨p, hy0, hypos⟩ := exists_aeval_ord_pos M hDVR hx P
    (P.mem_of_ord_nonneg (not_lt.mp hP))
  have hyL := ((RiemannDimension.mem_L M hDVR).mp
    (aeval_mem_L M hDVR x p)).resolve_left hy0
  refine ⟨z / aeval x p, div_ne_zero hz hy0, l + p.natDegree, ?_⟩
  rw [principalDivisor_div M hDVR hz hy0, add_nsmul,
    show A + Finsupp.single P 1 + (pdiv z - pdiv (aeval x p)) =
      (A + pdiv z) + (Finsupp.single P 1 - pdiv (aeval x p)) by abel]
  refine add_le_add hl fun Q => ?_
  have h1 := hyL Q
  have h2 := (nsmul_nonneg (functionPoleDivisor_nonneg M hDVR x) p.natDegree) Q
  simp only [Finsupp.coe_sub, Pi.sub_apply, functionDivisor_apply, ord_eq_placeOrd,
    Finsupp.coe_zero, Pi.zero_apply] at h1 h2 ⊢
  by_cases hQ : P = Q
  · subst hQ; rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_apply, if_neg hQ]; omega

/-- Source Riemann.lean:133-141. -/
theorem exists_add_single_nat_add_div_le {A : Divisor M} (P : Place M.K) (m : ℕ)
    (h : ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ, A + pdiv z ≤ l • pole x) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + Finsupp.single P (m : ℤ) + pdiv z ≤ l • pole x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have := exists_add_single_add_div_le M hDVR hx P ih
    rwa [Nat.cast_succ, Finsupp.single_add, ← add_assoc]

/-- Source Riemann.lean:144-158. No place, including infinity, is omitted. -/
theorem exists_add_div_le (A : Divisor M) :
    ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ, A + pdiv z ≤ l • pole x := by
  classical
  induction A using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | single_add P b f _ _ ih =>
    rcases le_or_gt b 0 with hb | hb
    · obtain ⟨z, hz, l, hl⟩ := ih
      refine ⟨z, hz, l, le_trans ?_ hl⟩
      rw [add_assoc]
      refine add_le_of_nonpos_left fun Q => ?_
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
      rw [add_comm]
      exact exists_add_single_nat_add_div_le M hDVR hx P m ih

end Reduction

end AbcAdaptation.Tripod.Fermat.Proper.RiemannApproximation
