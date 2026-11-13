/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Source proof: CurveField/Noncritical.lean:44-125 at pinned Belyi
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatNoncriticalFunctions
import Definitions.Def_FermatRiemannComposition

set_option autoImplicit false

open Polynomial
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- An actual rational function with simple zeros exactly at a finite set
T' containing the requested places. Every place outside T' has order ≤0. -/
structure SimpleZeroFunction (M : Model N) (hDVR : PlacesDiscrete M)
    (T : Finset (Place M.K)) where
  ψ : M.K
  transcendental : Transcendental ℚ ψ
  T' : Finset (Place M.K)
  contains : T ⊆ T'
  nonempty : T'.Nonempty
  simple : ∀ P ∈ T', ord M hDVR P ψ = 1
  no_other_zeros : ∀ P ∉ T', ord M hDVR P ψ ≤ 0

theorem model_infinite_places (M : Model N) : Infinite (Place M.K) := by
  letI : IsCurveField M.K := M.isCurveField
  let t := M.u
  have ht : Transcendental ℚ t := M.transcendental_u
  have hq : ∀ q : ℚ, Transcendental ℚ (t - algebraMap ℚ M.K q) := fun q => by
    have := ht.aeval (X - C q) (by rw [natDegree_X_sub_C]; exact one_ne_zero)
      (mem_nonZeroDivisors_of_ne_zero (leadingCoeff_ne_zero.mpr (X_sub_C_ne_zero q)))
    simpa using this
  choose P hP using fun q => Place.exists_ord_pos (hq q)
  refine Infinite.of_injective P fun q q' hqq' => ?_
  by_contra hne
  have h1 := hP q
  have h2 := hP q'
  rw [← hqq'] at h2
  have hsum : (t - algebraMap ℚ M.K q) + -(t - algebraMap ℚ M.K q') =
      algebraMap ℚ M.K (q' - q) := by rw [map_sub]; ring
  have hsum0 : (t - algebraMap ℚ M.K q) + -(t - algebraMap ℚ M.K q') ≠ 0 := by
    rw [hsum, Ne, map_eq_zero_iff _ (algebraMap ℚ M.K).injective, sub_eq_zero]
    exact Ne.symm hne
  have := (P q).min_le_ord_add hsum0
  rw [hsum, Place.ord_algebraMap_rat, Place.ord_neg] at this
  omega

/-- The existing genuine Riemann polar-realization input gives the source's
simple-zero function. No new Belyi existence assertion is used here. -/
theorem simpleZeroFunction_of_polarRealization
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hRealize : ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P)
    (T : Finset (Place M.K)) : Nonempty (SimpleZeroFunction M hDVR T) := by
  classical
  letI : IsCurveField M.K := M.isCurveField
  letI := model_infinite_places M
  obtain ⟨N1, hN1⟩ := hRealize
  obtain ⟨T', hTT', hcard⟩ :=
    Infinite.exists_superset_card_eq T (T.card + N1.toNat + 1) (by omega)
  let A : Divisor M := ∑ P ∈ T', Finsupp.single P 1
  have hA : ∀ P, A P = if P ∈ T' then 1 else 0 := by
    intro P
    dsimp only [A]
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hA0 : 0 ≤ A := fun P => by rw [hA]; split_ifs <;> simp
  have hdeg : N1 ≤ divisorDegree M A := by
    have h1 : divisorDegree M A = ∑ P ∈ T', (P.degree : ℤ) := by
      change divisorDegreeHom M A = _
      dsimp only [A]
      rw [map_sum]
      simp [divisorDegreeHom, divisorDegree_single]
    have h2 : ∑ P ∈ T', (1 : ℤ) ≤ ∑ P ∈ T', (P.degree : ℤ) :=
      Finset.sum_le_sum fun P _ => by exact_mod_cast P.degree_pos
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at h2
    push_cast at h2
    omega
  obtain ⟨f, hf⟩ := hN1 A hA0 hdeg
  let ψ := f⁻¹
  have hSimple : ∀ P ∈ T', ord M hDVR P ψ = 1 := by
    intro P hP
    have := hf P
    simp only [poleMultiplicity, hA P, if_pos hP] at this
    simp only [ψ, ord_eq_placeOrd, Place.ord_inv] at this ⊢
    omega
  have hNoZeros : ∀ P ∉ T', ord M hDVR P ψ ≤ 0 := by
    intro P hP
    have := hf P
    simp only [poleMultiplicity, hA P, if_neg hP] at this
    simp only [ψ, ord_eq_placeOrd, Place.ord_inv] at this ⊢
    omega
  have hne : T'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨P0, hP0⟩ := hne
  have hψ : Transcendental ℚ ψ := by
    intro ha
    have hz := P0.ord_eq_zero_of_isAlgebraic ha
    have ho := hSimple P0 hP0
    simp only [ord_eq_placeOrd] at ho
    omega
  exact ⟨⟨ψ, hψ, T', hTT', ⟨P0, hP0⟩, hSimple, hNoZeros⟩⟩

end AbcAdaptation.Tripod.Fermat.Proper
