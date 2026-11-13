/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of complete source proofs in
Belyi/CurveField/{NoncriticalBasic,NoncriticalElem}.lean.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
See source-consumer.json for source hashes, proof boundaries and consumers.
-/
import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatNoncriticalOrderSource

set_option autoImplicit false
open Polynomial
namespace AbcAdaptation.Tripod.Fermat.Proper

theorem noncriticalPolynomialOrderAtRegularPoint {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : ψ ∈ x.P.1) {g : ℚ[X]} (hg : g ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    x.P.ord (aeval ψ g) = ramIdx M hDVR ψ x.P *
      ((g.map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  induction hdeg_def : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  set r := x.P.residue ⟨ψ, h⟩ with hr_def
  have hr : IsIntegral ℚ r := x.P.noncritical_isIntegral_residue _
  have heval : ∀ p : ℚ[X], aeval (x.eval ψ h) p = x.σ (aeval r p) := fun p ↦
    aeval_algHom_apply x.σ.toRatAlgHom r p
  have hnz : ∀ p : ℚ[X], p ≠ 0 → aeval ψ p ≠ 0 := fun p hp h0 ↦ hψ ⟨p, hp, h0⟩
  by_cases hdvd : minpoly ℚ r ∣ g
  · obtain ⟨g', rfl⟩ := hdvd
    have hm0 := minpoly.ne_zero hr
    have hg' : g' ≠ 0 := by rintro rfl; simp at hg
    have hdeg : g'.natDegree < n := by
      rw [← hdeg_def, natDegree_mul hm0 hg']
      have := minpoly.natDegree_pos hr
      omega
    have hsep : ((minpoly ℚ r).map (algebraMap ℚ Tripod.Qbar)).Separable :=
      (minpoly.irreducible hr).separable.map
    have hroot : ((minpoly ℚ r).map (algebraMap ℚ Tripod.Qbar)).IsRoot (x.eval ψ h) := by
      rw [IsRoot, eval_map_algebraMap, heval, minpoly.aeval, map_zero]
    have hmap0 : (minpoly ℚ r).map (algebraMap ℚ Tripod.Qbar) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ Tripod.Qbar).injective).mpr hm0
    have h1 : ((minpoly ℚ r).map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) = 1 :=
      le_antisymm (rootMultiplicity_le_one_of_separable hsep _)
        ((rootMultiplicity_pos hmap0).mpr hroot)
    have hprod : ((minpoly ℚ r * g').map (algebraMap ℚ Tripod.Qbar)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ Tripod.Qbar).injective).mpr hg
    rw [map_mul, x.P.ord_mul (hnz _ hm0) (hnz _ hg'), ih _ hdeg hg' rfl, Polynomial.map_mul,
      rootMultiplicity_mul (by rwa [Polynomial.map_mul] at hprod), h1, NoncriticalElementarySource.ramIdx_of_mem M hDVR h]
    push_cast
    ring
  · have hne : aeval r g ≠ 0 := fun h0 ↦ hdvd (minpoly.dvd ℚ r h0)
    have hne' : ¬ (g.map (algebraMap ℚ Tripod.Qbar)).IsRoot (x.eval ψ h) := by
      rw [IsRoot, eval_map_algebraMap, heval]
      exact (map_ne_zero_iff _ x.σ.injective).mpr hne
    rw [rootMultiplicity_eq_zero hne', Nat.cast_zero, mul_zero]
    refine x.P.noncritical_ord_eq_zero_of_residue_ne_zero (x.P.noncritical_aeval_mem h g) ?_
    rwa [x.P.noncritical_residue_aeval h]

end AbcAdaptation.Tripod.Fermat.Proper
