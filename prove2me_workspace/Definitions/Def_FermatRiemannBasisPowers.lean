/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of Belyi/CurveField/Riemann.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannLocalDimension
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.AlgebraTower

set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.RiemannBasisPower

/-- Source Riemann.lean:164-213: actual basis powers give the dimension bound.
The existing hFinite supplies finiteness only for the actual target space. -/
theorem lowerBound {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hFinite : ∀ A : Divisor M, FiniteDimensional ℚ (riemannRochSpace M hDVR A))
    (l : ℕ) :
    (l + 1) * N ≤ riemannEll M hDVR
      (l • functionPoleDivisor M hDVR M.u + basisPoleCorrection M hDVR) := by
  letI : IsCurveField M.K := M.isCurveField
  letI : FiniteDimensional ℚ⟮M.u⟯ M.K := M.finite_u
  set n := Module.finrank ℚ⟮M.u⟯ M.K
  let u := functionBasis M
  set B := functionPoleDivisor M hDVR M.u
  set C : Divisor M := ∑ i, functionPoleDivisor M hDVR (u i : M.K)
  letI : FiniteDimensional ℚ (riemannRochSpace M hDVR (l • B + C)) := hFinite _
  have hx0 : M.u ≠ 0 := ne_zero_of_transcendental M.transcendental_u
  -- The actual elements M.u^k * u_i lie in the actual target space.
  have hmem : ∀ p : Fin (l + 1) × Fin n,
      M.u ^ (p.1 : ℕ) * u p.2 ∈ riemannRochSpace M hDVR (l • B + C) := by
    rintro ⟨k, i⟩
    rw [RiemannDimension.mem_L M hDVR]
    refine Or.inr fun Q => ?_
    rw [Q.ord_mul (pow_ne_zero _ hx0) (u.ne_zero i), Place.ord_pow]
    have hk : ((k : ℕ) : ℤ) ≤ l := by exact_mod_cast Nat.lt_succ_iff.mp k.2
    have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
    have h1 := le_max_right 0 (-Q.ord M.u)
    have h1' := le_max_left 0 (-Q.ord M.u)
    have h2 := le_max_right 0 (-Q.ord (u i))
    have h3 : max 0 (-Q.ord (u i)) ≤ C Q := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.single_le_sum
        (f := fun j => functionPoleDivisor M hDVR (u j : M.K) Q)
        (fun j _ => functionPoleDivisor_nonneg M hDVR _ Q) (Finset.mem_univ i)
    simp only [B, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply,
      functionPoleDivisor_apply, ord_eq_placeOrd, nsmul_eq_mul]
    nlinarith
  -- Polynomial evaluation preserves the independence of all monomials.
  have hpow : LinearIndependent ℚ (fun k : ℕ => M.u ^ k) := by
    have := (Polynomial.basisMonomials ℚ).linearIndependent.map' (aeval M.u).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp M.transcendental_u))
    simpa [Function.comp_def, Polynomial.coe_basisMonomials] using this
  let b : Fin (l + 1) → ℚ⟮M.u⟯ := fun k =>
    (IntermediateField.AdjoinSimple.gen ℚ M.u) ^ (k : ℕ)
  have hb : LinearIndependent ℚ b := by
    refine LinearIndependent.of_comp (IsScalarTower.toAlgHom ℚ ℚ⟮M.u⟯ M.K).toLinearMap ?_
    convert hpow.comp (Fin.val) Fin.val_injective using 1
    ext k
    simp [b]
    all_goals exact Subsingleton.elim _ _
  have hli := linearIndependent_smul hb u.linearIndependent
  have hv : ∀ p : Fin (l + 1) × Fin n,
      b p.1 • (u p.2 : M.K) = M.u ^ (p.1 : ℕ) * u p.2 := by
    intro p
    simp [b, Algebra.smul_def]
  let w : Fin (l + 1) × Fin n → riemannRochSpace M hDVR (l • B + C) :=
    fun p => ⟨M.u ^ (p.1 : ℕ) * u p.2, hmem p⟩
  have hw : LinearIndependent ℚ w := by
    refine LinearIndependent.of_comp (riemannRochSpace M hDVR (l • B + C)).subtype ?_
    convert hli using 1
    ext p
    exact congrArg Subtype.val (hv p).symm
  have hcard := hw.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hactual : (l + 1) * Module.finrank ℚ⟮M.u⟯ M.K ≤
      riemannEll M hDVR
        (l • functionPoleDivisor M hDVR M.u + basisPoleCorrection M hDVR) := hcard
  simpa only [M.degree_u] using hactual

end AbcAdaptation.Tripod.Fermat.Proper.RiemannBasisPower
