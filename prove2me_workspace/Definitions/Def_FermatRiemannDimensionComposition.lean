/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Source proof adaptation: Belyi/CurveField/Riemann.lean:158-282 at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannLocalDimension
import Mathlib.Data.Int.ConditionallyCompleteOrder

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The supremum of the actual integer defects. It receives no free genus
or dimension parameter. Boundedness and attainment are proved below. -/
noncomputable def riemannDefectSup (M : Model N) (hDVR : PlacesDiscrete M) : ℤ :=
  sSup (Set.range fun A : Divisor M =>
    divisorDegree M A - (riemannEll M hDVR A : ℤ))

/-- The three geometric inputs control actual divisors, actual function
values, and dimensions of actual Riemann–Roch spaces. Their source proof
implies eventual linearity without a separate genus axiom. -/
theorem riemannEventuallyLinear_of_degree_approximation_basis
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hDegreeZero : ∀ f : M.K, divisorDegree M (functionDivisor M hDVR f) = 0)
    (hPoleDegree : divisorDegree M (functionPoleDivisor M hDVR M.u) = (N : ℤ))
    (hApprox : ∀ A : Divisor M, ∃ z : M.K, z ≠ 0 ∧ ∃ l : ℕ,
      A + functionDivisor M hDVR z ≤ l • functionPoleDivisor M hDVR M.u)
    (hBasis : ∀ l : ℕ, (l + 1) * N ≤
      riemannEll M hDVR (l • functionPoleDivisor M hDVR M.u +
        basisPoleCorrection M hDVR)) :
    ∃ g0 N0 : ℤ, ∀ A : Divisor M, N0 ≤ divisorDegree M A →
      (riemannEll M hDVR A : ℤ) = divisorDegree M A - g0 := by
  letI : IsCurveField M.K := M.isCurveField
  let B := functionPoleDivisor M hDVR M.u
  let C := basisPoleCorrection M hDVR
  have hC : 0 ≤ C := basisPoleCorrection_nonneg M hDVR
  have hPolarBound : ∃ γ : ℤ, ∀ l : ℕ,
      divisorDegree M (l • B) - (riemannEll M hDVR (l • B) : ℤ) ≤ γ := by
    refine ⟨divisorDegree M C - N, fun l => ?_⟩
    have hcard := hBasis l
    have hdegD : divisorDegree M (l • B + C) = (l : ℤ) * N + divisorDegree M C := by
      rw [divisorDegree_add, divisorDegree_nsmul]
      dsimp only [B]
      rw [hPoleDegree]
    have hmono := RiemannDimension.degreeDefect_mono M hDVR hDegreeZero
      (le_add_of_nonneg_right hC : l • B ≤ l • B + C)
    have hcard' : ((l : ℤ) + 1) * N ≤ riemannEll M hDVR (l • B + C) := by
      exact_mod_cast hcard
    have hexpand : ((l : ℤ) + 1) * N = (l : ℤ) * N + N := by ring
    omega
  obtain ⟨γ, hγ⟩ := hPolarBound
  have hAllBound : ∀ A : Divisor M,
      divisorDegree M A - (riemannEll M hDVR A : ℤ) ≤ γ := by
    intro A
    obtain ⟨z, hz, l, hl⟩ := hApprox A
    have h := RiemannDimension.degreeDefect_mono M hDVR hDegreeZero hl
    rw [divisorDegree_add, hDegreeZero, add_zero,
      RiemannDimension.ell_add_pdiv M hDVR A hz] at h
    exact h.trans (hγ l)
  have hBdd : BddAbove (Set.range fun A : Divisor M =>
      divisorDegree M A - (riemannEll M hDVR A : ℤ)) := by
    exact ⟨γ, by rintro _ ⟨A, rfl⟩; exact hAllBound A⟩
  have hDefectLe : ∀ A : Divisor M,
      divisorDegree M A - (riemannEll M hDVR A : ℤ) ≤ riemannDefectSup M hDVR := by
    intro A
    exact le_csSup hBdd ⟨A, rfl⟩
  obtain ⟨A0, hA0⟩ := Int.csSup_mem (Set.range_nonempty _) hBdd
  change divisorDegree M A0 - (riemannEll M hDVR A0 : ℤ) =
    riemannDefectSup M hDVR at hA0
  refine ⟨riemannDefectSup M hDVR,
    divisorDegree M A0 + riemannDefectSup M hDVR + 1, fun A hA => ?_⟩
  have h1 := hDefectLe (A - A0)
  rw [divisorDegree_sub] at h1
  obtain ⟨z, hz, hle⟩ := RiemannDimension.exists_nonneg_add_pdiv M hDVR hDegreeZero
    (A := A - A0) (by omega)
  have hle' : A0 ≤ A + functionDivisor M hDVR z := by
    intro Q
    have := hle Q
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
      Finsupp.coe_zero, Pi.zero_apply] at this ⊢
    omega
  have h2 := RiemannDimension.degreeDefect_mono M hDVR hDegreeZero hle'
  rw [divisorDegree_add, hDegreeZero, add_zero,
    RiemannDimension.ell_add_pdiv M hDVR A hz] at h2
  have h3 := hDefectLe A
  omega

end AbcAdaptation.Tripod.Fermat.Proper
