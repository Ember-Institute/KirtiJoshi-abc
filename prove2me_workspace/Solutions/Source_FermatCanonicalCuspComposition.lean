/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

DRAFT composer from Belyi/CurveField/{Canonical.lean:159,BelyiRelation.lean:85},
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The two source inputs are explicit hypotheses. No open theorem is imported.
-/
import Definitions.Def_FermatProperDivisorHeight
import Definitions.Def_FermatCurveFieldResidue
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Combine the source differential-change formula with the explicit Belyi
coefficient identity. The witness is (φ*(φ-1))*q with its original positive
principal-divisor sign. All supplied canonical data and proper places remain. -/
theorem canonicalCuspPolarLinearEquivalence_of_children
    (hChange : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (φ : M.K) (hφ : Transcendental ℚ φ)
      (K : CanonicalDivisorData M hDVR),
      ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
        K.D P =
          (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
            else -ramIdx M hDVR φ P - 1) + ord M hDVR P q)
    (hBelyiCoefficient : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
      (hfin : (cusps M hDVR φ).Finite),
      ∀ P : Place M.K,
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
          poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)))
    {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR) :
    ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
      K.D P + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P r := by
  letI : IsCurveField M.K := M.isCurveField
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ.1
  have hφ1 : φ - 1 ≠ 0 := by
    intro h
    apply hφ.1
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_one
  have hprod : φ * (φ - 1) ≠ 0 := mul_ne_zero hφ0 hφ1
  obtain ⟨q, hq, hchange⟩ := hChange M hDVR hRF φ hφ.1 K
  refine ⟨(φ * (φ - 1)) * q, mul_ne_zero hprod hq, ?_⟩
  intro P
  have hmul : ord M hDVR P ((φ * (φ - 1)) * q) =
      ord M hDVR P (φ * (φ - 1)) + ord M hDVR P q := by
    simpa only [ord_eq_placeOrd] using P.ord_mul hprod hq
  calc
    K.D P + cuspDivisor M hDVR φ hfin P =
        ((if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P) +
            ord M hDVR P q := by rw [hchange P]; ring
    _ = (poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1))) +
          ord M hDVR P q := by rw [hBelyiCoefficient M hDVR hRF φ hφ hfin P]
    _ = poleMultiplicity M hDVR φ P +
          ord M hDVR P ((φ * (φ - 1)) * q) := by rw [hmul]; ring

end AbcAdaptation.Tripod.Fermat.Proper
