/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Composition of the existing divisor-degree and fiber-degree source proofs
from Belyi/CurveField/{Degree,Divisor}.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The concrete Fermat coordinate-pole identity is an explicit premise below.
It is not a theorem imported from the pinned source.
-/
import Definitions.Def_FermatFunctionFiberDegrees

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- Conditional coefficient calculation for the existing hyperplane divisor.
The premise is equality of actual fixed coordinate multiplicities at all places. -/
theorem infinityDivisor_eq_polar_u_of_coordinatePoles
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hPoles : ∀ P : Place M.K,
      poleMultiplicity M hDVR M.u P = poleMultiplicity M hDVR M.v P)
    (H : InfinityDivisorData M hDVR) :
    H.H = functionPoleDivisor M hDVR M.u := by
  ext P
  rw [H.coefficient, ← hPoles P, max_self]
  rfl

/-- Conditional actual fiber-degree calculation. No free degree is supplied. -/
theorem infinityDivisor_degree_of_coordinatePoles
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hPoles : ∀ P : Place M.K,
      poleMultiplicity M hDVR M.u P = poleMultiplicity M hDVR M.v P)
    (H : InfinityDivisorData M hDVR) :
    divisorDegree M H.H = (N : ℤ) := by
  rw [infinityDivisor_eq_polar_u_of_coordinatePoles M hDVR hPoles H,
    functionPoleDivisor_degree M hDVR M.transcendental_u, M.degree_u]

/-- Sum the supplied actual adjunction relation after the concrete pole identity.
This calculation supplies neither coordinate-pole equality nor adjunction. -/
theorem canonicalDegree_of_coordinatePoles_and_actualAdjunction
    (M : Model N) (hDVR : PlacesDiscrete M) (hN : 3 < N)
    (hPoles : ∀ P : Place M.K,
      poleMultiplicity M hDVR M.u P = poleMultiplicity M hDVR M.v P)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR)
    (J : PlaneAdjunctionData M hDVR K H) :
    divisorDegree M K.D = planeCanonicalDegree N := by
  have hCast : ((N - 3 : ℕ) : ℤ) = (N : ℤ) - 3 := by omega
  have hDiv : K.D = (N - 3) • H.H + functionDivisor M hDVR J.r := by
    ext P
    simpa only [Finsupp.add_apply, Finsupp.smul_apply, functionDivisor_apply,
      nsmul_eq_mul, hCast] using J.coefficient P
  have hPrincipal : divisorDegree M (functionDivisor M hDVR J.r) = 0 :=
    principalDegreeZero_of_zeroPoleDegrees M hDVR
      (fun f hf => ⟨functionZeroDivisor_degree M hDVR hf,
        functionPoleDivisor_degree M hDVR hf⟩) J.r
  rw [hDiv, divisorDegree_add, divisorDegree_nsmul, hPrincipal, add_zero,
    infinityDivisor_degree_of_coordinatePoles M hDVR hPoles H]
  simp only [hCast, planeCanonicalDegree]
  ring

end AbcAdaptation.Tripod.Fermat.Proper
