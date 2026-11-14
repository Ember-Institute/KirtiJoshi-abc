/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source proof from Belyi/CurveField/Canonical.lean:144-166,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The supplied actual canonical divisor and every proper place remain quantified.
See this unit's validation receipts and source mappings.
-/
import Definitions.Def_FermatProperDivisorHeight
import Solutions.Source_FermatDifferentialOrder

set_option autoImplicit false
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The source chain rule, with q = du/dφ and positive principal order. -/
theorem canonicalDifferentialChange_source {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (K : CanonicalDivisorData M hDVR) :
    ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
      K.D P =
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + ord M hDVR P q := by
  letI : IsCurveField M.K := M.isCurveField
  haveI : Algebra.IsAlgebraic ℚ⟮M.u⟯ M.K := isAlgebraic_adjoin M.transcendental_u
  haveI : Algebra.IsAlgebraic ℚ⟮φ⟯ M.K := isAlgebraic_adjoin hφ
  let q : M.K := CurveDeriv.derivAlong φ M.u
  have hq : q ≠ 0 := by
    intro h0
    have h1 := CurveDeriv.derivAlong_mul_derivAlong M.transcendental_u hφ
    rw [show CurveDeriv.derivAlong φ M.u = 0 from h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨q, hq, ?_⟩
  intro P
  rw [K.coefficient P]
  have hu := DifferentialOrderSource.ord_derivAlong M hDVR M.u M.transcendental_u P
  have hφorder := DifferentialOrderSource.ord_derivAlong M hDVR φ hφ P
  have hchain := congrArg (· M.u) (CurveDeriv.derivAlong_eq_smul P.uniformizer hφ)
  simp only [Derivation.smul_apply, smul_eq_mul] at hchain
  calc
    (if M.u ∈ P.1 then ramIdx M hDVR M.u P - 1 else -ramIdx M hDVR M.u P - 1) =
        P.ord (CurveDeriv.derivAlong P.uniformizer M.u) := hu.symm
    _ = P.ord (CurveDeriv.derivAlong P.uniformizer φ) + P.ord q := by
      rw [hchain, P.ord_mul
        (DifferentialOrderSource.derivAlong_uniformizer_ne_zero M φ hφ P) hq]
    _ = (if φ ∈ P.1 then ramIdx M hDVR φ P - 1 else -ramIdx M hDVR φ P - 1) +
          ord M hDVR P q := by rw [hφorder, ord_eq_placeOrd]

end AbcAdaptation.Tripod.Fermat.Proper
