/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent statement adaptation of Iut/Tripod/Northcott.lean and
Iut/Implication/Corollary23.lean, using the existing concrete definitions.
-/
import Definitions.Def_AbcTripod

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- Northcott finiteness over all algebraic points of bounded degree, not just
points in one fixed number field. The height is exactly the imported
`htCan x = Height.logHeight₁ (gen x.1) / deg x.1`. -/
def BoundedDegreeFiniteness : Prop :=
  ∀ (d : ℕ) (H : ℝ),
    {x : Pt | deg x.1 ≤ d ∧ htCan x ≤ H}.Finite

/-- The asymptotic estimate, with uniform threshold and additive constant for
each positive degree bound, positive error, and existing compactly bounded set.

This packages the high-height part of `statementII_of_cor312` after transferring
its auxiliary height to the existing `htCan`. Its finite exceptional core can
be put below the threshold since its image under `htCan` is bounded above.
That transfer and the arithmetic estimate belong to this open child.
The additive constant retains the source's bounded-discrepancy convention.
No auxiliary height or arbitrary proposition is an input to this predicate. -/
def HighHeightEstimate : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (ε : ℝ), 0 < ε →
    ∀ K : CompactlyBounded, ∃ H C : ℝ,
      ∀ x : Pt, x ∈ K.set → deg x.1 ≤ d → H < htCan x →
        htCan x ≤ (1 + ε) * (logDiff x + logCond x) + C

end AbcAdaptation.Tripod
