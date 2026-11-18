/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Source consumers: Tripod/CurveFacts.lean:499,507-510; Concrete/Existence.lean:408,414,416,
478-480. Exact types of the currently implementable actual-provider height fields.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- Exact comparison-field type when the actual source constructor chooses h=P.h. -/
theorem curveInputs_htCan_equiv :
    ((1 / 6 : ℝ) • P.h) ≈[tripodTheory.cbsSet K] tripodTheory.htCan tripodTheory.tripod :=
  legendreHeight P K

/-- Exact height-computation field for the same curve, arithmetic and Tate inputs. -/
theorem curveInputs_height_eq
    (x : tripodTheory.Pt tripodTheory.tripod)
    (_hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).height = P.h x := rfl

/-- Exact bounded-provider-height Northcott field, uniform over all point fields. -/
theorem curveInputs_northcott (H : ℝ) :
    {x : tripodTheory.Pt tripodTheory.tripod |
      x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d ∧ P.h x ≤ H}.Finite :=
  northcott_of_equiv northcottHyp K d (legendreHeight P K) H

end AbcAdaptation.Tripod
