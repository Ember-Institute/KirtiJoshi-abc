/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Uncompiled temporary source-proof draft. Namespace/imports adapted; selected
source proof bodies retained. No workspace edit, compiler, CI or API.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference

/-- The exact nonnegative source constant for the two-adic height field. -/
theorem curveInputs_B_nonneg (K : CompactlyBounded) : 0 ≤ max (4 * K.c) 0 :=
  le_max_right _ _

/-- The actual provider's two-adic field, with the same curve/arithmetic/Tate inputs. -/
theorem curveInputs_heightEq_two_le (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  twoAdicBound P K x hx.1

end AbcAdaptation.Tripod
