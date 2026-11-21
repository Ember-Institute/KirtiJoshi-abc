import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut

theorem AbcAdaptation.Tripod.curveInputs_twoAdic_fields (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    0 ≤ max (4 * K.c) 0 ∧
      ∀ (x : tripodTheory.Pt tripodTheory.tripod),
        x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d →
        ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 := by sorry
