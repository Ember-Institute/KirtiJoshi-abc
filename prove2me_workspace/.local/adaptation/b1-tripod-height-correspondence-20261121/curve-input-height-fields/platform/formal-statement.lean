import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference

theorem AbcAdaptation.Tripod.curveInputs_height_fields (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    (∀ x : Pt, x ∈ K.set ∩ ptLE d →
      ((P.curve x).localHeightData (P.arith x) (P.tate x)).height = P.h x) ∧
    LegendreHeightHyp P K ∧
    (∀ H : ℝ, {x : Pt | x ∈ K.set ∩ ptLE d ∧ P.h x ≤ H}.Finite) := by sorry
