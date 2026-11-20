/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (sl2Image and curveInputs)
                Iut/Concrete/SL2Image.lean (prime_dvd_card_range and sl_le_range_of)
-/
import Solutions.Source_SL2ImageFromSource
import Solutions.Source_TripodCurveInputs
import Solutions.Source_TripodLogCond
import Solutions.Source_TripodTorsionBasis

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference AbcAdaptation.Reference.Iut

/-- The local Tate-ramification proof supplies the SL₂ image field of the provider. -/
theorem sl2Image_from_source (P : CurveProviders) : SL2ImageHyp P := by
  classical
  intro x ℓ hℓ h5 hP2 hP4 hP5 A
  have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
    intro w hw
    have := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at this
    rwa [dif_pos hw] at this
  have hP5' : ∃ w ∈ (P.curve x).badAll,
      AbcAdaptation.Reference.Iut.residueChar w ≠ 2 ∧
      AbcAdaptation.Reference.Iut.residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (P.arith x).badAll_finite.mem_toFinset.mp hw, h⟩
  exact (P.curve x).sl_le_range_of_from_source (P.arith x) (P.tate x) hℓ (P.modRep x ℓ hℓ)
    h5 hP2' hP4 hP5' A

/-- Assemble the curve inputs using the proved image, torsion-degree and conductor fields. -/
noncomputable def curveInputs_from_source (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0)) :
    CurveInputs tripodTheory AG K d :=
  curveInputsOfSL2Image P K d CF hcore hN torsionDegreeBound_three' torsionDegreeBound_five'
    hh hB (logCondGe P) (logCondLe P) (sl2Image_from_source P)

end AbcAdaptation.Tripod
