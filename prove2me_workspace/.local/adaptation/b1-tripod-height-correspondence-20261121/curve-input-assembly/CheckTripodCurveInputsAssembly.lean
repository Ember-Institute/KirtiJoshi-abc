/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (sl2Image and curveInputs)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DifferentDegree
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp
import Solutions.Source_SL2ImageFromSource

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference AbcAdaptation.Reference.Iut

/-- The local Tate-ramification proof supplies the SL₂ image field of the provider. -/
private theorem sl2Image (P : CurveProviders) : SL2ImageHyp P := by
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

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- **The inputs of IUT IV, Corollary 2.2 for the tripod**, from the curves `E_λ/F_λ` of the
points, the facts proved in this file, the isolated hypotheses `CurveFactsProp`, the core
finiteness `CoreFinitenessHyp` (a theorem for the model geometry, `Iut.Tripod.coreFiniteness`),
the height comparison `LegendreHeightHyp` (proved in `Height.lean`), the `2`-adic and conductor
bounds (proved in `TwoAdic.lean`, `LogCond.lean`), and the Northcott property `NorthcottHyp`. -/
noncomputable def curveInputs {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3) (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (hge : LogCondGeHyp P) (hle : LogCondLeHyp P) :
    CurveInputs tripodTheory AG K d where
  h := P.h
  curve x _ := P.curve x
  arith x _ := P.arith x
  tate x _ := P.tate x
  modRep x _ ℓ hℓ := P.modRep x ℓ hℓ
  height_eq _ _ := rfl
  deg_le x hx := by
    refine (deg_le x _ _ (hdeg3 x) (hdeg5 x)).trans ?_
    exact Nat.mul_le_mul_left _ hx.2
  dmod_le x hx := (dmod_le x _ _).trans hx.2
  htCan_equiv := hh
  northcott := northcott_of_equiv hN K d hh
  B := max (4 * K.c) 0
  B_nonneg := le_max_right _ _
  heightEq_two_le x hx := hB x hx.1
  HasCyclicSubgroup x ℓ := (P.curve x).HasCyclicSubgroup ℓ
  TK := TK
  cyclic_bound := CF.cyclic
  sl2_of x _ ℓ hℓ := sl2Image P x ℓ hℓ
  logDiff_eq x _ := logDiff_eq x _ _
  excCore_finite := hcore
  logCond_ge x _ := hge x
  logCond_le x _ := hle x

end AbcAdaptation.Tripod

#print axioms AbcAdaptation.Tripod.curveInputs
