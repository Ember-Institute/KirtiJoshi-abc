/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (sl_le_range_of)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

universe u

theorem sl_le_range_of (C : EllipticCurveData.{u}) (_CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (_hℓ : ℓ.Prime) (R : C.ModEllRepData ℓ)
    (_h5 : 5 ≤ ℓ) (_hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (_hP4 : ¬ C.HasCyclicSubgroup ℓ)
    (_hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ)) : A.toGL ∈ R.rep.range := by
  sorry

end AbcAdaptation.Reference.Iut.EllipticCurveData
