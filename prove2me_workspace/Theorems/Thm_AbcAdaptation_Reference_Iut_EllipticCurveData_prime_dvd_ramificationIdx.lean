/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (prime_dvd_ramificationIdx)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField

universe u

/-- The prime divides the relative ramification index at a place of the torsion field
above a multiplicative place with the given residue characteristic and Tate order. -/
theorem prime_dvd_ramificationIdx (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  sorry

end AbcAdaptation.Reference.Iut.EllipticCurveData
