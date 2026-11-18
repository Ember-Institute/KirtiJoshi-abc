/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (prime_dvd_card_range)
-/
import Solutions.Source_SL2ImageRangeCardinality
import Theorems.Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_prime_dvd_ramificationIdx

set_option autoImplicit false

open AbcAdaptation.Reference.Iut

universe u

theorem solution (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    ℓ ∣ Nat.card R.rep.range :=
  C.prime_dvd_card_range_of_ramification R TI
    (fun {w} hw h2 hwℓ hcop {w'} hw'w =>
      C.prime_dvd_ramificationIdx CA TI hℓ hodd R (w := w) hw h2 hwℓ hcop (w' := w') hw'w)
    hP2 hP5
