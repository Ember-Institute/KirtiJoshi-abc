/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Concrete/SL2Image.lean (sl_le_range_of)
-/
import Solutions.Source_SL2ImageOfCardinality
import Theorems.Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_prime_dvd_card_range

set_option autoImplicit false

open AbcAdaptation.Reference.Iut

universe u

theorem solution (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (R : C.ModEllRepData ℓ)
    (h5 : 5 ≤ ℓ) (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP4 : ¬ C.HasCyclicSubgroup ℓ)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ)) : A.toGL ∈ R.rep.range :=
  R.sl_le_range_of_dvd_card hℓ (C.prime_dvd_card_range CA TI hℓ (by omega) R hP2 hP5) hP4 A
