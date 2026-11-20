/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (prime_dvd_card_range and sl_le_range_of)
-/
import Solutions.Source_SL2ImageLocalTate
import Solutions.Source_SL2ImageOfCardinality
import Solutions.Source_SL2ImageRangeCardinality

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

universe u

/-- Under (P2) and (P5), the prime divides the order of the representation image. -/
theorem prime_dvd_card_range_from_source (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    ℓ ∣ Nat.card R.rep.range :=
  C.prime_dvd_card_range_of_ramification R TI
    (fun {w} hw h2 hwℓ hcop {w'} hw'w =>
      C.prime_dvd_ramificationIdx_from_source CA TI hℓ hodd R
        (w := w) hw h2 hwℓ hcop (w' := w') hw'w)
    hP2 hP5

/-- Under (P2), (P4), and (P5), the mod-ℓ representation image contains SL₂. -/
theorem sl_le_range_of_from_source (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (R : C.ModEllRepData ℓ)
    (h5 : 5 ≤ ℓ) (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP4 : ¬ C.HasCyclicSubgroup ℓ)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ)) : A.toGL ∈ R.rep.range := by
  have hodd : ℓ ≠ 2 := ne_of_gt (lt_of_lt_of_le (by decide : (2 : ℕ) < 5) h5)
  exact R.sl_le_range_of_dvd_card hℓ
    (C.prime_dvd_card_range_from_source CA TI hℓ hodd R hP2 hP5) hP4 A

end AbcAdaptation.Reference.Iut.EllipticCurveData
