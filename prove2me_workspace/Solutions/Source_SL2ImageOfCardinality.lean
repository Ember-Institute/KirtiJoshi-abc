/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Concrete/SL2Image.lean (sl_le_range_of, group-theoretic conclusion)
-/
import Solutions.Source_ModEllRepStableLine
import Solutions.Source_ReferenceIutSL2Generation
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

universe u

open scoped MatrixGroups

/-- Image inclusion after the arithmetic proof that the image order is divisible by `ℓ`. -/
theorem sl_le_range_of_dvd_card {C : EllipticCurveData.{u}} {ℓ : ℕ}
    (R : C.ModEllRepData ℓ) (hℓ : ℓ.Prime) (hdvd : ℓ ∣ Nat.card R.rep.range)
    (hP4 : ¬ C.HasCyclicSubgroup ℓ) (A : SL(2, ZMod ℓ)) : A.toGL ∈ R.rep.range := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨T, hT⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  rw [← Subgroup.orderOf_coe] at hT
  obtain ⟨hT1, hT2⟩ := SL2.transvection_of_orderOf (T : GL (Fin 2) (ZMod ℓ)) hT
  exact SL2.toGL_mem_of_transvection R.rep.range T.2 hT1 hT2
    (R.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup hP4) A

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
