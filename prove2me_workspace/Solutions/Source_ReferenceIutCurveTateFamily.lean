/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Solutions.Source_ModEllRepGalois
import Solutions.Source_ReferenceIutSplitSquare
import Solutions.Source_ReferenceIutTateFamilyBridge
import Solutions.Source_ReferenceIutTateStructureOfTorsion
import Solutions.Source_ReferenceIutTateUniformizationLaws

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open NumberField
open scoped Classical Valued

universe u

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The Tate uniformizations over the fixed torsion field at the bad places selected for P7. -/
noncomputable def tateFamily (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ) :=
  TateFamily.ofStructures C.E R.torsionField ℓ (C.VBadOf ℓ) fun w hw =>
    tateStructureOfBadPlace C.E R.torsionField (VBad := C.VBadOf ℓ) (w := w)
      (fun _ hv => hv.1) (fun _ hv v hvw => hv.2.2.2 v hvw) hw
      (exists_sq_eq_neg_c₄_mul_c₆ C.E R.torsionField (VBad := C.VBadOf ℓ)
        (fun _ hv => hv.1) (fun _ hv v hvw => hv.2.2.2 v hvw)
        hℓ hodd R.TK le_rfl (by rw [R.card_torsionBy_EK, sq]) hw)
      TateParameterUniformization.ofTateParameter

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
