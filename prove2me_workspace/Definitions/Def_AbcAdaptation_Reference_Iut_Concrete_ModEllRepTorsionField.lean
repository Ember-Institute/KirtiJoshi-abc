/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Cor312/ThetaData/LocalConditions.lean
-/
import Mathlib.FieldTheory.Galois.Infinite
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveData

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open NumberField

universe u

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The torsion field cut out by the kernel of the mod-`ℓ` representation. -/
noncomputable def torsionField : IntermediateField C.F C.Fbar :=
  IntermediateField.fixedField R.rep.ker

/-- The fixed field is finite over the base number field because the kernel is open. -/
instance numberField_torsionField : NumberField ↥R.torsionField := by
  have hle : R.rep.ker ≤ R.torsionField.fixingSubgroup :=
    (IntermediateField.le_iff_le R.rep.ker R.torsionField).mp le_rfl
  have hopen : IsOpen (R.torsionField.fixingSubgroup : Set (C.Fbar ≃ₐ[C.F] C.Fbar)) :=
    Subgroup.isOpen_mono hle R.ker_isOpen
  haveI : FiniteDimensional C.F ↥R.torsionField :=
    (InfiniteGalois.isOpen_iff_finite R.torsionField).mp hopen
  exact NumberField.of_module_finite C.F ↥R.torsionField

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
