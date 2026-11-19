/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/Existence.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic
import Solutions.Source_ReferenceIutCurveThetaInputs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve OrbicurveDataSection

universe u

/-- The reference anabelian existence interface over the canonical inclusion of the moduli
field into the torsion field. The local witness uses the very orbicurve supplied by the
existential quantifier. -/
structure AnabelianExistence (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) :
    Prop where
  exists_data : ∀ (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F)
    [E.IsElliptic] (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    (VBad : Set (FinitePlace ↥(fieldOfModuli F E))) (P : AdmissiblePrimeData F E Fbar VBad)
    [NumberField ↥P.torsionField] (_TF : TateFamily E P.torsionField P.ℓ VBad),
    IsInitialThetaGlobalData F E Fbar VBad → HasCoreUniversally AG F E →
    letI : Algebra ↥(fieldOfModuli F E) ↥P.torsionField :=
      (fieldOfModuli F E).instAlgebraSubtypeMem
    ∃ O : OrbicurveData AG F E Fbar VBad P,
      Nonempty (LocalThetaData AG TG F E Fbar VBad P O)

namespace EllipticCurveData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- Assemble IUT I, Definition 3.1 at the admissible prime of the given curve.
The supplied Tate family is over the fixed field of the given representation.
The same family is passed to the geometry witness and stored in the result. -/
noncomputable def thetaData
    (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
    (TF : TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ))
    (anab : AnabelianExistence AG TG) (hcore : HasCoreUniversally AG C.F C.E) :
    InitialThetaData AG TG := by
  let P := C.primeData CA TI hℓ h7 R hsl hP2
  letI : NumberField ↥P.torsionField := R.numberField_torsionField
  letI : Algebra ↥(fieldOfModuli C.F C.E) ↥P.torsionField :=
    (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli C.F C.E) ↥P.torsionField =
      (algebraMap C.F ↥P.torsionField).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F) :=
    RingHom.ext fun _ => rfl
  let G := C.globalData CA hP5
  let h := anab.exists_data C.F C.E C.Fbar (C.VBadOf ℓ) P TF G hcore
  exact
    { F := C.F
      Fbar := C.Fbar
      E := C.E
      VBad := C.VBadOf ℓ
      global := G
      prime := P
      numberFieldK := R.numberField_torsionField
      algebraModK := (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
      towerModK := IsScalarTower.of_algebraMap_eq' hmap
      tate := TF
      orb := h.choose
      localData := h.choose_spec.some }

end EllipticCurveData
end AbcAdaptation.Reference.Iut
