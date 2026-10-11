/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/ModEllRepGalois.lean` and
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: projects the existing admissible-prime representation fields
into the local Scene1 representation contract and proves fixed-field alignment.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepFixedField

/-!
source-id: IUT-COR312-MODELLREP-ADMISSIBLE-ADAPTER
source: the representation fields of
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean` and the fixed-field
construction of `refer/iut/Iut/Concrete/ModEllRepGalois.lean`.
fidelity: the adapter preserves the actual torsion basis, Galois representation,
action formula, and open-kernel proof already carried by `AdmissiblePrimeData`.
It does not manufacture a new prime or prove the image condition; those remain
the corresponding explicit fields or later local-source obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (NumberField.FinitePlace ↥(
  JoshiTeich.ReferenceIut.fieldOfModuli F E))}

/-- The representation part of an existing admissible-prime datum. -/
def IutCurveModEllRepData.ofAdmissiblePrime
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad) :
    IutCurveModEllRepData F E Fbar P.ℓ :=
  { torsionBasis := P.torsionBasis
    rep := P.rep
    rep_spec := P.rep_spec
    ker_isOpen := P.ker_isOpen }

@[simp] theorem IutCurveModEllRepData.ofAdmissiblePrime_torsionField
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad) :
    IutCurveModEllRepData.torsionField E Fbar
        (IutCurveModEllRepData.ofAdmissiblePrime P) = P.torsionField := rfl

theorem IutCurveModEllRepData.ofAdmissiblePrime_sl_le_range
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod P.ℓ)) :
    A.toGL ∈ (IutCurveModEllRepData.ofAdmissiblePrime P).rep.range :=
  P.sl_le_range A

/-- The existing initial-Theta prime viewed through the local representation contract. -/
def iutInitialThetaModEllRepData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutCurveModEllRepData D.F D.E D.Fbar D.prime.ℓ :=
  IutCurveModEllRepData.ofAdmissiblePrime D.prime

@[simp] theorem iutInitialThetaModEllRepData_torsionField
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutCurveModEllRepData.torsionField D.E D.Fbar
        (iutInitialThetaModEllRepData D) = D.prime.torsionField := rfl

theorem iutInitialThetaModEllRepData_sl_le_range
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod D.prime.ℓ)) :
    A.toGL ∈ (iutInitialThetaModEllRepData D).rep.range :=
  D.prime.sl_le_range A

end

end JoshiTeich.Act1Scene1
