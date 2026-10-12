/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Torsion/Count.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `405008c4c62cf451d297393f7e24611cf44ca55e`
additional-source: `refer/iut/Iut/Tower/IntegralTorsion.lean`, completeSquare,
completeSquare_a₁ and completeSquare_a₃, commit
`869a7edc0305e18297c600b7d860f9679791d227` (same authors and license)
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: transports the torsion count and basis through completion of
the square and supplies the basis to the candidate-prime representation.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Torsion.Count
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.VariableChangePoint
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaMaximalPrimeImage

/-!
source-id: IUT-COR312-GEOMETRIC-TORSION-BASIS
source: `Iut/Torsion/Count.lean`, `card_torsionBy_eq_sq` and `torsionBasis`;
`Iut/Tower/IntegralTorsion.lean`, the change of variables that completes the square.
fidelity: proves the torsion cardinality and basis for every elliptic curve
over an algebraically closed field of characteristic zero. The basis supplies
the genuine Galois representation and the maximal admissible-prime constructor.
The absence of a Galois-stable subgroup of order ell remains an explicit input.
This does not construct new orbicurves, local theta data or a Scene1 volume model.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open scoped Classical

universe u

noncomputable section

namespace IutGeometricTorsion

variable {k : Type u} [Field k]

/-- Complete the square without a restriction on the x coordinate. -/
def completeSquare (W : WeierstrassCurve k) : VariableChange k :=
  ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩

lemma completeSquare_a₁ (W : WeierstrassCurve k) [NeZero (2 : k)] :
    (completeSquare W • W).a₁ = 0 := by
  rw [variableChange_a₁]
  simp only [completeSquare, inv_one, Units.val_one, one_mul]
  field_simp
  ring

lemma completeSquare_a₃ (W : WeierstrassCurve k) [NeZero (2 : k)] :
    (completeSquare W • W).a₃ = 0 := by
  rw [variableChange_a₃]
  simp only [completeSquare, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero]
  field_simp
  ring

/-- An additive point equivalence preserves the n-torsion subgroup. -/
def torsionEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A ≃+ B) (n : ℕ) : AddSubgroup.torsionBy A n ≃+ AddSubgroup.torsionBy B n where
  toFun P := ⟨f P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero])⟩
  invFun P := ⟨f.symm P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero])⟩
  left_inv P := Subtype.ext (f.symm_apply_apply P.1)
  right_inv P := Subtype.ext (f.apply_symm_apply P.1)
  map_add' P Q := Subtype.ext (map_add f P.1 Q.1)

end IutGeometricTorsion

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- The n-torsion of any elliptic curve has n squared elements. -/
theorem iutGeometricTorsion_card (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) : Nat.card (AddSubgroup.torsionBy W.toAffine.Point n) = n ^ 2 := by
  let C := IutGeometricTorsion.completeSquare W
  let e := IutGeometricTorsion.torsionEquiv (JoshiTeich.ReferenceIut.Anabelian.vcEquiv C W) n
  rw [Nat.card_congr e.toEquiv]
  exact JoshiTeich.ReferenceIut.Torsion.card_torsionBy_eq_sq
    (IutGeometricTorsion.completeSquare_a₁ W) (IutGeometricTorsion.completeSquare_a₃ W) n hn

/-- The prime torsion of any elliptic curve has an additive rank two basis. -/
theorem iutGeometricTorsionBasis (W : WeierstrassCurve k) [W.IsElliptic]
    (ell : ℕ) [Fact ell.Prime] :
    Nonempty (AddSubgroup.torsionBy W.toAffine.Point ell ≃+ (Fin 2 → ZMod ell)) := by
  let C := IutGeometricTorsion.completeSquare W
  let e := IutGeometricTorsion.torsionEquiv (JoshiTeich.ReferenceIut.Anabelian.vcEquiv C W) ell
  obtain ⟨b⟩ := JoshiTeich.ReferenceIut.Torsion.torsionBasis
    (IutGeometricTorsion.completeSquare_a₁ W) (IutGeometricTorsion.completeSquare_a₃ W) ell
  exact ⟨e.trans b⟩

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

/-- Construct the actual mod ell representation without an external torsion basis. -/
def IutCurveModEllRepData.ofGeometricTorsion (ell : ℕ) (hp : ell.Prime) :
    IutCurveModEllRepData F E Fbar ell := by
  letI : CharZero Fbar :=
    charZero_of_injective_algebraMap (algebraMap F Fbar).injective
  letI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  letI : (Affine.baseChange E Fbar).IsElliptic := by
    change (E.map (algebraMap F Fbar)).IsElliptic
    infer_instance
  letI : Fact ell.Prime := ⟨hp⟩
  letI : NeZero ell := ⟨hp.ne_zero⟩
  exact IutCurveModEllRepData.ofBasis E Fbar ell
    (iutGeometricTorsionBasis (Affine.baseChange E Fbar) ell)

/-- The maximal prime constructor needs only the remaining cyclic subgroup obstruction. -/
def iutInitialThetaMaximalPrimeData_of_geometricTorsion
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {ell : ℕ} (hp : ell.Prime) (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (hP4 : ¬ IutHasCyclicSubgroup D.E D.Fbar ell) :
    JoshiTeich.ReferenceIut.AdmissiblePrimeData D.F D.E D.Fbar
      (IutOddMultiplicativeModSupport D) :=
  iutInitialThetaMaximalPrimeData_of_not_hasCyclicSubgroup D
    (IutCurveModEllRepData.ofGeometricTorsion D.E D.Fbar ell hp) hp hLarge hP4

end

end JoshiTeich.Act1Scene1
