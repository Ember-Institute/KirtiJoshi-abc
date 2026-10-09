import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-SELECTED-QROOT-RESIDUE-ALIGNMENT
source: the selected `IutTorsionQRootSource` carrier and its `liesOver`
field, together with `Arithmetic.residueChar_eq_of_liesOver`.
fidelity: exposes the residue-characteristic equality already implied by
the selected source/base-place contraction. This is an index alignment
lemma; it does not choose paper `L'` representatives or remove any
q-pilot/residue-degree weight.
boundary: Scene1/Derived
-/

/-! A selected source place and its contracted base place have the same
residue characteristic. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlace_residueChar_eq_basePlace
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}) :
    Arithmetic.residueChar s.1.1 =
      Arithmetic.residueChar
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1 := by
  exact Arithmetic.residueChar_eq_of_liesOver
    ((iutInitialThetaOddSupportTorsionQRootSource D).liesOver s.1)

/-! Filtering by a rational prime is therefore independent of whether the
selected carrier is indexed by source places or contracted base places. -/
theorem iutInitialThetaOddSupportSelectedQRootSourcePlace_residueChar_eq_iff
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D})
    (p : ℕ) :
    Arithmetic.residueChar s.1.1 = p ↔
      Arithmetic.residueChar
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1 = p := by
  rw [iutInitialThetaOddSupportSelectedQRootSourcePlace_residueChar_eq_basePlace D s]

end

end JoshiTeich.Act1Scene1
