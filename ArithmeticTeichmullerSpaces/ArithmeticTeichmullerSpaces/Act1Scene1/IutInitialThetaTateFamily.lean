import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPlaceSection
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.TateFamilyOfTorsion
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Torsion

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-TATE-FAMILY
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`JoshiTeich.ReferenceIut.tateFamilyOfTorsion`; `refer/iut/Iut/Anabelian/Torsion.lean`,
`AdmissiblePrimeData.TK` and `card_TK`; `ThetaData/AdmissiblePrime.lean`,
`AdmissiblePrimeData.ell_prime` and `five_le`.
fidelity: constructs the Tate family over the actual torsion field on the complete
odd multiplicative support, using the actual admissible-prime torsion subgroup.
It also restricts this family to each representative selected by the actual
InitialThetaData section. It does not identify this support with the paper's
`underline V^oss` or the Scene1 link carrier.
boundary: Scene1/Derived
-/

/-- IUT's torsion theorem constructs the Tate family on the complete odd
    multiplicative support of the actual initial theta datum. -/
noncomputable def iutInitialThetaTateFamilyOfTorsion
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.TateFamily D.E D.prime.torsionField D.prime.ℓ
      (iutVBadOddModSupportPort D) :=
  JoshiTeich.ReferenceIut.tateFamilyOfTorsion D.E D.prime.torsionField D.prime.ℓ
    (fun _ hv => hv.1)
    (fun _ hv w hw => hv.2.2 w hw)
    D.prime.ℓ_prime
    (by have h := D.prime.five_le; omega)
    D.prime.TK
    le_rfl
    (by rw [D.prime.card_TK, pow_two])

/-- The actual finite-place section selects a place carrying the corresponding
    Tate structure from the family above. -/
noncomputable def iutInitialThetaFinitePlaceSection_tateStructure
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    JoshiTeich.ReferenceIut.TateStructure (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField
      (iutInitialThetaFinitePlaceSection D v)) := by
  have hAlgebra : D.algebraModK =
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem := by
    apply Algebra.algebra_ext
    intro x
    apply Subtype.ext
    calc
      ((D.algebraModK.algebraMap x : ↥D.prime.torsionField) : D.Fbar) =
          ((algebraMap D.F ↥D.prime.torsionField
            (algebraMap (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F x) :
              ↥D.prime.torsionField) : D.Fbar) := by
        exact congrArg Subtype.val
          (@IsScalarTower.algebraMap_apply
            (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
            ↥D.prime.torsionField _ _ _ _ _ D.algebraModK D.towerModK x)
      _ = ((JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem.algebraMap x :
          ↥D.prime.torsionField) := rfl
  have hOver := hAlgebra ▸ iutInitialThetaFinitePlaceSection_liesOver D v
  let hw : JoshiTeich.ReferenceIut.IsBadPlace D.E D.prime.torsionField
      (iutVBadOddModSupportPort D)
      (iutInitialThetaFinitePlaceSection D v) := ⟨v, hv, hOver⟩
  exact (iutInitialThetaTateFamilyOfTorsion D).S _ hw

end

end JoshiTeich.Act1Scene1
