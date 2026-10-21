import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionGroups
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionPoints

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Pi1.lean` and `Genuine/Realize.lean`.
fidelity: actual Galois subgroups and finite fixed fields for the same arithmetic
seed's torsion field, chosen rank-one torsion line, and compatible division point.
The field/Galois identities and cover inclusions are proved from these objects.
boundary: Scene1/Derived. This does not identify affine normalizations or prove
etaleness, core, tempered comparison, or a theta-root model.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The signed/unsigned torsion-translation subgroup for this same seed. -/
def functionFieldCoverGroup (pm : Bool) : Subgroup (Genuine.Gal S.prime.EK) :=
  Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M pm

/-- The actual finite fixed field of the seed's subgroup. -/
def functionFieldCoverField (pm : Bool) :
    IntermediateField (Genuine.baseField S.prime.EK) S.functionFieldClosure :=
  Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M pm

theorem functionFieldCoverGroup_isOpen (pm : Bool) :
    IsOpen (S.functionFieldCoverGroup pm : Set (Genuine.Gal S.prime.EK)) :=
  Genuine.isOpen_Hgp S.prime.EK S.prime.ℓ S.prime.M pm

theorem functionFieldCoverGroup_isClosed (pm : Bool) :
    IsClosed (S.functionFieldCoverGroup pm : Set (Genuine.Gal S.prime.EK)) :=
  Genuine.isClosed_Hgp S.prime.EK S.prime.ℓ S.prime.M pm

theorem functionFieldCoverField_finite (pm : Bool) :
    FiniteDimensional (Genuine.baseField S.prime.EK) (S.functionFieldCoverField pm) :=
  Genuine.finiteDimensional_stabilizerField S.prime.EK S.prime.ℓ S.prime.M pm

theorem functionFieldCoverField_fixingSubgroup (pm : Bool) :
    (S.functionFieldCoverField pm).fixingSubgroup = S.functionFieldCoverGroup pm :=
  Genuine.fixingSubgroup_stabilizerField S.prime.EK S.prime.ℓ S.prime.M pm

theorem functionFieldCoverField_le_coordinateField (pm : Bool) :
    S.functionFieldCoverField pm ≤ Genuine.QField S.prime.EK S.prime.ℓ :=
  Genuine.stabilizerField_le_QField S.prime.EK S.prime.ℓ S.prime.M pm

/-- The fixed fields inherit the actual signed-quotient inclusion. -/
theorem functionFieldCoverField_signed_le_unsigned :
    S.functionFieldCoverField true ≤ S.functionFieldCoverField false :=
  Genuine.stabilizerField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M

/-- The level used by the subgroup is exactly the seed's proved generic division point. -/
theorem functionFieldCoverGroup_point_eq :
    Genuine.Qpt S.prime.EK S.prime.ℓ = S.functionFieldDivisionPoint S.prime.ℓ :=
  Genuine.Qpt_eq_divSys S.prime.EK S.prime.ℓ_prime.pos

/-- Multiplication by the admissible prime kills the chosen global torsion line. -/
theorem functionFieldCoverGroup_le_base (pm : Bool) :
    S.functionFieldCoverGroup pm ≤ Genuine.Hgp S.prime.EK 1 ⊥ pm := by
  apply Genuine.Hgp_le S.prime.EK (n := S.prime.ℓ) S.prime.ℓ_prime.pos
    (mul_one S.prime.ℓ) ?_ (fun h => h)
  intro R hR
  change S.prime.ℓ • R = 0
  exact (AddSubgroup.torsionBy.nsmul_iff).mp (S.prime.M_le_TK hR)

/-- The corresponding base-curve fixed field embeds in the seed's covering field. -/
theorem functionFieldCoverField_contains_base (pm : Bool) :
    Genuine.stabilizerField S.prime.EK 1 ⊥ pm ≤ S.functionFieldCoverField pm :=
  IntermediateField.fixedField_antitone (S.functionFieldCoverGroup_le_base pm)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
