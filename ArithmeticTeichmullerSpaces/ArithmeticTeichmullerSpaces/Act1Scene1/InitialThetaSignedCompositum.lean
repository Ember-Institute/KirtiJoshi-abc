import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedCompositum
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationFinite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d), the cartesian covering diagram;
Joshi III `ss:theta-data-fixing2`.
fidelity: identifies the same seed's unsigned covering field as the compositum
of its signed covering field and original unsigned elliptic field. Gives the
resulting criterion for containment in any actual ambient intermediate field.
boundary: Scene1/Derived. This is the function-field part of the covering
construction. No orbicurve cartesian or scheme pullback law is assumed.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem functionFieldCoverField_unsigned_eq_sup :
    S.functionFieldCoverField false = S.functionFieldCoverField true ⊔
      Genuine.stabilizerField S.prime.EK 1 ⊥ false :=
  Genuine.stabilizerField_unsigned_eq_sup S.prime.EK S.prime.ℓ S.prime.M

theorem normalizationFieldCover_unsigned_eq_sup :
    Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false =
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M true ⊔
        Genuine.normalizationField S.prime.EK 1 ⊥ false :=
  Genuine.normalizationField_unsigned_eq_sup S.prime.EK S.prime.ℓ S.prime.M

/-- These two fields generate the entire actual unsigned normalization field. -/
theorem normalizationFieldCover_le_iff
    (N : IntermediateField (Genuine.xLine S.prime.EK) S.functionFieldClosure) :
    Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false ≤ N ↔
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M true ≤ N ∧
        Genuine.normalizationField S.prime.EK 1 ⊥ false ≤ N := by
  rw [S.normalizationFieldCover_unsigned_eq_sup, sup_le_iff]

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
