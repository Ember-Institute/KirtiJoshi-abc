import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationEtale
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnsignedNormalizationRamification
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib `HasRingHomProperty.Spec_iff`.
fidelity: the same seed's original unsigned normalization map is finite etale.
The algebra structure is induced by the original base-to-cover ring map.
boundary: Scene1/Derived. This proves ordinary scheme etaleness. Orbicurve
comparison, the cartesian square, core and the full producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] unsignedBaseCoefficientAlgebra unsignedCoverCoefficientAlgebra
  unsignedCoverNormalizationAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem unsignedCoverNormalization_etale :
    Algebra.Etale (S.baseNormalizationRing false) (S.coverNormalizationRing false) :=
  Genuine.unsignedNormalization_etale S.prime.EK S.prime.ℓ S.prime.M

theorem baseToCoverUnsignedNormalizationRingMap_etale :
    (S.baseToCoverNormalizationRingMap false).toRingHom.Etale := by
  have := S.unsignedCoverNormalization_etale
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The existing finite normalization morphism is etale on its entire domain. -/
instance etale_coverToBaseUnsignedNormalizationMap :
    AlgebraicGeometry.Etale (S.coverToBaseNormalizationMap false) :=
  AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr
    S.baseToCoverUnsignedNormalizationRingMap_etale

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
