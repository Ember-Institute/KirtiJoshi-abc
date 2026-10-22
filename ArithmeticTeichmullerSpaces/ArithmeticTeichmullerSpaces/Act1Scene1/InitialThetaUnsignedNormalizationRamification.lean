import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationFinite
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOrbicurvePresentation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Homs.lean`, ramificationIdx_geom_eq_one.
fidelity: the same seed's actual unsigned base-to-cover normalization inclusion
has ramification index one at every closed point of the cover.
boundary: Scene1/Derived. This proves the ramification law for that original
inclusion. Orbicurve comparison, cartesianness and the producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance unsignedBaseCoefficientAlgebra :
    Algebra ↥S.prime.torsionField (S.baseNormalizationRing false) :=
  normalizationCoefficientAlgebra S.prime.EK 1 ⊥ false

local instance unsignedCoverCoefficientAlgebra :
    Algebra ↥S.prime.torsionField (S.coverNormalizationRing false) :=
  normalizationCoefficientAlgebra S.prime.EK S.prime.ℓ S.prime.M false

/-- Use the original unsigned base-to-cover normalization ring map as its algebra. -/
@[instance_reducible] def unsignedCoverNormalizationAlgebra :
    Algebra (S.baseNormalizationRing false) (S.coverNormalizationRing false) :=
  (S.baseToCoverNormalizationRingMap false).toRingHom.toAlgebra

attribute [local instance] unsignedCoverNormalizationAlgebra

theorem unsignedCoverNormalization_ramificationIdx_one
    (w : Ideal (S.coverNormalizationRing false)) (hw : w.IsMaximal) :
    w.ramificationIdx (S.baseNormalizationRing false) = 1 :=
  Genuine.unsignedNormalization_ramificationIdx_one S.prime.EK S.prime.ℓ S.prime.M w hw

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
