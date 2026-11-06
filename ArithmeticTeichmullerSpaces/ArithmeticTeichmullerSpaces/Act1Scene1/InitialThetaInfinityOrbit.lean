import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.PrimeFiberOrbit

/-!
source-id: JT-SCENE1-INITIAL-THETA-INFINITY-ORBIT-QUOTIENT-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
finite Galois descent of the actual boundary prime fibers.
fidelity: uses the original signed quotient action on the inverse-coordinate
normalization. The original infinity fiber map identifies its target with the
orbit quotient of its source, with the original map as the quotient projection.
Original proofs; no reference implementation copied.
boundary: this identifies the signed quotient of the actual closed-point
boundary. It does not identify that boundary with elliptic torsion, geometric
points, the distinguished epsilon, or the complete geometry producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityNormalizationField_field infinityNormalizationField_rationalBaseAlgebra
  infinityNormalizationField_baseAlgebra infinityNormalizationField_baseSMul
  infinityNormalizationField_baseModule infinityNormalizationField_coefficientAlgebra
  infinityNormalizationField_coefficientSMul infinityNormalizationField_coefficientModule
  infinityNormalizationField_coefficientBaseTower infinityNormalizationField_baseTower
  infinityNormalizationRing_baseAlgebra infinityNormalizationRing_baseSMul
  infinityNormalizationRing_baseModule infinityNormalizationRing_coefficientAlgebra
  infinityNormalizationRing_isDedekindDomain infinityNormalizationRing_finite
  infinityNormalizationRing_fractionField

attribute [local instance] infinitySignedFieldAlgebra infinitySignedFieldSMul
  infinitySignedFieldModule infinitySignedFieldBaseTower infinitySignedFieldAction
  infinitySignedFieldActionSMul infinityFieldBaseComm infinitySignedNormalizationAction
  infinitySignedNormalizationActionSMul infinitySignedRingAlgebra
  infinitySignedRingSMul infinitySignedRingModule infinitySignedNormalizationGaloisGroup

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinitySignedBaseRingTower :
    IsScalarTower S.infinityPolynomialBase (S.infinityNormalizationRing true)
      (S.infinityNormalizationRing false) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinitySignedBaseRingComm :
    SMulCommClass S.signedCoverQuotientGroup S.infinityPolynomialBase
      (S.infinityNormalizationRing false) where
  smul_comm g a b := Subtype.ext
    ((S.infinityFieldBaseComm).smul_comm g a (b : S.infinityNormalizationField false))

/-- The actual signed quotient acts on the inverse-coordinate prime fiber. -/
@[instance_reducible] def infinityFiberSignedAction :
    MulAction S.signedCoverQuotientGroup (S.infinityFiber false) := inferInstance

attribute [local instance] infinityFiberSignedAction

local instance infinityFiberSignedSMul :
    SMul S.signedCoverQuotientGroup (S.infinityFiber false) :=
  S.infinityFiberSignedAction.toSMul

theorem coe_infinityFiberSignedAction (g : S.signedCoverQuotientGroup)
    (q : S.infinityFiber false) :
    (g • q).1 = g • q.1 := rfl

private theorem infinityFiberMap_under (q : S.infinityFiber false) :
    (S.infinityFiberMap q).1 = q.1.under (S.infinityNormalizationRing true) :=
  S.infinityFiberMap_asIdeal q

theorem infinityFiberMap_smul (g : S.signedCoverQuotientGroup)
    (q : S.infinityFiber false) : S.infinityFiberMap (g • q) = S.infinityFiberMap q :=
  PrimeFiberOrbit.map_smul (G := S.signedCoverQuotientGroup)
    S.infinityBaseIdeal S.infinityFiberMap S.infinityFiberMap_under g q

/-- Two actual unsigned infinity primes have the same signed image exactly in one orbit. -/
theorem infinityFiberMap_eq_iff_orbit (q₁ q₂ : S.infinityFiber false) :
    S.infinityFiberMap q₁ = S.infinityFiberMap q₂ ↔
      ∃ g : S.signedCoverQuotientGroup, g • q₁ = q₂ :=
  PrimeFiberOrbit.map_eq_iff_exists_smul (G := S.signedCoverQuotientGroup)
    S.infinityBaseIdeal S.infinityFiberMap S.infinityFiberMap_under q₁ q₂

/-- The actual signed boundary is the orbit quotient of the unsigned boundary. -/
def infinityFiberOrbitQuotientEquiv :
    MulAction.orbitRel.Quotient S.signedCoverQuotientGroup (S.infinityFiber false) ≃
      S.infinityFiber true :=
  PrimeFiberOrbit.orbitQuotientEquiv (G := S.signedCoverQuotientGroup)
    S.infinityBaseIdeal S.infinityFiberMap S.infinityFiberMap_under S.infinityFiberMap_surjective

theorem infinityFiberOrbitQuotientEquiv_mk (q : S.infinityFiber false) :
    S.infinityFiberOrbitQuotientEquiv
      (Quotient.mk (MulAction.orbitRel S.signedCoverQuotientGroup (S.infinityFiber false)) q) =
      S.infinityFiberMap q := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
