import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityGeometricPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotientNontrivial
import ArithmeticTeichmullerSpaces.Act1Scene1.OrbitStabilizerNatCard

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the actual geometric-point inertia theorem and signed quotient order.
fidelity: reuses the original geometric point action and proves that its
orbit cardinality times the actual inertia cardinality equals two.
The numerical transport uses the already proved generic orbit-stabilizer law.
Original proof; no reference implementation copied.
boundary: Scene1/Derived. This does not select either factor, identify the
point with a torsion cusp or epsilon, or construct an AG orbicurve realization.
-/

namespace JoshiTeich.Act1Scene1

private theorem orbit_card_mul_of_stabilizer_card
    {G X : Type*} [Group G] [MulAction G X]
    (x : X) {i g : ℕ}
    (hi : Nat.card (MulAction.stabilizer G x) = i)
    (hg : Nat.card G = g) :
    Nat.card (MulAction.orbit G x) * i = g :=
  (congrArg (fun n : ℕ => Nat.card (MulAction.orbit G x) * n) hi.symm).trans
    ((OrbitStabilizerNatCard.orbit_card_mul_stabilizer_card x).trans hg)

end JoshiTeich.Act1Scene1

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
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
  infinitySignedFieldAlgebra infinitySignedFieldSMul infinitySignedFieldModule
  infinitySignedFieldBaseTower infinitySignedFieldAction infinitySignedFieldActionSMul
  infinityFieldBaseComm infinitySignedNormalizationAction infinitySignedNormalizationActionSMul
  infinitySignedRingAlgebra infinitySignedRingSMul infinitySignedRingModule
  infinitySignedNormalizationGaloisGroup

attribute [local instance] infinitySignedNormalizationAction

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

-- Reuse the already compiled action, instead of reconstructing it through instance search.
local instance geometricOrbitPointAction (C : Type u) [CommRing C] :
    MulAction S.signedCoverQuotientGroup
      (S.infinityNormalizationRing false →+* C) :=
  infinityNormalizationPointAction S C

attribute [local instance] geometricOrbitPointAction

theorem signedCoverQuotientGroup_card_eq_two :
    Nat.card S.signedCoverQuotientGroup = 2 :=
  Genuine.signedGaloisGroup_card_eq_two S.prime.EK S.prime.ℓ S.prime.M

/-- The actual geometric orbit size times actual inertia order is two. -/
theorem infinityNormalizationGeometricOrbit_mul_inertia_card
    (q : S.infinityFiber false) :
    Nat.card (MulAction.orbit S.signedCoverQuotientGroup
      (S.infinityNormalizationGeometricPoint q)) *
      Nat.card (q.1.inertia S.signedCoverQuotientGroup) = 2 :=
  orbit_card_mul_of_stabilizer_card
    (S.infinityNormalizationGeometricPoint q)
    (S.infinityNormalizationGeometricPoint_stabilizer_card q)
    S.signedCoverQuotientGroup_card_eq_two

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
