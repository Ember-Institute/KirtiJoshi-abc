import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationGeometricPoints

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original residue geometric point's stabilizer/inertia identity and orbit formula.
fidelity: consumes triviality of the original translation inertia on the original
normalization and identifies the original geometric orbit cardinality with the
same admissible prime ell. No prime-fiber cardinality or residue-degree input
is supplied or inferred.
boundary: the geometric point includes a residue-field embedding. Its trivial
stabilizer does not assert arithmetic prime-stabilizer triviality, residue degree
one, torsion-boundary equivalence, projective cusp, AG.Cusp or theta-root identity.
-/

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
  infinityTranslationNormal
  infinityTranslationFieldAlgebra infinityTranslationFieldSMul infinityTranslationFieldModule
  infinityTranslationFieldAction infinityTranslationFieldActionSMul
  infinityTranslationFieldBaseComm infinityTranslationNormalizationAction
  infinityTranslationNormalizationSMul infinityTranslationGeometricPointAction

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The original translation action has trivial stabilizer at each original residue geometric point. -/
theorem infinityTranslationGeometricPoint_stabilizer_eq_bot (q : S.infinityFiber false) :
    MulAction.stabilizer S.infinityTranslationGroup
      (S.infinityNormalizationGeometricPoint q) = ⊥ :=
  (S.infinityTranslationGeometricPoint_stabilizer q).trans
    (S.infinityTranslationPrimeInertia_eq_bot q)

/-- The original translation geometric orbit has the same size as the admissible prime. -/
theorem infinityTranslationGeometricOrbit_card_eq_ell (q : S.infinityFiber false) :
    Nat.card (MulAction.orbit S.infinityTranslationGroup
      (S.infinityNormalizationGeometricPoint q)) = S.prime.ℓ := by
  have h := S.infinityTranslationGeometricOrbit_mul_inertia_card q
  simpa only [S.infinityTranslationPrimeInertia_card_eq_one q, mul_one] using h

/-- Only the identity translation fixes this geometric point, including its residue embedding. -/
theorem infinityTranslationGeometricPoint_smul_eq_iff
    (q : S.infinityFiber false) (g : S.infinityTranslationGroup) :
    g • S.infinityNormalizationGeometricPoint q = S.infinityNormalizationGeometricPoint q ↔
      g = 1 := by
  change g ∈ MulAction.stabilizer S.infinityTranslationGroup
    (S.infinityNormalizationGeometricPoint q) ↔ g = 1
  rw [S.infinityTranslationGeometricPoint_stabilizer_eq_bot q]
  exact Subgroup.mem_bot

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
