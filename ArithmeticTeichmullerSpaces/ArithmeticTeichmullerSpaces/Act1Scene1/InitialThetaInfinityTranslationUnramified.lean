import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFinitePrimeLift
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationGalois

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original finite-inertia field containment and normalization ramification criterion.
fidelity: applies the existing ramification-one criterion to a lift of the
ORIGINAL unsigned infinity prime. The conclusion uses the original lower ring,
the original upper ring, and the original translation ring algebra.
Original composition of existing project theorems; no reference implementation copied.
boundary: no statement about residue degree, arithmetic prime stabilizers,
projective cusps, AG.Cusp or theta-root identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve IsDedekindDomain
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section

attribute [local instance 2000] Classical.propDecidable
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
  infinityTranslationBaseField_field infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra
  infinityTranslationBaseField_baseTower infinityTranslationBaseField_coefficientTower
  infinityTranslationBaseRing_baseAlgebra infinityTranslationBaseRing_baseSMul
  infinityTranslationBaseRing_baseModule infinityTranslationBaseRing_coefficientAlgebra
  infinityDivisionNormalClosure_field infinityDivisionNormalClosure_rationalAlgebra
  infinityDivisionNormalClosure_baseAlgebra infinityDivisionNormalClosure_baseSMul
  infinityDivisionNormalClosure_baseModule infinityDivisionNormalClosure_coefficientAlgebra
  infinityDivisionNormalClosure_coefficientSMul infinityDivisionNormalClosure_coefficientModule
  infinityDivisionNormalClosure_coefficientBaseTower infinityDivisionNormalClosure_baseTower
  infinityDivisionClosure_separable infinityDivisionClosureRing_baseAlgebra
  infinityDivisionClosureRing_dedekind infinityDivisionClosureRing_fraction
  galoisNormalizationCoeffComm fieldRingAction

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The original unsigned infinity normalization is unramified over its original lower ring. -/
theorem infinityTranslation_ramificationIdx_one
    (q : S.infinityFiber false) :
    (letI := S.infinityTranslationRingAlgebra
     q.1.ramificationIdx S.infinityTranslationBaseRing) = 1 := by
  have hex := S.infinityDivisionClosure_exists_prime_over q
  let p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure) := hex.choose
  have hpmax : p.asIdeal.IsMaximal := hex.choose_spec.1
  have hpq : p.asIdeal.comap (ringMap S.infinityUnsignedField_le_divisionNormalClosure) =
      q.1 := hex.choose_spec.2.1
  have hpcenter : algebraMap S.infinityPolynomialBase
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      S.infinityCoordinate ∈ p.asIdeal := hex.choose_spec.2.2
  change (letI := ringMapAlgebra S.infinityTranslationBaseField_le
    q.1.ramificationIdx S.infinityTranslationBaseRing) = 1
  exact ramificationIdx_one_of_prime_lift
    S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityTranslationBaseField_le S.infinityUnsignedField_le_divisionNormalClosure
    q.1 p hpmax hpq (S.infinityClosurePrime_inertia_fixSub_le p hpcenter)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
