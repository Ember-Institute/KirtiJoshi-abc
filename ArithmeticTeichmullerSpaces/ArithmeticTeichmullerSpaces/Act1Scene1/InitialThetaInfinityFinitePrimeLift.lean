import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFinitePrimeFieldInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationCenteredPrimeLift

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original inverse-coordinate normalization fiber and the already proved
normalization lying-over theorem.
fidelity: lifts every ORIGINAL unsigned infinity prime to the SAME actual
finite division normal closure, and transports the original inverse-coordinate
center through the exact normalization ring map. No new point or normal field
is selected as caller input.
boundary: does not assert a cusp identity or arithmetic prime-stabilizer freeness.
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

/-- The original unsigned boundary prime is maximal, not merely prime. -/
theorem infinityUnsignedFiber_isMaximal (q : S.infinityFiber false) : q.1.IsMaximal := by
  have hint : (algebraMap S.infinityPolynomialBase
      (S.infinityNormalizationRing false)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'
    (algebraMap S.infinityPolynomialBase (S.infinityNormalizationRing false)) hint q.1
  change (q.1.under S.infinityPolynomialBase).IsMaximal
  rw [← q.2.2.over]
  exact S.infinityBaseIdeal_isMaximal

/-- The original inverse coordinate lies in every original unsigned boundary prime. -/
theorem infinityUnsignedFiber_inverseCoordinate_mem (q : S.infinityFiber false) :
    algebraMap S.infinityPolynomialBase (S.infinityNormalizationRing false)
      S.infinityCoordinate ∈ q.1 := by
  change S.infinityCoordinate ∈ q.1.under S.infinityPolynomialBase
  rw [← q.2.2.over]
  exact S.infinityCoordinate_mem_baseIdeal

/-- Lift the original upper infinity prime, retaining its contraction and inverse center. -/
theorem infinityDivisionClosure_exists_prime_over
    (q : S.infinityFiber false) :
    ∃ p : HeightOneSpectrum
        (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure),
      p.asIdeal.IsMaximal ∧
      p.asIdeal.comap (ringMap S.infinityUnsignedField_le_divisionNormalClosure) = q.1 ∧
      algebraMap S.infinityPolynomialBase
        (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
        S.infinityCoordinate ∈ p.asIdeal :=
  exists_heightOne_over_center
    (k := ↥S.prime.torsionField) (Ω := Genuine.Ω S.prime.EK)
    (t := (Genuine.xG S.prime.EK)⁻¹)
    (F := S.infinityNormalizationField false) (N := S.infinityDivisionNormalClosure)
    S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityUnsignedField_le_divisionNormalClosure q.1 (S.infinityUnsignedFiber_isMaximal q)
    S.infinityCoordinate (S.infinityUnsignedFiber_inverseCoordinate_mem q)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
