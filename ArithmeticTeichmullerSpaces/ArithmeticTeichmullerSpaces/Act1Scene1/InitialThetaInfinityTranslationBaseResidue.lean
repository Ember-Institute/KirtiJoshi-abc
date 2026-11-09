import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationResidueStructures
import ArithmeticTeichmullerSpaces.Act1Scene1.ResidueCoefficientEquivalence
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationSubalgebraDenominators

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original lower infinity fiber, raw origin and common-fraction-field denominators.
fidelity: identifies the original lower residue field by its actual coefficient map.
boundary: upper residue fields, arithmetic stabilizers and cusp identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityTranslationBaseField_field infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra
  infinityTranslationBaseField_baseTower infinityTranslationBaseField_coefficientTower
  infinityTranslationBaseRing_baseAlgebra infinityTranslationBaseRing_baseSMul
  infinityTranslationBaseRing_baseModule infinityTranslationBaseRing_coefficientAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

attribute [local instance] baseResidue_lowerCommRing
  baseResidue_lowerIsDomain
  baseResidue_coefficientSMul
  baseResidue_coefficientModule
  baseResidue_selfTower
  baseResidue_rawCoefficientAlgebra
  baseResidue_rawCommRing
  baseResidue_rawIsDomain
  baseResidue_rawCoefficientSMul
  baseResidue_rawCoefficientModule
  baseResidue_rawAlgebra
  baseResidue_rawSMul
  baseResidue_rawModule
  baseResidue_coefficientRawTower
  baseResidue_originPrime
  baseResidue_prime
  baseResidue_quotientCommRing
  baseResidue_quotientAlgebra
  baseResidue_residueField
  baseResidue_residueAlgebra
  baseResidue_residueSMul
  baseResidue_residueModule

/-- Each element of the ORIGINAL lower normalization has a raw-chart denominator
outside the ORIGINAL raw origin. -/
theorem infinityTranslationBaseRing_origin_denominators
    (x : S.infinityTranslationBaseRing) :
    ∃ a : S.infinityInverseRawChart,
      ∃ s : S.infinityInverseRawOriginIdeal.primeCompl,
        x * algebraMap S.infinityInverseRawChart S.infinityTranslationBaseRing s =
          algebraMap S.infinityInverseRawChart S.infinityTranslationBaseRing a := by
  let C := S.infinityTranslationBaseRing
  let F := S.infinityTranslationBaseField
  letI : Algebra C F := C.toAlgebra
  letI : SMul C F := (inferInstance : Algebra C F).toSMul
  exact NormalizationResidueConstants.denominators_subalgebra_common_fractionField
    (k := ↥S.prime.torsionField) (A := C) (K := F)
    S.infinityInverseRawChart S.infinityInverseRawOriginIdeal
    S.infinityInverseRawChart_isFractionRing
    S.infinityTranslationBaseRing_isIntegral_over_inverseRawChart
    S.infinityInverseRawOrigin_isIntegrallyClosed
    Subtype.val_injective x

/-- The ORIGINAL lower boundary prime is maximal by its original polynomial zero-fiber membership. -/
theorem infinityTranslationBaseFiber_isMaximal
    (q : S.infinityTranslationBaseFiber) : q.1.IsMaximal := by
  letI : (zeroBaseIdeal (Genuine.xG S.prime.EK)⁻¹
      S.infinityTranslation_inverseCoordinate_transcendental).IsMaximal :=
    zeroBaseIdeal_isMaximal (Genuine.xG S.prime.EK)⁻¹
      S.infinityTranslation_inverseCoordinate_transcendental
  letI : Algebra.IsIntegral S.infinityPolynomialBase S.infinityTranslationBaseRing :=
    integralClosure.AlgebraIsIntegral
  exact Ideal.isMaximal_of_mem_primesOver
    (p := zeroBaseIdeal (Genuine.xG S.prime.EK)⁻¹
      S.infinityTranslation_inverseCoordinate_transcendental)
    (B := S.infinityTranslationBaseRing) q.2

/-- The ORIGINAL lower normalization quotient has only coefficient-field constants. -/
theorem infinityTranslationBaseQuotient_algebraMap_surjective
    (q : S.infinityTranslationBaseFiber) :
    Function.Surjective
      (algebraMap (↥S.prime.torsionField) (S.infinityTranslationBaseRing ⧸ q.1)) := by
  letI : q.1.IsMaximal := S.infinityTranslationBaseFiber_isMaximal q
  letI : q.1.LiesOver S.infinityInverseRawOriginIdeal :=
    (S.infinityTranslationBaseFiberToRawPrimesOver q).2.2
  exact NormalizationResidueConstants.quotient_constants_surjective_of_denominators
    S.infinityInverseRawOriginIdeal q.1
    (InverseChartRawAlgebra.quotient_algebraMap_surjective
      (↥S.prime.torsionField)
      S.infinityTranslationInverseFirstCoordinate S.infinityTranslationInverseSecondCoordinate)
    S.infinityTranslationBaseRing_origin_denominators

/-- The coefficient map onto the ORIGINAL lower residue field is surjective. -/
theorem infinityTranslationBaseResidue_algebraMap_surjective
    (q : S.infinityTranslationBaseFiber) :
    Function.Surjective (algebraMap (↥S.prime.torsionField) q.1.ResidueField) := by
  letI : q.1.IsMaximal := S.infinityTranslationBaseFiber_isMaximal q
  exact NormalizationResidueConstants.residue_constants_surjective_of_quotient
    (k := ↥S.prime.torsionField) q.1
    (S.infinityTranslationBaseQuotient_algebraMap_surjective q)

/-- The identity on coefficients gives the actual lower-residue algebra equivalence. -/
def infinityTranslationBaseResidueEquiv
    (q : S.infinityTranslationBaseFiber) :
    (↥S.prime.torsionField) ≃ₐ[↥S.prime.torsionField] q.1.ResidueField :=
  NormalizationResidueConstants.coefficientEquivOfSurjective
    (↥S.prime.torsionField) q.1.ResidueField
    (S.infinityTranslationBaseResidue_algebraMap_surjective q)

/-- Its degree over the same coefficient field is exactly one. -/
theorem infinityTranslationBaseResidue_finrank
    (q : S.infinityTranslationBaseFiber) :
    Module.finrank (↥S.prime.torsionField) q.1.ResidueField = 1 :=
  NormalizationResidueConstants.coefficient_finrank_eq_one
    (↥S.prime.torsionField) q.1.ResidueField
    (S.infinityTranslationBaseResidueEquiv q)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
