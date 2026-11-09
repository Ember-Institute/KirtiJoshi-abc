import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationSingleton
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationCommonFractionResidue
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the same actual lower infinity fiber, its raw-origin center, common fraction
field, local integral closedness, and existing normalization denominators.
fidelity: the original coefficient map onto the original lower residue field
is surjective; its algebra equivalence and degree are obtained from that map.
No new residue certificate, field, prime or source hypothesis is supplied.
boundary: this is the LOWER residue field. It does not prove upper residue
degree one, arithmetic upper-prime stabilizer freeness, or a cusp identity.
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

local instance baseResidue_lowerCommRing :
    CommRing S.infinityTranslationBaseRing := S.infinityTranslationBaseRing.toCommRing

local instance baseResidue_lowerIsDomain :
    IsDomain S.infinityTranslationBaseRing := Subalgebra.isDomain _

local instance baseResidue_coefficientSMul :
    SMul (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toSMul

local instance baseResidue_coefficientModule :
    Module (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toModule

local instance baseResidue_selfTower :
    IsScalarTower (↥S.prime.torsionField) (↥S.prime.torsionField)
      S.infinityTranslationBaseRing :=
  IsScalarTower.of_algebraMap_eq
    (R := ↥S.prime.torsionField) (S := ↥S.prime.torsionField)
    (A := S.infinityTranslationBaseRing) (fun _ => rfl)

local instance baseResidue_rawCoefficientAlgebra :
    Algebra (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.infinityInverseRawChart.algebra'

local instance baseResidue_rawCommRing :
    CommRing S.infinityInverseRawChart :=
  S.infinityInverseRawChart.toCommRing

local instance baseResidue_rawIsDomain :
    IsDomain S.infinityInverseRawChart := Subalgebra.isDomain _

local instance baseResidue_rawCoefficientSMul :
    SMul (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.baseResidue_rawCoefficientAlgebra.toSMul

local instance baseResidue_rawCoefficientModule :
    Module (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.baseResidue_rawCoefficientAlgebra.toModule

local instance baseResidue_rawAlgebra :
    Algebra S.infinityInverseRawChart S.infinityTranslationBaseRing :=
  Subalgebra.toAlgebra (R := ↥S.prime.torsionField) S.infinityInverseRawChart

local instance baseResidue_rawSMul :
    SMul S.infinityInverseRawChart S.infinityTranslationBaseRing :=
  S.baseResidue_rawAlgebra.toSMul

local instance baseResidue_rawModule :
    Module S.infinityInverseRawChart S.infinityTranslationBaseRing :=
  S.baseResidue_rawAlgebra.toModule

local instance baseResidue_coefficientRawTower :
    IsScalarTower (↥S.prime.torsionField) S.infinityInverseRawChart
      S.infinityTranslationBaseRing :=
  IsScalarTower.of_algebraMap_eq
    (R := ↥S.prime.torsionField) (S := S.infinityInverseRawChart)
    (A := S.infinityTranslationBaseRing) (fun _ => rfl)

local instance baseResidue_originPrime :
    S.infinityInverseRawOriginIdeal.IsPrime :=
  S.infinityInverseRawOriginIdeal_isMaximal.isPrime

local instance baseResidue_prime (q : S.infinityTranslationBaseFiber) : q.1.IsPrime :=
  q.2.1

local instance baseResidue_quotientCommRing (q : S.infinityTranslationBaseFiber) :
    CommRing (S.infinityTranslationBaseRing ⧸ q.1) := Ideal.Quotient.commRing q.1

local instance baseResidue_quotientAlgebra (q : S.infinityTranslationBaseFiber) :
    Algebra (↥S.prime.torsionField) (S.infinityTranslationBaseRing ⧸ q.1) :=
  Ideal.Quotient.algebra (↥S.prime.torsionField) (I := q.1)

local instance baseResidue_residueField (q : S.infinityTranslationBaseFiber) :
    Field q.1.ResidueField := IsLocalRing.ResidueField.field (Localization.AtPrime q.1)

local instance baseResidue_residueAlgebra (q : S.infinityTranslationBaseFiber) :
    Algebra (↥S.prime.torsionField) q.1.ResidueField :=
  NormalizationResidueConstants.residueCoefficientAlgebra
    (k := ↥S.prime.torsionField) (A := S.infinityTranslationBaseRing) q.1

local instance baseResidue_residueSMul (q : S.infinityTranslationBaseFiber) :
    SMul (↥S.prime.torsionField) q.1.ResidueField :=
  (S.baseResidue_residueAlgebra q).toSMul

local instance baseResidue_residueModule (q : S.infinityTranslationBaseFiber) :
    Module (↥S.prime.torsionField) q.1.ResidueField :=
  (S.baseResidue_residueAlgebra q).toModule


end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
