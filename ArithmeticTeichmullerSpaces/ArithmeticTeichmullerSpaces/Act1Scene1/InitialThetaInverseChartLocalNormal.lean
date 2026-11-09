import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityInverseRawChart
import ArithmeticTeichmullerSpaces.Act1Scene1.InverseChartOriginLocalization
import Mathlib.RingTheory.Adjoin.FG

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the original raw chart is Noetherian and its origin localization is integrally closed.
Original proofs; no reference implementation copied.
boundary: this does not identify the infinity fiber with a projective cusp,
`AG.Cusp`, the distinguished torsion class or the theta-root model.
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

local instance infinityTranslationBaseRing_coefficientSMul :
    SMul (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toSMul

local instance infinityTranslationBaseRing_coefficientModule :
    Module (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toModule

local instance infinityTranslationBaseRing_selfTower :
    IsScalarTower (↥S.prime.torsionField) (↥S.prime.torsionField)
      S.infinityTranslationBaseRing :=
  IsScalarTower.of_algebraMap_eq
    (R := ↥S.prime.torsionField) (S := ↥S.prime.torsionField)
    (A := S.infinityTranslationBaseRing) (fun _ => rfl)

local instance infinityInverseRawChart_coefficientAlgebra :
    Algebra (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.infinityInverseRawChart.algebra'

local instance infinityInverseRawChart_commRing :
    CommRing S.infinityInverseRawChart :=
  S.infinityInverseRawChart.toCommRing

/-- The actual two-generator chart is a Noetherian ring over the coefficient field. -/
instance infinityInverseRawChart_isNoetherianRing :
    IsNoetherianRing S.infinityInverseRawChart := by
  apply isNoetherianRing_of_fg
  exact Subalgebra.fg_def.mpr
    ⟨({S.infinityTranslationInverseFirstCoordinate,
       S.infinityTranslationInverseSecondCoordinate} : Set S.infinityTranslationBaseRing),
      by simp, rfl⟩

private theorem infinityInverseRawOrigin_isPrime : S.infinityInverseRawOriginIdeal.IsPrime :=
  S.infinityInverseRawOriginIdeal_isMaximal.isPrime

attribute [local instance] infinityInverseRawOrigin_isPrime

/-- Integral closedness of the local ring at the same actual raw origin. -/
theorem infinityInverseRawOrigin_isIntegrallyClosed :
    IsIntegrallyClosed (Localization.AtPrime S.infinityInverseRawOriginIdeal) := by
  let k := ↥S.prime.torsionField
  let C := S.infinityTranslationBaseRing
  let B := S.infinityInverseRawChart
  let uB : B := InverseChartRawAlgebra.firstGenerator k
    S.infinityTranslationInverseFirstCoordinate S.infinityTranslationInverseSecondCoordinate
  let vB : B := InverseChartRawAlgebra.secondGenerator k
    S.infinityTranslationInverseFirstCoordinate S.infinityTranslationInverseSecondCoordinate
  let a₁ : B := algebraMap k B S.prime.EK.a₁
  let a₂ : B := algebraMap k B S.prime.EK.a₂
  let a₃ : B := algebraMap k B S.prime.EK.a₃
  let a₄ : B := algebraMap k B S.prime.EK.a₄
  let a₆ : B := algebraMap k B S.prime.EK.a₆
  have hrelation : vB ^ 2 = uB *
      (1 + a₂ * uB + a₄ * uB ^ 2 + a₆ * uB ^ 3 - a₁ * vB - a₃ * uB * vB) := by
    apply Subtype.val_injective
    change S.infinityTranslationInverseSecondCoordinate ^ 2 =
      S.infinityTranslationInverseFirstCoordinate *
        (1 + algebraMap k C S.prime.EK.a₂ * S.infinityTranslationInverseFirstCoordinate
          + algebraMap k C S.prime.EK.a₄ * S.infinityTranslationInverseFirstCoordinate ^ 2
          + algebraMap k C S.prime.EK.a₆ * S.infinityTranslationInverseFirstCoordinate ^ 3
          - algebraMap k C S.prime.EK.a₁ * S.infinityTranslationInverseSecondCoordinate
          - algebraMap k C S.prime.EK.a₃ * S.infinityTranslationInverseFirstCoordinate *
            S.infinityTranslationInverseSecondCoordinate)
    exact S.infinityTranslationInverseCoordinates_equation
  exact InverseChartOriginLocalization.isIntegrallyClosed_at_origin
    S.infinityInverseRawOriginIdeal uB vB a₁ a₂ a₃ a₄ a₆ rfl hrelation

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
