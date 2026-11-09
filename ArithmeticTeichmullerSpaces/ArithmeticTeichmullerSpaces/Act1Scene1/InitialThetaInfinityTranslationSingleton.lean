import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInverseChartFractionField
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInverseChartLocalNormal
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationUniquePrime
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInverseChartIntegral
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationOrbit

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the original lower infinity fiber is a singleton by common fraction field, integrality and local normality.
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

local instance singleton_infinityTranslationBaseRing_coefficientSMul :
    SMul (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toSMul

local instance singleton_infinityTranslationBaseRing_coefficientModule :
    Module (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toModule

local instance singleton_infinityTranslationBaseRing_selfTower :
    IsScalarTower (↥S.prime.torsionField) (↥S.prime.torsionField)
      S.infinityTranslationBaseRing :=
  IsScalarTower.of_algebraMap_eq
    (R := ↥S.prime.torsionField) (S := ↥S.prime.torsionField)
    (A := S.infinityTranslationBaseRing) (fun _ => rfl)

local instance singleton_infinityInverseRawChart_coefficientAlgebra :
    Algebra (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.infinityInverseRawChart.algebra'

local instance singleton_infinityInverseRawChart_commRing :
    CommRing S.infinityInverseRawChart :=
  S.infinityInverseRawChart.toCommRing

/-- The same actual prime, regarded as lying over the raw-chart origin. -/
def infinityTranslationBaseFiberToRawPrimesOver
    (q : S.infinityTranslationBaseFiber) :
    S.infinityInverseRawOriginIdeal.primesOver S.infinityTranslationBaseRing := by
  refine ⟨q.1, q.2.1, ⟨?_⟩⟩
  change S.infinityInverseRawOriginIdeal = S.infinityInverseRawChart_center q
  exact (S.infinityInverseRawChart_center_eq_origin q).symm

theorem infinityTranslationBaseFiberToRawPrimesOver_injective :
    Function.Injective S.infinityTranslationBaseFiberToRawPrimesOver := by
  intro q r h
  apply Subtype.ext
  exact congrArg (fun p : S.infinityInverseRawOriginIdeal.primesOver
      S.infinityTranslationBaseRing => p.1) h

set_option maxHeartbeats 1000000 in
private theorem infinityInverseRawPrimes_subsingleton :
    Subsingleton (S.infinityInverseRawOriginIdeal.primesOver S.infinityTranslationBaseRing) := by
  let B := S.infinityInverseRawChart
  let C := S.infinityTranslationBaseRing
  let F := S.infinityTranslationBaseField
  let m := S.infinityInverseRawOriginIdeal
  let aCF : Algebra C F := C.toAlgebra
  letI : Algebra C F := aCF
  let aBC : Algebra B C := Subalgebra.toAlgebra (R := ↥S.prime.torsionField) B
  letI : Algebra B C := aBC
  let aBF : Algebra B F := Subalgebra.toAlgebra (R := ↥S.prime.torsionField) (α := F) B
  letI : Algebra B F := aBF
  letI : SMul B C := aBC.toSMul
  letI : SMul C F := aCF.toSMul
  letI : SMul B F := aBF.toSMul
  letI : IsScalarTower B C F :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := C) (A := F) (fun _ => rfl)
  letI : IsFractionRing B F := S.infinityInverseRawChart_isFractionRing
  letI : Algebra.IsIntegral B C :=
    S.infinityTranslationBaseRing_isIntegral_over_inverseRawChart
  letI : m.IsPrime := S.infinityInverseRawOriginIdeal_isMaximal.isPrime
  letI : IsIntegrallyClosed (Localization.AtPrime m) :=
    S.infinityInverseRawOrigin_isIntegrallyClosed
  exact NormalizationUniquePrime.primesOver_subsingleton_common_fractionField
    (R := B) (A := C) (K := F) m Subtype.val_injective

/-- The original lower infinity fiber has at most one prime. -/
instance infinityTranslationBaseFiber_subsingleton :
    Subsingleton S.infinityTranslationBaseFiber := by
  letI := S.infinityInverseRawPrimes_subsingleton
  exact Function.Injective.subsingleton
    S.infinityTranslationBaseFiberToRawPrimesOver_injective

attribute [local instance] infinityTranslationNormal
  infinityTranslationFiberAction infinityTranslationFiberSMul

/-- The original translation quotient acts transitively on the unsigned infinity fiber. -/
theorem infinityTranslationFiber_transitive
    (q₁ q₂ : S.infinityFiber false) :
    ∃ g : S.infinityTranslationGroup, g • q₁ = q₂ := by
  letI : Subsingleton S.infinityTranslationBaseFiber :=
    S.infinityTranslationBaseFiber_subsingleton
  exact (S.infinityTranslationFiberMap_eq_iff_orbit q₁ q₂).mp
    (Subsingleton.elim _ _)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
