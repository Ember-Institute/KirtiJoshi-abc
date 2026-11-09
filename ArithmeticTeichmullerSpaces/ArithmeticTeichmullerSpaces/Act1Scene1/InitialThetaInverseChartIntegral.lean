import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityInverseRawChart
import ArithmeticTeichmullerSpaces.Act1Scene1.AdjoinImageMembership

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the original normalization is integral over its actual raw inverse chart.
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

local instance inverseIntegral_infinityTranslationBaseRing_coefficientSMul :
    SMul (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toSMul

local instance inverseIntegral_infinityTranslationBaseRing_coefficientModule :
    Module (↥S.prime.torsionField) S.infinityTranslationBaseRing :=
  S.infinityTranslationBaseRing_coefficientAlgebra.toModule

local instance inverseIntegral_infinityTranslationBaseRing_selfTower :
    IsScalarTower (↥S.prime.torsionField) (↥S.prime.torsionField)
      S.infinityTranslationBaseRing :=
  IsScalarTower.of_algebraMap_eq
    (R := ↥S.prime.torsionField) (S := ↥S.prime.torsionField)
    (A := S.infinityTranslationBaseRing) (fun _ => rfl)

local instance inverseIntegral_infinityInverseRawChart_coefficientAlgebra :
    Algebra (↥S.prime.torsionField) S.infinityInverseRawChart :=
  S.infinityInverseRawChart.algebra'

local instance inverseIntegral_infinityInverseRawChart_commRing :
    CommRing S.infinityInverseRawChart :=
  S.infinityInverseRawChart.toCommRing

private def infinityPolynomialBaseToTranslationBase :
    S.infinityPolynomialBase →ₐ[↥S.prime.torsionField] S.infinityTranslationBaseRing :=
  { (algebraMap S.infinityPolynomialBase S.infinityTranslationBaseRing) with
    commutes' := fun _ => rfl }

/-- The existing polynomial base maps into the actual raw inverse chart. -/
theorem infinityPolynomialBase_image_mem_inverseRawChart
    (a : S.infinityPolynomialBase) :
    algebraMap S.infinityPolynomialBase S.infinityTranslationBaseRing a ∈
      S.infinityInverseRawChart := by
  exact AdjoinImageMembership.image_mem_singleton
    (k := ↥S.prime.torsionField) (Genuine.xG S.prime.EK)⁻¹
    S.infinityPolynomialBaseToTranslationBase S.infinityInverseRawChart
    (by
      change S.infinityTranslationInverseFirstCoordinate ∈ S.infinityInverseRawChart
      exact Algebra.subset_adjoin (Set.mem_insert _ _)) a

/-- The original polynomial-base inclusion, with codomain restricted to B. -/
def infinityPolynomialBaseToInverseRawChart :
    S.infinityPolynomialBase →ₐ[↥S.prime.torsionField] S.infinityInverseRawChart := by
  exact S.infinityPolynomialBaseToTranslationBase.codRestrict S.infinityInverseRawChart
    S.infinityPolynomialBase_image_mem_inverseRawChart

@[simp] theorem coe_infinityPolynomialBaseToInverseRawChart
    (a : S.infinityPolynomialBase) :
    (S.infinityPolynomialBaseToInverseRawChart a : S.infinityTranslationBaseRing) =
      algebraMap S.infinityPolynomialBase S.infinityTranslationBaseRing a := rfl

/-- Enlarging the base from k[u] to its actual intermediate raw chart preserves
the existing integrality of the normalization. -/
theorem infinityTranslationBaseRing_isIntegral_over_inverseRawChart :
    Algebra.IsIntegral S.infinityInverseRawChart S.infinityTranslationBaseRing := by
  refine ⟨fun x => ?_⟩
  apply RingHom.isIntegralElem.of_comp
    S.infinityPolynomialBaseToInverseRawChart.toRingHom
    S.infinityInverseRawChart.val.toRingHom
  change IsIntegral S.infinityPolynomialBase x
  exact integralClosure.isIntegral x

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
