import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.PrimeFiberOrbit

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the original translation quotient, its actual infinity normalization action,
and the proved finite invariant prime-fiber orbit theorem.
fidelity: the original upper unsigned infinity fiber carries the original
translation quotient action. Its actual contraction to the full-TK lower
infinity fiber is the orbit projection, with equality of contractions exactly
the orbit relation. No new action or source certificate is supplied.
boundary: Scene1/Derived. This does not prove the lower fiber is a singleton,
that the upper action is free, or a torsion-cusp/AG realization identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical Pointwise IntermediateField.algebraAdjoinAdjoin
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

attribute [local instance] infinityTranslationBaseField_field
  infinityTranslationBaseField_rationalAlgebra infinityTranslationBaseField_baseAlgebra
  infinityTranslationBaseField_baseSMul infinityTranslationBaseField_baseModule
  infinityTranslationBaseField_coefficientAlgebra infinityTranslationBaseField_baseTower
  infinityTranslationBaseField_coefficientTower infinityTranslationBaseRing_baseAlgebra
  infinityTranslationBaseRing_baseSMul infinityTranslationBaseRing_baseModule
  infinityTranslationBaseRing_coefficientAlgebra

attribute [local instance] infinityTranslationNormal
  infinityTranslationFieldAlgebra infinityTranslationFieldSMul infinityTranslationFieldModule
  infinityTranslationFieldAction infinityTranslationFieldActionSMul infinityTranslationFieldBaseComm
  infinityTranslationNormalizationAction infinityTranslationNormalizationSMul
  infinityTranslationRingAlgebra infinityTranslationRingSMul infinityTranslationRingModule
  infinityTranslationNormalizationGaloisGroup

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinityTranslationBaseRingTower :
    IsScalarTower S.infinityPolynomialBase S.infinityTranslationBaseRing
      (S.infinityNormalizationRing false) := IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance infinityTranslationRingBaseComm :
    SMulCommClass S.infinityTranslationGroup S.infinityPolynomialBase
      (S.infinityNormalizationRing false) where
  smul_comm g a b := Subtype.ext
    ((S.infinityTranslationFieldBaseComm).smul_comm g a
      (b : S.infinityNormalizationField false))

/-- The original quotient acts on the original unsigned infinity prime fiber. -/
@[instance_reducible] def infinityTranslationFiberAction :
    MulAction S.infinityTranslationGroup (S.infinityFiber false) := inferInstance

attribute [local instance] infinityTranslationFiberAction

@[instance_reducible] def infinityTranslationFiberSMul :
    SMul S.infinityTranslationGroup (S.infinityFiber false) :=
  S.infinityTranslationFiberAction.toSMul

attribute [local instance] infinityTranslationFiberSMul

/-- The fiber action is the ideal action induced by the same normalization automorphisms. -/
theorem coe_infinityTranslationFiberAction (g : S.infinityTranslationGroup)
    (q : S.infinityFiber false) : (g • q).1 = g • q.1 := rfl

private theorem infinityTranslationFiberMap_under (q : S.infinityFiber false) :
    (S.infinityTranslationFiberMap q).1 = q.1.under S.infinityTranslationBaseRing :=
  S.infinityTranslationFiberMap_asIdeal q

/-- The actual contraction map is constant on the actual translation orbits. -/
theorem infinityTranslationFiberMap_smul (g : S.infinityTranslationGroup)
    (q : S.infinityFiber false) :
    S.infinityTranslationFiberMap (g • q) = S.infinityTranslationFiberMap q :=
  PrimeFiberOrbit.map_smul (G := S.infinityTranslationGroup)
    S.infinityBaseIdeal S.infinityTranslationFiberMap S.infinityTranslationFiberMap_under g q

/-- Two original upper primes have the same lower center exactly in one translation orbit. -/
theorem infinityTranslationFiberMap_eq_iff_orbit (q₁ q₂ : S.infinityFiber false) :
    S.infinityTranslationFiberMap q₁ = S.infinityTranslationFiberMap q₂ ↔
      ∃ g : S.infinityTranslationGroup, g • q₁ = q₂ :=
  PrimeFiberOrbit.map_eq_iff_exists_smul (G := S.infinityTranslationGroup)
    S.infinityBaseIdeal S.infinityTranslationFiberMap S.infinityTranslationFiberMap_under q₁ q₂

/-- The actual lower boundary is the orbit quotient of the existing upper boundary. -/
def infinityTranslationFiberOrbitQuotientEquiv :
    MulAction.orbitRel.Quotient S.infinityTranslationGroup (S.infinityFiber false) ≃
      S.infinityTranslationBaseFiber :=
  PrimeFiberOrbit.orbitQuotientEquiv (G := S.infinityTranslationGroup)
    S.infinityBaseIdeal S.infinityTranslationFiberMap S.infinityTranslationFiberMap_under
      S.infinityTranslationFiberMap_surjective

/-- The orbit equivalence retains the actual original ideal contraction map. -/
theorem infinityTranslationFiberOrbitQuotientEquiv_mk (q : S.infinityFiber false) :
    S.infinityTranslationFiberOrbitQuotientEquiv
      (Quotient.mk (MulAction.orbitRel S.infinityTranslationGroup (S.infinityFiber false)) q) =
        S.infinityTranslationFiberMap q := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
