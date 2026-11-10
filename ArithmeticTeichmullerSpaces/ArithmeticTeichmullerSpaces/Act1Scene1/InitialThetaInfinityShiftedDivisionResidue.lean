import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedDivisionFiberEquation
import ArithmeticTeichmullerSpaces.Act1Scene1.ValuationFiberSpecialization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing original shifted division coordinates and original target bound.
fidelity: names the actual finite prime valuation, its residue field, and the
residues of both ORIGINAL shifted Qpt coordinates. The original x residue is
a root of the exact completed-square fibre over the original rational shift.
The coefficient map restricts the original constants to the valuation ring
and then applies its canonical residue map.
No new point, prime, valuation, or residue certificate is supplied.
boundary: does not prove either coordinate residue rational over the original
coefficient field, upper residue degree one, or a cusp/theta-root identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve IsDedekindDomain
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization IntegralDivisionCoordinates
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 2000] Classical.propDecidable
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityDivisionNormalClosure_field infinityDivisionNormalClosure_rationalAlgebra
  infinityDivisionNormalClosure_baseAlgebra infinityDivisionNormalClosure_baseSMul
  infinityDivisionNormalClosure_baseModule infinityDivisionNormalClosure_coefficientAlgebra
  infinityDivisionNormalClosure_coefficientSMul infinityDivisionNormalClosure_coefficientModule
  infinityDivisionNormalClosure_coefficientBaseTower infinityDivisionNormalClosure_baseTower
  infinityDivisionClosure_separable infinityDivisionClosureRing_baseAlgebra
  infinityDivisionClosureRing_dedekind infinityDivisionClosureRing_fraction
  poleShiftClosureRing_coefficientAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)
variable (p : HeightOneSpectrum
  (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))

/-- The original valuation at this original finite closure prime. -/
abbrev infinityDivisionClosurePrimeValuation :
    ValuationSubring S.infinityDivisionNormalClosure :=
  NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p

/-- The original coefficient field lies in the named actual valuation ring. -/
theorem infinityDivisionClosurePrimeValuation_coefficients_mem
    (c : ↥S.prime.torsionField) :
    algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure c ∈
      S.infinityDivisionClosurePrimeValuation p :=
  NormalizationPrimeValuation.coordinate_mem p
    (algebraMap ↥S.prime.torsionField
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure) c)

local instance shiftedDivisionResidue_primeCommRing :
    CommRing (S.infinityDivisionClosurePrimeValuation p) :=
  (S.infinityDivisionClosurePrimeValuation p).toSubring.toCommRing

local instance shiftedDivisionResidue_primeLocalRing :
    IsLocalRing (S.infinityDivisionClosurePrimeValuation p) :=
  ValuationSubring.isLocalRing _

/-- The actual residue field of the original finite closure prime valuation. -/
abbrev infinityDivisionClosurePrimeResidueField :=
  ValuationResidueCoefficients.residueField (S.infinityDivisionClosurePrimeValuation p)

local instance shiftedDivisionResidue_field :
    Field (S.infinityDivisionClosurePrimeResidueField p) :=
  IsLocalRing.ResidueField.field (S.infinityDivisionClosurePrimeValuation p)

/-- The coefficient algebra induced through the original valuation ring. -/
@[instance_reducible]
def infinityDivisionClosurePrimeResidue_coefficientAlgebra :
    Algebra ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) :=
  ValuationResidueCoefficients.coefficientAlgebra
    (S.infinityDivisionClosurePrimeValuation p)
    (S.infinityDivisionClosurePrimeValuation_coefficients_mem p)

attribute [local instance] infinityDivisionClosurePrimeResidue_coefficientAlgebra

local instance shiftedDivisionResidue_coefficientSMul :
    SMul ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) :=
  (S.infinityDivisionClosurePrimeResidue_coefficientAlgebra p).toSMul

local instance shiftedDivisionResidue_coefficientModule :
    Module ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) :=
  (S.infinityDivisionClosurePrimeResidue_coefficientAlgebra p).toModule

variable (hp : algebraMap
  (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
  (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
  (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)

/-- The residue of the ORIGINAL shifted Qpt x coordinate at the SAME prime. -/
def infinityDivisionClosurePrime_shifted_Qpt_residueX :
    S.infinityDivisionClosurePrimeResidueField p :=
  IsLocalRing.residue (S.infinityDivisionClosurePrimeValuation p)
    ⟨ptX S.infinityDivisionClosureShiftedQpt,
      (S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp).1⟩

/-- The residue of the ORIGINAL shifted Qpt y coordinate at the SAME prime. -/
def infinityDivisionClosurePrime_shifted_Qpt_residueY :
    S.infinityDivisionClosurePrimeResidueField p :=
  IsLocalRing.residue (S.infinityDivisionClosurePrimeValuation p)
    ⟨ptY S.infinityDivisionClosureShiftedQpt,
      (S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp).2⟩

include hp

/-- The original target has integral x at the same centered finite prime. -/
theorem infinityDivisionClosurePrime_shifted_generic_x_mem :
    ptX S.infinityDivisionClosureShiftedGenericPoint ∈
      S.infinityDivisionClosurePrimeValuation p :=
  IntegralDivisionFiberData.rational_shift_x_mem S.prime.EK
    (S.infinityDivisionClosurePrimeValuation p)
    (S.infinityDivisionClosurePrimeValuation_coefficients_mem p)
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
    (S.closurePrime_generic_x_not_mem p hp)

/-- Actual specialization: the ORIGINAL x residue satisfies the exact fibre
over the ORIGINAL rational two-torsion shift x coordinate. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_residueX_isRoot :
    (JoshiTeich.ReferenceIut.Torsion.fibrePoly
      (((shortModel S.prime.EK)⁄(S.infinityDivisionClosurePrimeResidueField p)).toAffine)
      S.prime.ℓ
      (algebraMap ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p)
        (ptX S.infinityTwoTorsionShift))).IsRoot
      (S.infinityDivisionClosurePrime_shifted_Qpt_residueX p hp) := by
  exact ValuationFiberSpecialization.short_fibre_isRoot S.prime.EK
    (S.infinityDivisionClosurePrimeValuation p)
    (S.infinityDivisionClosurePrimeValuation_coefficients_mem p)
    S.prime.ℓ (ptX S.infinityTwoTorsionShift)
    (S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp).1
    (S.infinityDivisionClosurePrime_shifted_generic_x_mem p hp)
    (S.infinityDivisionClosurePrime_shifted_Qpt_short_fibre_equation p hp)
    (S.infinityDivisionClosurePrime_shifted_generic_x_sub_lt_one p hp)

/-- The same original shifted x and y residues satisfy the original reduced model. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_residue_equation :
    (S.prime.EK⁄(S.infinityDivisionClosurePrimeResidueField p)).toAffine.Equation
      (S.infinityDivisionClosurePrime_shifted_Qpt_residueX p hp)
      (S.infinityDivisionClosurePrime_shifted_Qpt_residueY p hp) := by
  exact ValuationFiberSpecialization.equation_residue S.prime.EK
    (S.infinityDivisionClosurePrimeValuation p)
    (S.infinityDivisionClosurePrimeValuation_coefficients_mem p)
    (S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp).1
    (S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp).2
    (ShiftedDivisionCoordinatesIntegral.nonsingular_ptX_ptY
      S.prime.EK S.infinityDivisionClosureShiftedQpt
      (S.infinityDivisionClosurePrime_shifted_Qpt_ne_zero p hp)).1

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
