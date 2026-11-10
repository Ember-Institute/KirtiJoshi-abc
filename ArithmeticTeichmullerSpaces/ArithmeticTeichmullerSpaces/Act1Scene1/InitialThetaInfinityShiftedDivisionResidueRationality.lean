import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedDivisionResidue
import ArithmeticTeichmullerSpaces.Act1Scene1.OriginalShiftedFiberResidueRationality

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the same seed's full torsion and its original rational two-torsion shift.
fidelity: BOTH residues of the ORIGINAL shifted Qpt at the SAME actual finite
closure prime are images of original coefficient-field elements. The reduced
equation and exact completed-square fibre root come from the original residues.
No new point, prime, valuation, cardinality, or residue certificate is supplied.
boundary: this does not identify the upper normalization residue field, prove
relative residue degree one, or establish a cusp/theta-root identity.
Original composition of existing project theorems; no reference code copied.
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

local instance shiftedDivisionRationality_primeCommRing :
    CommRing (S.infinityDivisionClosurePrimeValuation p) :=
  (S.infinityDivisionClosurePrimeValuation p).toSubring.toCommRing

local instance shiftedDivisionRationality_primeLocalRing :
    IsLocalRing (S.infinityDivisionClosurePrimeValuation p) :=
  ValuationSubring.isLocalRing _

local instance shiftedDivisionRationality_field :
    Field (S.infinityDivisionClosurePrimeResidueField p) :=
  IsLocalRing.ResidueField.field (S.infinityDivisionClosurePrimeValuation p)

attribute [local instance] infinityDivisionClosurePrimeResidue_coefficientAlgebra

local instance shiftedDivisionRationality_coefficientSMul :
    SMul ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) :=
  (S.infinityDivisionClosurePrimeResidue_coefficientAlgebra p).toSMul

local instance shiftedDivisionRationality_coefficientModule :
    Module ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) :=
  (S.infinityDivisionClosurePrimeResidue_coefficientAlgebra p).toModule

variable (hp : algebraMap
  (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
  (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
  (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)

/-- Both ORIGINAL shifted coordinate residues at the SAME prime are constants. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_residue_coordinates_rational :
    ∃ a b : ↥S.prime.torsionField,
      algebraMap ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) a =
        S.infinityDivisionClosurePrime_shifted_Qpt_residueX p hp ∧
      algebraMap ↥S.prime.torsionField (S.infinityDivisionClosurePrimeResidueField p) b =
        S.infinityDivisionClosurePrime_shifted_Qpt_residueY p hp := by
  exact OriginalShiftedFiberResidueRationality.coordinates_rational
    S.prime.EK (S.infinityDivisionClosurePrimeResidueField p)
    S.prime.ℓ S.prime.ℓ_prime.ne_zero
    (S.prime.ℓ_prime.odd_of_ne_two (Nat.ne_of_gt
      ((Nat.lt_succ_self 2).trans_le
        ((Nat.le_succ 3).trans ((Nat.le_succ 4).trans S.prime.five_le)))))
    S.prime.card_TK S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul
    (S.infinityDivisionClosurePrime_shifted_Qpt_residue_equation p hp)
    (S.infinityDivisionClosurePrime_shifted_Qpt_residueX_isRoot p hp)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
