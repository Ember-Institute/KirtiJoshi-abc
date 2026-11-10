import ArithmeticTeichmullerSpaces.Act1Scene1.ShortDivisionFiberEquation
import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionFiberData
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedDivisionIntegral

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the same original Qpt, same division normal closure, and same rational shift.
fidelity: the original shifted division point has integral coordinates and
satisfies the exact completed-square multiplication-fibre polynomial. Its
target is the original shifted generic point, whose strict residue bound is
already proved at the same centered finite prime. No independent point,
valuation, rationality certificate, or residue-field equality is an input.
Original composition of existing project theorems; no reference code copied.
boundary: this prepares specialization. It does not perform specialization,
prove coordinate residues rational, identify the upper residue field, or
construct the cusp/theta-root identity.
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

/-- The original generic point shifted by the same original rational two-torsion point. -/
def infinityDivisionClosureShiftedGenericPoint :
    (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Point :=
  Affine.Point.add (W := (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine)
    S.infinityDivisionClosureGenericPoint (pointMap S.prime.EK
      (algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure)
      S.infinityTwoTorsionShift)

private theorem fiberEquation_ell_odd : Odd S.prime.ℓ :=
  S.prime.ℓ_prime.odd_of_ne_two (Nat.ne_of_gt
    ((Nat.lt_succ_self 2).trans_le
      ((Nat.le_succ 3).trans ((Nat.le_succ 4).trans S.prime.five_le))))

/-- The exact multiplication relation between the two original shifted points. -/
theorem infinityDivisionClosureShiftedQpt_nsmul :
    S.prime.ℓ • S.infinityDivisionClosureShiftedQpt =
      S.infinityDivisionClosureShiftedGenericPoint :=
  ShortDivisionFiberEquation.shifted_nsmul S.prime.EK S.prime.ℓ
    S.fiberEquation_ell_odd S.infinityTwoTorsionShift
    S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
    S.infinityDivisionClosureQpt S.infinityDivisionClosureQpt_nsmul

variable
    (p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)

include hp

/-- The exact completed-square fibre equation at each original centered finite prime. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_short_fibre_equation :
    (((shortModel S.prime.EK)⁄S.infinityDivisionNormalClosure).Φ S.prime.ℓ).eval
        (ptX S.infinityDivisionClosureShiftedQpt) -
      ptX S.infinityDivisionClosureShiftedGenericPoint *
        (((shortModel S.prime.EK)⁄S.infinityDivisionNormalClosure).ΨSq S.prime.ℓ).eval
          (ptX S.infinityDivisionClosureShiftedQpt) = 0 := by
  let N := S.infinityDivisionNormalClosure
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : ↥S.prime.torsionField) : algebraMap ↥S.prime.torsionField N c ∈ W :=
    NormalizationPrimeValuation.coordinate_mem p
      (algebraMap ↥S.prime.torsionField (coordRing (Genuine.xG S.prime.EK)⁻¹ N) c)
  have hTarget : S.infinityDivisionClosureShiftedGenericPoint ≠ 0 :=
    IntegralDivisionFiberData.rational_shift_ne_zero S.prime.EK W hk
      S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
      S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
      (S.closurePrime_generic_x_not_mem p hp)
  exact ShortDivisionFiberEquation.short_division_fibre_equation
    S.prime.EK S.prime.ℓ S.infinityDivisionClosureShiftedGenericPoint
    S.infinityDivisionClosureShiftedQpt hTarget S.infinityDivisionClosureShiftedQpt_nsmul

/-- Actual affine integral coordinates, exact fibre equation, and the original
target pole-limit bound, all at the SAME finite prime. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_integral_fibre_data :
    ∃ (x y : S.infinityDivisionNormalClosure)
        (h : (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Nonsingular x y),
      S.infinityDivisionClosureShiftedQpt = Affine.Point.some x y h ∧
      x ∈ NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p ∧
      y ∈ NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p ∧
      ptX S.infinityDivisionClosureShiftedGenericPoint ∈
        NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p ∧
      (((shortModel S.prime.EK)⁄S.infinityDivisionNormalClosure).Φ S.prime.ℓ).eval x -
        ptX S.infinityDivisionClosureShiftedGenericPoint *
          (((shortModel S.prime.EK)⁄S.infinityDivisionNormalClosure).ΨSq S.prime.ℓ).eval x = 0 ∧
      (NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p).valuation
        (ptX S.infinityDivisionClosureShiftedGenericPoint -
          algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure
            (ptX S.infinityTwoTorsionShift)) < 1 := by
  let N := S.infinityDivisionNormalClosure
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : ↥S.prime.torsionField) : algebraMap ↥S.prime.torsionField N c ∈ W :=
    NormalizationPrimeValuation.coordinate_mem p
      (algebraMap ↥S.prime.torsionField (coordRing (Genuine.xG S.prime.EK)⁻¹ N) c)
  have hxTarget : ptX S.infinityDivisionClosureShiftedGenericPoint ∈ W :=
    IntegralDivisionFiberData.rational_shift_x_mem S.prime.EK W hk
      S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
      S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
      (S.closurePrime_generic_x_not_mem p hp)
  exact IntegralDivisionFiberData.of_coordinates S.prime.EK W S.prime.ℓ
    S.infinityDivisionClosureShiftedGenericPoint S.infinityDivisionClosureShiftedQpt
    (algebraMap ↥S.prime.torsionField N (ptX S.infinityTwoTorsionShift))
    (S.infinityDivisionClosurePrime_shifted_Qpt_affine_integral p hp) hxTarget
    (S.infinityDivisionClosurePrime_shifted_Qpt_short_fibre_equation p hp)
    (S.infinityDivisionClosurePrime_shifted_generic_x_sub_lt_one p hp)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
