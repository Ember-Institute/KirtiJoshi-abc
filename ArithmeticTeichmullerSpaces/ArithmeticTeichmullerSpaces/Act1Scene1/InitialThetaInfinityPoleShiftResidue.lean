import ArithmeticTeichmullerSpaces.Compatibility.Transcendental
import ArithmeticTeichmullerSpaces.Act1Scene1.TwoTorsionPoleShiftResidue
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityPoleInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFinitePrimeCoordinates

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the same seed's rational two-torsion shift and original inverse-coordinate centers.
fidelity: the shifted actual generic point has x-residue equal to the original
rational shift's x-coordinate, both at each original ambient infinity valuation
and at each centered prime in the same actual finite division normal closure.
No independent point, valuation lift, or residue certificate is an input.
boundary: does not prove shifted division-point residues rational, full upper
residue field equal to the coefficient field, or cusp/theta-root identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve IsDedekindDomain
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance poleShiftClosureRing_coefficientAlgebra :
    Algebra ↥S.prime.torsionField
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure) :=
  (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure).algebra'

/-- The original generic point expressed over the same actual finite division closure. -/
def infinityDivisionClosureGenericPoint :
    (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Point := by
  let N := S.infinityDivisionNormalClosure
  let ι : N →ₐ[↥S.prime.torsionField] Genuine.Ω S.prime.EK := N.val.restrictScalars _
  exact Affine.Point.some
    ⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩
    ⟨Genuine.yG S.prime.EK, S.infinityDivisionNormalClosure_yG_mem⟩
    ((Affine.baseChange_nonsingular (W := S.prime.EK) (f := ι)
      Subtype.val_injective _ _).mp (Genuine.nonsingular_generic S.prime.EK))

/-- Its x-coordinate retains the original actual ambient value. -/
theorem infinityDivisionClosureGenericPoint_ptX :
    ptX S.infinityDivisionClosureGenericPoint =
      (⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩ :
        S.infinityDivisionNormalClosure) := rfl

/-- At the original ambient boundary valuation, the pole shift reduces to its rational x-coordinate. -/
theorem infinityAmbientValuation_shifted_generic_x_sub_lt_one
    (pm : Bool) (q : S.infinityFiber pm) :
    (S.infinityAmbientValuation pm q).valuation
      (ptX (Affine.Point.add
          (W := (S.prime.EK⁄(Genuine.Ω S.prime.EK)).toAffine)
          (Genuine.genericPoint S.prime.EK)
          (pointMap S.prime.EK
            (algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK))
            S.infinityTwoTorsionShift)) -
        algebraMap ↥S.prime.torsionField (Genuine.Ω S.prime.EK)
          (ptX S.infinityTwoTorsionShift)) < 1 :=
  TwoTorsionPoleShiftResidue.ptX_add_pointMap_sub_lt_one S.prime.EK
    (S.infinityAmbientValuation pm q) (S.infinityAmbientValuation_constant_mem pm q)
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul (Genuine.genericPoint S.prime.EK)
    (S.infinityAmbientValuation_xG_not_mem pm q)

/-- The same exact pole-limit residue at an actual finite closure prime, without any inertia assumption. -/
theorem infinityDivisionClosurePrime_shifted_generic_x_sub_lt_one
    (p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal) :
    (NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p).valuation
      (ptX (Affine.Point.add
          (W := (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine)
          S.infinityDivisionClosureGenericPoint
          (pointMap S.prime.EK
            (algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure)
            S.infinityTwoTorsionShift)) -
        algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure
          (ptX S.infinityTwoTorsionShift)) < 1 := by
  let N := S.infinityDivisionNormalClosure
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : ↥S.prime.torsionField) : algebraMap ↥S.prime.torsionField N c ∈ W :=
    NormalizationPrimeValuation.coordinate_mem p
      (algebraMap ↥S.prime.torsionField (coordRing (Genuine.xG S.prime.EK)⁻¹ N) c)
  have hinv : algebraMap (coordRing (Genuine.xG S.prime.EK)⁻¹ N) N
      (algebraMap (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
        (coordRing (Genuine.xG S.prime.EK)⁻¹ N)
        (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹)) =
      (⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩ : N)⁻¹ := by
    apply Subtype.ext
    rfl
  have hx0 : (⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩ : N) ≠ 0 := by
    intro h
    exact (JoshiTeich.Compatibility.transcendental_ne_zero (Genuine.transcendental_xG S.prime.EK))
      (congrArg (fun a : N => (a : Genuine.Ω S.prime.EK)) h)
  have hx : ptX S.infinityDivisionClosureGenericPoint ∉ W := by
    rw [S.infinityDivisionClosureGenericPoint_ptX]
    exact FiniteInversePrimePoleInertia.not_mem_primeSubring_of_inverse_center
      (Genuine.xG S.prime.EK)⁻¹ S.infinityTranslation_inverseCoordinate_transcendental
      N p _ hx0 hinv hp
  exact TwoTorsionPoleShiftResidue.ptX_add_pointMap_sub_lt_one
    S.prime.EK W hk S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint hx

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
