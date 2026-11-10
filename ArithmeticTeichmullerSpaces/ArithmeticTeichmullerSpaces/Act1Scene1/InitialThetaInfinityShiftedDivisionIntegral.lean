import ArithmeticTeichmullerSpaces.Act1Scene1.ShiftedDivisionCoordinatesIntegral
import ArithmeticTeichmullerSpaces.Act1Scene1.ShortDivisionFiberEquation
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityPoleShiftResidue

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the original seed division point and its same rational two-torsion shift.
fidelity: descends the ORIGINAL Qpt into the SAME finite division normal closure,
proves ell times that point is the ORIGINAL generic point, then proves both
coordinates of its same seed-produced shift integral at the actual finite
inverse-center valuation. No inertia law, free division point, or free shift.
boundary: integral coordinates are not yet rational residues; no upper
normalization residue identity or cusp/theta-root identity is asserted.
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
  poleShiftClosureRing_coefficientAlgebra

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

private theorem sourceQpt_ne_zero :
    Genuine.Qpt S.prime.EK S.prime.ℓ ≠ 0 :=
  Genuine.divSys_ne_zero S.prime.EK (Genuine.effLevel S.prime.ℓ)
    (Genuine.effLevel_pos S.prime.ℓ)

/-- The original Qpt descended by its original coordinates into the same finite normal closure. -/
def infinityDivisionClosureQpt :
    (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Point := by
  let N := S.infinityDivisionNormalClosure
  let ι : N →ₐ[↥S.prime.torsionField] Genuine.Ω S.prime.EK := N.val.restrictScalars _
  have hQN : (S.prime.EK⁄N).toAffine.Nonsingular
      (⟨ptX (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1⟩ : N)
      ⟨ptY (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2⟩ :=
    (Affine.baseChange_nonsingular (W := S.prime.EK) (f := ι)
      Subtype.val_injective _ _).mp
      (ShiftedDivisionCoordinatesIntegral.nonsingular_ptX_ptY
        S.prime.EK (Genuine.Qpt S.prime.EK S.prime.ℓ) S.sourceQpt_ne_zero)
  exact Affine.Point.some _ _ hQN

/-- The descended point maps back to the original Qpt, not an independent division point. -/
theorem infinityDivisionClosureQpt_map :
    Affine.Point.map (W' := S.prime.EK) (S := ↥S.prime.torsionField)
      (S.infinityDivisionNormalClosure.val.restrictScalars ↥S.prime.torsionField)
      S.infinityDivisionClosureQpt = Genuine.Qpt S.prime.EK S.prime.ℓ := by
  change Affine.Point.some (ptX (Genuine.Qpt S.prime.EK S.prime.ℓ))
    (ptY (Genuine.Qpt S.prime.EK S.prime.ℓ)) _ =
    Genuine.Qpt S.prime.EK S.prime.ℓ
  exact ShiftedDivisionCoordinatesIntegral.some_ptX_ptY
    S.prime.EK (Genuine.Qpt S.prime.EK S.prime.ℓ) S.sourceQpt_ne_zero

/-- The named generic point retains the original ambient generic point. -/
theorem infinityDivisionClosureGenericPoint_map :
    Affine.Point.map (W' := S.prime.EK) (S := ↥S.prime.torsionField)
      (S.infinityDivisionNormalClosure.val.restrictScalars ↥S.prime.torsionField)
      S.infinityDivisionClosureGenericPoint = Genuine.genericPoint S.prime.EK := rfl

/-- The original admissible ell multiplication equation descends to the same closure. -/
theorem infinityDivisionClosureQpt_nsmul :
    S.prime.ℓ • S.infinityDivisionClosureQpt = S.infinityDivisionClosureGenericPoint := by
  let ι : S.infinityDivisionNormalClosure →ₐ[↥S.prime.torsionField]
      Genuine.Ω S.prime.EK := S.infinityDivisionNormalClosure.val.restrictScalars _
  have heff : Genuine.effLevel S.prime.ℓ = S.prime.ℓ :=
    if_neg (Nat.ne_of_gt S.prime.ℓ_prime.pos)
  have hsource : S.prime.ℓ • Genuine.Qpt S.prime.EK S.prime.ℓ =
      Genuine.genericPoint S.prime.EK := by
    simpa only [Genuine.Qpt, heff] using
      Genuine.nsmul_divSys S.prime.EK S.prime.ℓ S.prime.ℓ_prime.pos
  exact ShortDivisionFiberEquation.nsmul_eq_of_injective_map
    (Affine.Point.map (W' := S.prime.EK) (S := ↥S.prime.torsionField) ι)
    (Affine.Point.map_injective (W' := S.prime.EK) (S := ↥S.prime.torsionField) ι)
    S.prime.ℓ S.infinityDivisionClosureQpt_map
    S.infinityDivisionClosureGenericPoint_map hsource

/-- The SAME Qpt shifted by the SAME seed-produced rational two-torsion point. -/
def infinityDivisionClosureShiftedQpt :
    (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Point :=
  Affine.Point.add (W := (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine)
    S.infinityDivisionClosureQpt
    (pointMap S.prime.EK
      (algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure)
      S.infinityTwoTorsionShift)

private theorem source_ell_odd : Odd S.prime.ℓ :=
  S.prime.ℓ_prime.odd_of_ne_two (Nat.ne_of_gt
    ((Nat.lt_succ_self 2).trans_le
      ((Nat.le_succ 3).trans ((Nat.le_succ 4).trans S.prime.five_le))))

/-- The original inverse-coordinate center makes the original generic x a pole. -/
theorem closurePrime_generic_x_not_mem
    (p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal) :
    ptX S.infinityDivisionClosureGenericPoint ∉
      NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p := by
  let N := S.infinityDivisionNormalClosure
  have hinv : algebraMap (coordRing (Genuine.xG S.prime.EK)⁻¹ N) N
      (algebraMap (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
        (coordRing (Genuine.xG S.prime.EK)⁻¹ N)
        (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹)) =
      (⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩ : N)⁻¹ := by
    apply Subtype.ext
    rfl
  have hx0 : (⟨Genuine.xG S.prime.EK, S.infinityDivisionNormalClosure_xG_mem⟩ : N) ≠ 0 := by
    intro h
    exact (Genuine.transcendental_xG S.prime.EK).ne_zero
      (congrArg (fun a : N => (a : Genuine.Ω S.prime.EK)) h)
  rw [S.infinityDivisionClosureGenericPoint_ptX]
  exact FiniteInversePrimePoleInertia.not_mem_primeSubring_of_inverse_center
    (Genuine.xG S.prime.EK)⁻¹ S.infinityTranslation_inverseCoordinate_transcendental
    N p _ hx0 hinv hp

variable
    (p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)

include hp

/-- Both coordinates of the original shifted division point lie in the actual finite prime valuation. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem :
    ptX S.infinityDivisionClosureShiftedQpt ∈
        NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p ∧
      ptY S.infinityDivisionClosureShiftedQpt ∈
        NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p := by
  let N := S.infinityDivisionNormalClosure
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : ↥S.prime.torsionField) : algebraMap ↥S.prime.torsionField N c ∈ W :=
    NormalizationPrimeValuation.coordinate_mem p
      (algebraMap ↥S.prime.torsionField (coordRing (Genuine.xG S.prime.EK)⁻¹ N) c)
  exact ShiftedDivisionCoordinatesIntegral.shifted_division_coordinates_mem
    S.prime.EK W hk S.prime.ℓ S.prime.ℓ_prime.pos S.source_ell_odd
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
    S.infinityDivisionClosureQpt (S.closurePrime_generic_x_not_mem p hp)
    S.infinityDivisionClosureQpt_nsmul

/-- The same integral shifted point is nonzero and hence represents an affine point at this chart. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_ne_zero :
    S.infinityDivisionClosureShiftedQpt ≠ 0 := by
  let N := S.infinityDivisionNormalClosure
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : ↥S.prime.torsionField) : algebraMap ↥S.prime.torsionField N c ∈ W :=
    NormalizationPrimeValuation.coordinate_mem p
      (algebraMap ↥S.prime.torsionField (coordRing (Genuine.xG S.prime.EK)⁻¹ N) c)
  exact ShiftedDivisionCoordinatesIntegral.shifted_division_ne_zero
    S.prime.EK W hk S.prime.ℓ S.source_ell_odd
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul S.infinityDivisionClosureGenericPoint
    S.infinityDivisionClosureQpt (S.closurePrime_generic_x_not_mem p hp)
    S.infinityDivisionClosureQpt_nsmul

/-- A concrete integral affine presentation of the original shifted Qpt, ready for specialization. -/
theorem infinityDivisionClosurePrime_shifted_Qpt_affine_integral :
    ∃ (x y : S.infinityDivisionNormalClosure)
        (h : (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Nonsingular x y),
      S.infinityDivisionClosureShiftedQpt = Affine.Point.some x y h ∧
      x ∈ NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p ∧
      y ∈ NormalizationPrimeValuation.primeSubring S.infinityDivisionNormalClosure p := by
  have hne := S.infinityDivisionClosurePrime_shifted_Qpt_ne_zero p hp
  have hm := S.infinityDivisionClosurePrime_shifted_Qpt_coordinates_mem p hp
  exact ⟨ptX S.infinityDivisionClosureShiftedQpt, ptY S.infinityDivisionClosureShiftedQpt,
    ShiftedDivisionCoordinatesIntegral.nonsingular_ptX_ptY
      S.prime.EK S.infinityDivisionClosureShiftedQpt hne,
    (ShiftedDivisionCoordinatesIntegral.some_ptX_ptY
      S.prime.EK S.infinityDivisionClosureShiftedQpt hne).symm, hm.1, hm.2⟩

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
