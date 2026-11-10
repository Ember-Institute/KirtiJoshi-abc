import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineShiftedDivisionPointTranscendence
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityShiftedDivisionIntegral

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the seed's original division point and its same rational two-torsion shift.
fidelity: the shifted point in the SAME finite normal closure maps to the
original selected Qpt plus the original constant shift in the original ambient
closure. Its x coordinate is transcendental over the original coefficient
field. No prime or independent point is supplied by the caller.
Original composition of existing project theorems; no reference code copied.
boundary: coordinate-field generation and normalization residue identification
remain separate consumers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance shiftedDivisionClosureTranscendence_decidableEq :
    DecidableEq (Genuine.Ω S.prime.EK) :=
  Genuine.shiftedDivisionTranscendence_decidableEq S.prime.EK

/-- The original finite-closure shifted point retains the same ambient selected point and shift. -/
theorem infinityDivisionClosureShiftedQpt_map :
    Affine.Point.map (W' := S.prime.EK) (S := ↥S.prime.torsionField)
      (S.infinityDivisionNormalClosure.val.restrictScalars ↥S.prime.torsionField)
      S.infinityDivisionClosureShiftedQpt =
        Affine.Point.add (W := (S.prime.EK⁄(Genuine.Ω S.prime.EK)).toAffine)
          (Genuine.Qpt S.prime.EK S.prime.ℓ)
          (Genuine.base S.prime.EK S.infinityTwoTorsionShift) := by
  let ι : S.infinityDivisionNormalClosure →ₐ[↥S.prime.torsionField]
      Genuine.Ω S.prime.EK := S.infinityDivisionNormalClosure.val.restrictScalars _
  let m := Affine.Point.map (W' := S.prime.EK) ι
  have hc : m (pointMap S.prime.EK
      (algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure)
      S.infinityTwoTorsionShift) =
      Genuine.base S.prime.EK S.infinityTwoTorsionShift := by
    change Affine.Point.map (W' := S.prime.EK) ι
      (Affine.Point.baseChange (W' := S.prime.EK.toAffine)
        ↥S.prime.torsionField S.infinityDivisionNormalClosure S.infinityTwoTorsionShift) = _
    exact Affine.Point.map_baseChange (W' := S.prime.EK.toAffine) ι S.infinityTwoTorsionShift
  exact (map_add m S.infinityDivisionClosureQpt
    (pointMap S.prime.EK
      (algebraMap ↥S.prime.torsionField S.infinityDivisionNormalClosure)
      S.infinityTwoTorsionShift)).trans
    (congrArg₂ (Affine.Point.add (W := (S.prime.EK⁄(Genuine.Ω S.prime.EK)).toAffine))
      S.infinityDivisionClosureQpt_map hc)

/-- The actual shifted x coordinate is transcendental in the same finite normal closure. -/
theorem infinityDivisionClosureShiftedQpt_x_transcendental :
    Transcendental ↥S.prime.torsionField (ptX S.infinityDivisionClosureShiftedQpt) := by
  let ι : S.infinityDivisionNormalClosure →ₐ[↥S.prime.torsionField]
      Genuine.Ω S.prime.EK := S.infinityDivisionNormalClosure.val.restrictScalars _
  have hxmap (P : (S.prime.EK⁄S.infinityDivisionNormalClosure).toAffine.Point) :
      ptX (Affine.Point.map (W' := S.prime.EK) ι P) = ι (ptX P) := by
    cases P with
    | zero => exact (map_zero ι).symm
    | some x y h => rfl
  intro hx
  apply Genuine.Qpt_add_base_x_transcendental S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.infinityTwoTorsionShift
  rw [← S.infinityDivisionClosureShiftedQpt_map, hxmap]
  exact hx.algHom ι

/-- The same shifted point is affine without a prime-dependent hypothesis. -/
theorem infinityDivisionClosureShiftedQpt_ne_zero :
    S.infinityDivisionClosureShiftedQpt ≠ 0 := by
  intro h
  apply S.infinityDivisionClosureShiftedQpt_x_transcendental.ne_zero
  rw [h]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
