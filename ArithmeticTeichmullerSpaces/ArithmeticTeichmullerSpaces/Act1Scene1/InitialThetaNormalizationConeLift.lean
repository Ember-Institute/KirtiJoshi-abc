import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationCone

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZATION-CONE-LIFT
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
integral closure inside the actual unsigned covering fraction field.
fidelity: every compatible presentation cone admits an injective coordinate
map from the actual unsigned normalization, preserving both original legs.
Original proofs; no reference implementation copied.
boundary: coordinate-ring lifting; the Cover law is proved separately.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverTensorBaseAlgebra coverTensorBaseSMul coverTensorBaseModule
  baseTensorBaseAlgebra baseTensorBaseSMul baseTensorBaseModule normalizationTensorCommRing
  tensorRingBaseAlgebra normalizationTensorBase_xLineSMul normalizationFieldTensorBaseAlgebra
  presentationCoefficientAlgebra basePresentationCoefficientAlgebra
  coneCoverMulAction coneBaseMulAction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

private theorem normalizationConeLift_overBase_exists
    (D : AffineOrbicurvePresentation ↥S.prime.torsionField)
    (a : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation true))
    (b : AffineOrbicurvePresentation.Cover D (S.baseOrbicurvePresentation false))
    (h : a.f.comp (S.baseToCoverNormalizationRingMap true) =
      b.f.comp S.signedBaseNormalizationRingMap) :
    letI := normalizationConeBaseAlgebra S D a
    ∃ j : S.coverNormalizationRing false →ₐ[S.normalizationTensorBase] D.A,
      Function.Injective j ∧
        j.toRingHom.comp S.normalizationTensorMap.toRingHom =
          (normalizationConeTensorMap S D a b h).toRingHom := by
  letI : Algebra S.normalizationTensorBase D.A := normalizationConeBaseAlgebra S D a
  let A := S.normalizationTensorBase
  let R := S.coverNormalizationRing true
  let T := S.normalizationTensorRing
  let B := S.coverNormalizationRing false
  let N := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : Algebra A (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M true) :=
    IntermediateField.algebra' _
  letI : SMul A N := S.normalizationFieldTensorBaseAlgebra.toSMul
  letI : Algebra T B := S.normalizationTensorMap.toRingHom.toAlgebra
  letI : Algebra T N := S.normalizationTensorFieldAlgebra
  have : IsScalarTower A T N := IsScalarTower.of_algebraMap_eq fun x =>
    (S.normalizationTensorFieldMap.commutes x).symm
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower T B N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing T N := S.normalizationTensor_fractionField
  have : Algebra.IsIntegral A R := ⟨integralClosure.isIntegral⟩
  have : Algebra.IsIntegral A B := ⟨integralClosure.isIntegral⟩
  have : Algebra.IsIntegral A D.A := by
    have hA : (algebraMap A R).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
    have hD := RingHom.IsIntegral.trans (algebraMap A R) a.f.toRingHom hA a.isIntegral
    exact ⟨hD⟩
  exact integral_normalization_lift_exists
    (A := A) (T := T) (B := B) (N := N) (D := D.A) Subtype.val_injective
    (normalizationConeTensorMap S D a b h) (normalizationConeTensorMap_injective S D a b h)

theorem normalizationConeLift_exists
    (D : AffineOrbicurvePresentation ↥S.prime.torsionField)
    (a : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation true))
    (b : AffineOrbicurvePresentation.Cover D (S.baseOrbicurvePresentation false))
    (h : a.f.comp (S.baseToCoverNormalizationRingMap true) =
      b.f.comp S.signedBaseNormalizationRingMap) :
    ∃ j : S.coverNormalizationRing false →ₐ[↥S.prime.torsionField] D.A,
      Function.Injective j ∧ j.comp S.signedCoverNormalizationRingMap = a.f ∧
        j.comp (S.baseToCoverNormalizationRingMap false) = b.f := by
  let R := S.coverNormalizationRing true
  let B := S.coverNormalizationRing false
  letI := normalizationConeBaseAlgebra S D a
  have hlift := normalizationConeLift_overBase_exists S D a b h
  obtain ⟨j, hj, hT⟩ := hlift
  have hl (r : S.coverNormalizationRing true) : j (S.signedCoverNormalizationRingMap r) = a.f r := by
    have hx := RingHom.congr_fun S.normalizationTensorMap_comp_left r
    exact (congrArg j hx).symm.trans
      ((RingHom.congr_fun hT (S.normalizationTensorLeftRingMap r)).trans
        ((normalizationConeTensorMap_tmul S D a b h r 1).trans
          ((congrArg (fun x : D.A => a.f r * x) (map_one b.f)).trans (mul_one _))))
  have hr (z : S.baseNormalizationRing false) : j (S.baseToCoverNormalizationRingMap false z) = b.f z := by
    have hx := RingHom.congr_fun S.normalizationTensorMap_comp_right z
    exact (congrArg j hx).symm.trans
      ((RingHom.congr_fun hT (S.normalizationTensorRightRingMap z)).trans
        ((normalizationConeTensorMap_tmul S D a b h 1 z).trans
          ((congrArg (fun x : D.A => x * b.f z) (map_one a.f)).trans (one_mul _))))
  let jκ : B →ₐ[↥S.prime.torsionField] D.A := {
    j.toRingHom with
    commutes' := fun c => by
      calc
        j (algebraMap ↥S.prime.torsionField B c) =
            j (S.signedCoverNormalizationRingMap (algebraMap ↥S.prime.torsionField R c)) :=
          congrArg j (S.signedCoverNormalizationRingMap.commutes c).symm
        _ = a.f (algebraMap ↥S.prime.torsionField R c) := hl _
        _ = algebraMap ↥S.prime.torsionField D.A c := a.f.commutes c
  }
  exact ⟨jκ, hj, AlgHom.ext hl, AlgHom.ext hr⟩

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
