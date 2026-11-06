import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationConeLift
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationFactor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-ORBICURVE-PRESENTATION-CARTESIAN
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
normalization lifting and ramification in the actual covering square.
fidelity: the original signed/unsigned normalization square is a pullback
in the existing category of affine orbicurve presentations. Every compatible
cone has a unique lifted Cover, including its closed-point ramification law.
Original proofs; no reference implementation copied.
boundary: this presentation-category universal property does not identify
root stacks or arbitrary AG.Orbicurve objects, and does not supply core,
cusp, theta-root or the full geometry producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory WeierstrassCurve
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

set_option maxHeartbeats 1000000 in
private theorem normalizationCone_tensor_map_eq_of_legs
    (D : AffineOrbicurvePresentation ↥S.prime.torsionField)
    (c c' : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation false))
    (hl : c.f.comp S.signedCoverNormalizationRingMap =
      c'.f.comp S.signedCoverNormalizationRingMap)
    (hr : c.f.comp (S.baseToCoverNormalizationRingMap false) =
      c'.f.comp (S.baseToCoverNormalizationRingMap false)) :
    c.f.toRingHom.comp S.normalizationTensorMap.toRingHom =
      c'.f.toRingHom.comp S.normalizationTensorMap.toRingHom := by
  apply RingHom.ext
  intro x
  change c.f (S.normalizationTensorMap x) = c'.f (S.normalizationTensorMap x)
  induction x using TensorProduct.induction_on with
  | zero =>
    calc
      c.f (S.normalizationTensorMap 0) = c.f 0 := congrArg c.f (map_zero _)
      _ = 0 := map_zero _
      _ = c'.f 0 := (map_zero _).symm
      _ = c'.f (S.normalizationTensorMap 0) := congrArg c'.f (map_zero _).symm
  | add x y hx hy =>
    calc
      c.f (S.normalizationTensorMap (x + y)) =
          c.f (S.normalizationTensorMap x + S.normalizationTensorMap y) :=
        congrArg c.f (map_add S.normalizationTensorMap x y)
      _ = c.f (S.normalizationTensorMap x) + c.f (S.normalizationTensorMap y) := map_add _ _ _
      _ = c'.f (S.normalizationTensorMap x) + c'.f (S.normalizationTensorMap y) :=
        congrArg₂ (· + ·) hx hy
      _ = c'.f (S.normalizationTensorMap x + S.normalizationTensorMap y) :=
        (map_add c'.f _ _).symm
      _ = c'.f (S.normalizationTensorMap (x + y)) :=
        congrArg c'.f (map_add S.normalizationTensorMap x y).symm
  | tmul r z =>
    calc
      c.f (S.normalizationTensorMap (r ⊗ₜ z)) =
          c.f (S.signedCoverNormalizationRingMap r *
            S.baseToCoverNormalizationRingMap false z) :=
        congrArg c.f (S.normalizationTensorMap_tmul r z)
      _ = c.f (S.signedCoverNormalizationRingMap r) *
            c.f (S.baseToCoverNormalizationRingMap false z) := map_mul _ _ _
      _ = c'.f (S.signedCoverNormalizationRingMap r) *
            c'.f (S.baseToCoverNormalizationRingMap false z) :=
        congrArg₂ (· * ·) (AlgHom.congr_fun hl r) (AlgHom.congr_fun hr z)
      _ = c'.f (S.signedCoverNormalizationRingMap r *
            S.baseToCoverNormalizationRingMap false z) := (map_mul _ _ _).symm
      _ = c'.f (S.normalizationTensorMap (r ⊗ₜ z)) :=
        congrArg c'.f (S.normalizationTensorMap_tmul r z).symm

set_option maxHeartbeats 1000000 in
private theorem normalizationCone_fraction_unique
    (D : AffineOrbicurvePresentation ↥S.prime.torsionField)
    (c c' : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation false))
    (hT : c.f.toRingHom.comp S.normalizationTensorMap.toRingHom =
      c'.f.toRingHom.comp S.normalizationTensorMap.toRingHom) : c.f = c'.f := by
  let T := S.normalizationTensorRing
  let B := (S.coverOrbicurvePresentation false).A
  let N := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : Algebra T B := S.normalizationTensorMap.toRingHom.toAlgebra
  letI : Algebra T N := S.normalizationTensorFieldAlgebra
  letI : Algebra B N := FunctionFieldNormalization.ringMapFieldAlgebra (le_refl N)
  letI : IsScalarTower T B N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsFractionRing T N := S.normalizationTensor_fractionField
  letI : IsFractionRing B N :=
    FunctionFieldNormalization.fractionFieldRing
      (t := Genuine.xG S.prime.EK) (L := N)
  apply AlgHom.ext
  have hc := fraction_intermediate_ringHom_ext (T := T) (N := N)
    (j := c.f.toRingHom) (j' := c'.f.toRingHom) c.injective c'.injective hT
  exact fun x => congrArg (fun f => f x) hc

theorem normalizationOrbicurvePresentation_isPullback :
    IsPullback (C := AffineOrbicurvePresentation ↥S.prime.torsionField)
      (P := S.coverOrbicurvePresentation false) (X := S.coverOrbicurvePresentation true)
      (Y := S.baseOrbicurvePresentation false) (Z := S.baseOrbicurvePresentation true)
      S.signedCoverOrbicurvePresentation (S.normalizationOrbicurvePresentationCover false)
      (S.normalizationOrbicurvePresentationCover true) S.signedBaseOrbicurvePresentation := by
  apply IsPullback.mk'
  · exact S.normalizationPresentation_coverSquare.symm
  · intro D c c' h h'
    have hl : c.f.comp S.signedCoverNormalizationRingMap =
        c'.f.comp S.signedCoverNormalizationRingMap :=
      congrArg (fun q : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation true) => q.f) h
    have hr : c.f.comp (S.baseToCoverNormalizationRingMap false) =
        c'.f.comp (S.baseToCoverNormalizationRingMap false) :=
      congrArg (fun q : AffineOrbicurvePresentation.Cover D (S.baseOrbicurvePresentation false) => q.f) h'
    have hT := normalizationCone_tensor_map_eq_of_legs S D c c' hl hr
    apply AffineOrbicurvePresentation.Cover.ext_f
    exact normalizationCone_fraction_unique S D c c' hT
  · intro D a b h
    have hring : a.f.comp (S.baseToCoverNormalizationRingMap true) =
        b.f.comp S.signedBaseNormalizationRingMap :=
      congrArg (fun q : AffineOrbicurvePresentation.Cover D (S.baseOrbicurvePresentation true) => q.f) h
    obtain ⟨j, hj, hl, hr⟩ := S.normalizationConeLift_exists D a b hring
    let l := AffineOrbicurvePresentation.Cover.factorThroughUnramified
      (S.normalizationOrbicurvePresentationCover false) b j hj hr
      (fun _ => rfl) (fun _ => rfl)
      (fun q hq => S.unsignedCoverNormalization_ramificationIdx_one q hq)
    refine ⟨l, ?_, ?_⟩
    · exact AffineOrbicurvePresentation.Cover.ext_f hl
    · exact AffineOrbicurvePresentation.Cover.ext_f hr

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
