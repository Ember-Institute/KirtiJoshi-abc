import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOrbicurvePresentationSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationTensorDomain
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationPullback
import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralNormalizationLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZATION-CONE
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual tensor square and its signed base inclusion.
fidelity: compatible covers to the signed covering and unsigned base give
an injective map from the original tensor ring into the cone coordinate ring.
Original proofs; no reference implementation copied.
boundary: ordinary coordinate algebra for the existing presentation category.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverTensorBaseAlgebra coverTensorBaseSMul coverTensorBaseModule
  baseTensorBaseAlgebra baseTensorBaseSMul baseTensorBaseModule
  normalizationTensorCommRing tensorRingBaseAlgebra normalizationTensorBase_xLineSMul
  normalizationFieldTensorBaseAlgebra presentationCoefficientAlgebra basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance coneCoverMulAction (pm : Bool) :
    MulAction S.normalizationTensorBase (S.coverNormalizationRing pm) :=
  (coverTensorBaseModule S pm).toDistribMulAction.toMulAction

local instance coneBaseMulAction :
    MulAction S.normalizationTensorBase (S.baseNormalizationRing false) :=
  (baseTensorBaseModule S).toDistribMulAction.toMulAction

local instance coneSignedBaseAlgebra :
    Algebra S.normalizationTensorBase (S.baseNormalizationRing true) :=
  FunctionFieldNormalization.coordRingBaseAlgebra (Genuine.normalizationField S.prime.EK 1 ⊥ true)

def normalizationTensorBaseSignedBaseEquiv :
    S.normalizationTensorBase ≃+* S.baseNormalizationRing true :=
  RingEquiv.ofBijective (algebraMap S.normalizationTensorBase (S.baseNormalizationRing true))
    (Genuine.signedBaseNormalization_algebraMap_bijective S.prime.EK)

theorem normalizationTensorBase_to_unsignedBase (x : S.normalizationTensorBase) :
    algebraMap S.normalizationTensorBase (S.baseNormalizationRing false) x =
      S.signedBaseNormalizationRingMap (S.normalizationTensorBaseSignedBaseEquiv x) := by
  apply Subtype.ext
  rfl

theorem normalizationTensorBase_to_signedCover (x : S.normalizationTensorBase) :
    algebraMap S.normalizationTensorBase (S.coverNormalizationRing true) x =
      S.baseToCoverNormalizationRingMap true (S.normalizationTensorBaseSignedBaseEquiv x) := by
  apply Subtype.ext
  rfl

variable (D : AffineOrbicurvePresentation ↥S.prime.torsionField)
variable (a : AffineOrbicurvePresentation.Cover D (S.coverOrbicurvePresentation true))
variable (b : AffineOrbicurvePresentation.Cover D (S.baseOrbicurvePresentation false))

@[instance_reducible] def normalizationConeBaseAlgebra :
    Algebra S.normalizationTensorBase D.A :=
  (a.f.toRingHom.comp (algebraMap S.normalizationTensorBase
    (S.coverNormalizationRing true))).toAlgebra

def normalizationConeSignedMap :
    letI := normalizationConeBaseAlgebra S D a
    S.coverNormalizationRing true →ₐ[S.normalizationTensorBase] D.A := by
  letI := normalizationConeBaseAlgebra S D a
  exact { a.f.toRingHom with commutes' := fun _ => rfl }

variable (h : a.f.comp (S.baseToCoverNormalizationRingMap true) =
  b.f.comp S.signedBaseNormalizationRingMap)
include h

theorem normalizationConeBase_compat (x : S.normalizationTensorBase) :
    letI := normalizationConeBaseAlgebra S D a
    b.f (algebraMap S.normalizationTensorBase (S.baseNormalizationRing false) x) =
      algebraMap S.normalizationTensorBase D.A x := by
  letI := normalizationConeBaseAlgebra S D a
  change b.f (algebraMap S.normalizationTensorBase (S.baseNormalizationRing false) x) =
    a.f (algebraMap S.normalizationTensorBase (S.coverNormalizationRing true) x)
  exact (congrArg b.f (S.normalizationTensorBase_to_unsignedBase x)).trans
    ((AlgHom.congr_fun h (S.normalizationTensorBaseSignedBaseEquiv x)).symm.trans
      (congrArg a.f (S.normalizationTensorBase_to_signedCover x)).symm)

def normalizationConeUnsignedMap :
    letI := normalizationConeBaseAlgebra S D a
    S.baseNormalizationRing false →ₐ[S.normalizationTensorBase] D.A := by
  letI := normalizationConeBaseAlgebra S D a
  exact { b.f.toRingHom with commutes' := normalizationConeBase_compat S D a b h }

def normalizationConeTensorMap :
    letI := normalizationConeBaseAlgebra S D a
    S.normalizationTensorRing →ₐ[S.normalizationTensorBase] D.A := by
  letI := normalizationConeBaseAlgebra S D a
  exact Algebra.TensorProduct.lift (normalizationConeSignedMap S D a)
    (normalizationConeUnsignedMap S D a b h) (fun _ _ => Commute.all _ _)

theorem normalizationConeTensorMap_tmul
    (r : S.coverNormalizationRing true) (z : S.baseNormalizationRing false) :
    letI := normalizationConeBaseAlgebra S D a
    normalizationConeTensorMap S D a b h (r ⊗ₜ z) = a.f r * b.f z := rfl

theorem normalizationConeTensorMap_injective :
    letI := normalizationConeBaseAlgebra S D a
    Function.Injective (normalizationConeTensorMap S D a b h) := by
  letI := normalizationConeBaseAlgebra S D a
  have : Algebra.IsIntegral S.normalizationTensorBase S.normalizationTensorRing :=
    FunctionFieldNormalization.normalizationTensor_integral
  apply injective_of_integral_of_base_injective
  intro x y hxy
  have hR : Function.Injective
      (algebraMap S.normalizationTensorBase (S.coverNormalizationRing true)) := by
    intro c d hc
    exact Subtype.ext (congrArg (fun r : S.coverNormalizationRing true =>
      ((r : Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M true) :
        Genuine.Ω S.prime.EK)) hc)
  exact hR (a.injective hxy)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
