import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineNormalizationSquareRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseOrbicurvePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnsignedNormalizationEtale

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the normalization square and the proved ramification tower formula.
fidelity: constructs the actual horizontal covers of the base and covering
affine presentations. All four maps have their closed-point multiplicity law.
Their coarse square is the original commuting finite normalization square;
its unsigned horizontal map is etale.
boundary: Scene1/Derived. The root-stack comparison, orbicurve cartesian square,
core and full geometric producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] presentationCoefficientAlgebra basePresentationCoefficientAlgebra
  unsignedCoverNormalizationAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem baseToCoverNormalizationRingMap_isIntegral (pm : Bool) :
    (S.baseToCoverNormalizationRingMap pm).toRingHom.IsIntegral :=
  FunctionFieldNormalization.ringMap_isIntegral (S.normalizationField_contains_base pm)

/-- Both horizontal maps satisfy the multiplicity law on every closed point. -/
theorem baseToCoverNormalization_ramificationCondition (pm : Bool)
    (w : Ideal (S.coverNormalizationRing pm)) (hw : w.IsMaximal) :
    (letI := (S.baseToCoverNormalizationRingMap pm).toRingHom.toAlgebra;
      w.ramificationIdx (S.baseNormalizationRing pm)) * S.coverNormalizationMultiplicity pm w =
        S.baseNormalizationMultiplicity pm (w.comap (S.baseToCoverNormalizationRingMap pm)) := by
  cases pm
  · exact (mul_one _).trans (S.unsignedCoverNormalization_ramificationIdx_one w hw)
  · exact Genuine.signedNormalization_base_ramification S.prime.EK S.prime.ℓ S.prime.M w hw

/-- The original base-to-cover inclusion defines a cover of the actual presentations. -/
def normalizationOrbicurvePresentationCover (pm : Bool) :
    AffineOrbicurvePresentation.Cover
      (S.coverOrbicurvePresentation pm) (S.baseOrbicurvePresentation pm) where
  f := S.baseToCoverNormalizationRingMap pm
  injective := S.baseToCoverNormalizationRingMap_injective pm
  isIntegral := S.baseToCoverNormalizationRingMap_isIntegral pm
  ramification := S.baseToCoverNormalization_ramificationCondition pm

theorem normalizationOrbicurvePresentationCover_coarseMap (pm : Bool) :
    (S.normalizationOrbicurvePresentationCover pm).coarseMap =
      S.coverToBaseNormalizationMap pm := rfl

theorem normalizationOrbicurvePresentationCover_coarseMap_finite (pm : Bool) :
    AlgebraicGeometry.IsFinite (S.normalizationOrbicurvePresentationCover pm).coarseMap :=
  S.finite_coverToBaseNormalizationMap pm

theorem normalizationOrbicurvePresentationCover_unsigned_coarseMap_etale :
    AlgebraicGeometry.Etale (S.normalizationOrbicurvePresentationCover false).coarseMap :=
  S.etale_coverToBaseUnsignedNormalizationMap

/-- This is the original commuting square, with all four presentation-cover laws proved. -/
theorem normalizationOrbicurvePresentation_square :
    (S.normalizationOrbicurvePresentationCover false).coarseMap ≫
        S.signedBaseOrbicurvePresentation.coarseMap =
      S.signedCoverOrbicurvePresentation.coarseMap ≫
        (S.normalizationOrbicurvePresentationCover true).coarseMap :=
  S.normalizationMap_square

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
