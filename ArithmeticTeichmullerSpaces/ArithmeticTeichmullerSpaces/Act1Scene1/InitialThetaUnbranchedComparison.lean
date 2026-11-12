import ArithmeticTeichmullerSpaces.Act1Scene1.DedekindUnbranchedEtale
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaUnbranchedPullback
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaOrbicurvePresentationSquare

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved ramification tower law and the original two-torsion branch polynomial.
fidelity: the signed horizontal map is etale over the original branch
complement. The unsigned covering's comparison with the actual tensor
pullback restricts to a finite etale morphism, with its original base map.
boundary: Scene1/Derived. This proves etaleness of the comparison. Its
identification with the selected component as an isomorphism remains open.
-/

namespace JoshiTeich.Act1Scene1

private theorem factors_of_product_one {a b : ℕ} (h : a * b = 1) : a = 1 ∧ b = 1 :=
  ⟨Nat.dvd_one.mp ⟨b, h.symm⟩, Nat.dvd_one.mp ⟨a, h.symm.trans (mul_comm a b)⟩⟩

@[instance_reducible] private noncomputable def unbranchedAwayAlgebraOf
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    Algebra R (Localization.Away a) := inferInstance

end JoshiTeich.Act1Scene1

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] presentationCoefficientAlgebra basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance signedHorizontalAlgebra :
    Algebra (S.baseNormalizationRing true) (S.coverNormalizationRing true) :=
  (S.baseToCoverNormalizationRingMap true).toRingHom.toAlgebra
local instance signedHorizontalSMul :
    SMul (S.baseNormalizationRing true) (S.coverNormalizationRing true) :=
  (signedHorizontalAlgebra S).toSMul
local instance signedHorizontalModule :
    Module (S.baseNormalizationRing true) (S.coverNormalizationRing true) :=
  (signedHorizontalAlgebra S).toModule
local instance signedHorizontalFinite :
    Module.Finite (S.baseNormalizationRing true) (S.coverNormalizationRing true) :=
  S.baseToCoverNormalizationRingMap_finite true
local instance signedHorizontalIntegral :
    Algebra.IsIntegral (S.baseNormalizationRing true) (S.coverNormalizationRing true) :=
  ⟨S.baseToCoverNormalizationRingMap_isIntegral true⟩
local instance signedHorizontalBaseDedekind : IsDedekindDomain (S.baseNormalizationRing true) :=
  FunctionFieldNormalization.dedekindRing (Genuine.xG S.prime.EK)
    (Genuine.transcendental_xG S.prime.EK) _
local instance signedHorizontalCoverDedekind : IsDedekindDomain (S.coverNormalizationRing true) :=
  FunctionFieldNormalization.dedekindRing (Genuine.xG S.prime.EK)
    (Genuine.transcendental_xG S.prime.EK) _
local instance signedHorizontalAwayAlgebra (a : S.coverNormalizationRing true) :
    Algebra (S.baseNormalizationRing true) (Localization.Away a) :=
  unbranchedAwayAlgebraOf a

theorem signedCoverUnbranched_indices
    (q : Ideal (S.coverNormalizationRing true)) (hq : q.IsMaximal)
    (hd : S.baseNormalizationBranchPolynomial ∉ q.under (S.baseNormalizationRing true)) :
    q.ramificationIdx (S.baseNormalizationRing true) = 1 ∧
      S.coverNormalizationMultiplicity true q = 1 := by
  haveI : q.IsMaximal := hq
  have hp : (q.under (S.baseNormalizationRing true)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  have hb : S.baseNormalizationMultiplicity true (q.under (S.baseNormalizationRing true)) = 1 := by
    rw [S.baseNormalizationMultiplicity_eq_branch _ hp, if_neg hd]
  exact factors_of_product_one ((S.baseToCoverNormalization_ramificationCondition true q hq).trans hb)

theorem signedCoverNormalization_etaleAway_branch :
    Algebra.Etale (S.baseNormalizationRing true)
      (Localization.Away (S.baseToCoverNormalizationRingMap true S.baseNormalizationBranchPolynomial)) :=
  DedekindUnbranchedEtale.etale_away_of_closed_index_one (k := ↥S.prime.torsionField)
    (S.baseToCoverNormalizationRingMap_injective true) S.baseNormalizationBranchPolynomial
    (fun q hq hd => (S.signedCoverUnbranched_indices q hq hd).1)

instance etale_signedCoverUnbranchedMap : Etale S.signedCoverUnbranchedMap := by
  haveI : Algebra.Etale (S.baseNormalizationRing true)
      (Localization.Away (algebraMap (S.baseNormalizationRing true)
        (S.coverNormalizationRing true) S.baseNormalizationBranchPolynomial)) :=
    S.signedCoverNormalization_etaleAway_branch
  exact BranchEtaleRestriction.spec_restrict_etale (R := S.baseNormalizationRing true)
    (A := S.coverNormalizationRing true) S.baseNormalizationBranchPolynomial

instance finite_signedCoverUnbranchedMap : IsFinite S.signedCoverUnbranchedMap :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (S.coverToBaseNormalizationMap true)
      S.baseNormalizationUnbranchedOpen).flip
    (S.finite_coverToBaseNormalizationMap true)

instance etale_tensorToUnsignedBaseUnbranchedMap : Etale S.tensorToUnsignedBaseUnbranchedMap :=
  MorphismProperty.of_isPullback S.normalizationTensorUnbranchedSquare_isPullback
    S.etale_signedCoverUnbranchedMap

instance finite_tensorToUnsignedBaseUnbranchedMap : IsFinite S.tensorToUnsignedBaseUnbranchedMap :=
  MorphismProperty.of_isPullback S.normalizationTensorUnbranchedSquare_isPullback
    S.finite_signedCoverUnbranchedMap

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
