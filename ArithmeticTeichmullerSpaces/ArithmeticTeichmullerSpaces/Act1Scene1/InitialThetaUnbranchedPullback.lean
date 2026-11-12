import ArithmeticTeichmullerSpaces.Act1Scene1.BranchEtaleRestriction
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseNormalizationBranch
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original two-torsion branch polynomial and the proved normalization square.
fidelity: computes the entire signed base etale locus from the original branch
polynomial. The actual tensor pullback restricts to a finite etale cover over
the same branch complement in the signed covering scheme.
boundary: Scene1/Derived. This is the ordinary unbranched pullback. The
normalization comparison on this open and the orbicurve producer remain open.
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve

private theorem twoTorsion_toPoly_ne_zero {k : Type*} [Field k] [CharZero k]
    (E : WeierstrassCurve k) : E.twoTorsionPolynomial.toPoly ≠ 0 :=
  E.twoTorsionPolynomial.ne_zero_of_a_ne_zero (by change (4 : k) ≠ 0; norm_num)

@[instance_reducible] private noncomputable def branchAwayAlgebraOf
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
attribute [local instance] basePresentationCoefficientAlgebra signedBaseNormalizationAlgebra
  baseBranchSMul baseBranchModule presentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance branchBaseDedekind (pm : Bool) : IsDedekindDomain (S.baseNormalizationRing pm) :=
  FunctionFieldNormalization.dedekindRing (Genuine.xG S.prime.EK)
    (Genuine.transcendental_xG S.prime.EK) _

local instance branchBaseFinite :
    Module.Finite (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
  S.signedBaseNormalizationRingMap_finite

local instance branchBaseIntegral :
    Algebra.IsIntegral (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
  ⟨RingHom.IsIntegral.of_finite S.signedBaseNormalizationRingMap_finite⟩

local instance branchAwayAlgebra (a : S.baseNormalizationRing false) :
    Algebra (S.baseNormalizationRing true) (Localization.Away a) :=
  branchAwayAlgebraOf a

theorem baseNormalizationBranchPolynomial_ne_zero : S.baseNormalizationBranchPolynomial ≠ 0 := by
  intro h
  apply twoTorsion_toPoly_ne_zero S.prime.EK
  exact S.baseSignedNormalizationRingEquiv.injective
    (h.trans S.baseSignedNormalizationRingEquiv.map_zero.symm)

theorem signedBaseNormalization_ramificationIdx_branch
    (q : Ideal (S.baseNormalizationRing false)) (hq : q.IsMaximal) :
    q.ramificationIdx (S.baseNormalizationRing true) =
      if S.baseNormalizationBranchPolynomial ∈ q.under (S.baseNormalizationRing true)
      then 2 else 1 := by
  haveI : q.IsMaximal := hq
  let p := q.under (S.baseNormalizationRing true)
  have hp : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  exact (Genuine.signedNormalizationMultiplicity_eq_ramificationIdx S.prime.EK 1 ⊥ p q).symm.trans
    (S.baseNormalizationMultiplicity_eq_branch p hp)

theorem signedBaseNormalization_isEtaleAt_iff_branch
    (q : Ideal (S.baseNormalizationRing false)) [q.IsPrime] :
    Algebra.IsEtaleAt (S.baseNormalizationRing true) q ↔
      S.baseNormalizationBranchPolynomial ∉ q.under (S.baseNormalizationRing true) :=
  BranchEtaleRestriction.isEtaleAt_iff (k := ↥S.prime.torsionField)
    (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)
    S.baseNormalizationBranchPolynomial S.baseNormalizationBranchPolynomial_ne_zero
    S.signedBaseNormalization_ramificationIdx_branch q

theorem signedBaseNormalization_etaleLocus_branch :
    Algebra.etaleLocus (S.baseNormalizationRing true) (S.baseNormalizationRing false) =
      PrimeSpectrum.basicOpen (S.signedBaseNormalizationRingMap S.baseNormalizationBranchPolynomial) :=
  BranchEtaleRestriction.etaleLocus_eq_basicOpen (k := ↥S.prime.torsionField)
    (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)
    S.baseNormalizationBranchPolynomial S.baseNormalizationBranchPolynomial_ne_zero
    S.signedBaseNormalization_ramificationIdx_branch

theorem signedBaseNormalization_etaleAway_branch :
    Algebra.Etale (S.baseNormalizationRing true)
      (Localization.Away (S.signedBaseNormalizationRingMap S.baseNormalizationBranchPolynomial)) :=
  BranchEtaleRestriction.etale_away_branch (k := ↥S.prime.torsionField)
    (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)
    S.baseNormalizationBranchPolynomial S.baseNormalizationBranchPolynomial_ne_zero
    S.signedBaseNormalization_ramificationIdx_branch

def baseNormalizationUnbranchedOpen : (S.baseNormalizationScheme true).Opens :=
  PrimeSpectrum.basicOpen S.baseNormalizationBranchPolynomial

def baseUnsignedUnbranchedOpen : (S.baseNormalizationScheme false).Opens :=
  S.signedBaseNormalizationMap ⁻¹ᵁ S.baseNormalizationUnbranchedOpen

def signedCoverUnbranchedOpen : (S.coverNormalizationScheme true).Opens :=
  S.coverToBaseNormalizationMap true ⁻¹ᵁ S.baseNormalizationUnbranchedOpen

theorem baseNormalizationUnbranchedOpen_nonempty :
    (S.baseNormalizationUnbranchedOpen : Set (S.baseNormalizationScheme true)).Nonempty := by
  refine ⟨(⊥ : PrimeSpectrum (S.baseNormalizationRing true)), ?_⟩
  change S.baseNormalizationBranchPolynomial ≠ 0
  exact S.baseNormalizationBranchPolynomial_ne_zero

theorem signedCoverUnbranchedOpen_nonempty :
    (S.signedCoverUnbranchedOpen : Set (S.coverNormalizationScheme true)).Nonempty := by
  refine ⟨(⊥ : PrimeSpectrum (S.coverNormalizationRing true)), ?_⟩
  change S.baseToCoverNormalizationRingMap true S.baseNormalizationBranchPolynomial ≠ 0
  intro h
  exact S.baseNormalizationBranchPolynomial_ne_zero
    (S.baseToCoverNormalizationRingMap_injective true (h.trans (map_zero _).symm))

def normalizationTensorUnbranchedOpen : S.normalizationTensorScheme.Opens :=
  S.normalizationTensorToSignedCover ⁻¹ᵁ S.signedCoverUnbranchedOpen ⊓
    S.normalizationTensorToUnsignedBase ⁻¹ᵁ S.baseUnsignedUnbranchedOpen

def signedBaseUnbranchedMap : S.baseUnsignedUnbranchedOpen.toScheme ⟶
    S.baseNormalizationUnbranchedOpen.toScheme :=
  S.signedBaseNormalizationMap ∣_ S.baseNormalizationUnbranchedOpen

def signedCoverUnbranchedMap : S.signedCoverUnbranchedOpen.toScheme ⟶
    S.baseNormalizationUnbranchedOpen.toScheme :=
  S.coverToBaseNormalizationMap true ∣_ S.baseNormalizationUnbranchedOpen

def tensorToSignedCoverUnbranchedMap : S.normalizationTensorUnbranchedOpen.toScheme ⟶
    S.signedCoverUnbranchedOpen.toScheme :=
  S.normalizationTensorToSignedCover.resLE _ _ inf_le_left

def tensorToUnsignedBaseUnbranchedMap : S.normalizationTensorUnbranchedOpen.toScheme ⟶
    S.baseUnsignedUnbranchedOpen.toScheme :=
  S.normalizationTensorToUnsignedBase.resLE _ _ inf_le_right

instance etale_signedBaseUnbranchedMap : Etale S.signedBaseUnbranchedMap := by
  haveI : Algebra.Etale (S.baseNormalizationRing true)
      (Localization.Away (algebraMap (S.baseNormalizationRing true)
        (S.baseNormalizationRing false) S.baseNormalizationBranchPolynomial)) :=
    S.signedBaseNormalization_etaleAway_branch
  exact BranchEtaleRestriction.spec_restrict_etale (R := S.baseNormalizationRing true)
    (A := S.baseNormalizationRing false) S.baseNormalizationBranchPolynomial

instance finite_signedBaseUnbranchedMap : IsFinite S.signedBaseUnbranchedMap := by
  exact MorphismProperty.of_isPullback
    (isPullback_morphismRestrict S.signedBaseNormalizationMap S.baseNormalizationUnbranchedOpen).flip
    S.finite_signedBaseNormalizationMap

instance surjective_signedBaseNormalizationMap : Surjective S.signedBaseNormalizationMap :=
  ⟨(RingHom.IsIntegral.of_finite S.signedBaseNormalizationRingMap_finite).comap_surjective
    (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)⟩

instance surjective_signedBaseUnbranchedMap : Surjective S.signedBaseUnbranchedMap :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict S.signedBaseNormalizationMap S.baseNormalizationUnbranchedOpen).flip
    S.surjective_signedBaseNormalizationMap

theorem normalizationTensorUnbranchedSquare_isPullback :
    IsPullback S.tensorToSignedCoverUnbranchedMap S.tensorToUnsignedBaseUnbranchedMap
      S.signedCoverUnbranchedMap S.signedBaseUnbranchedMap := by
  simpa only [tensorToSignedCoverUnbranchedMap, tensorToUnsignedBaseUnbranchedMap,
    signedCoverUnbranchedMap, signedBaseUnbranchedMap, signedCoverUnbranchedOpen,
    baseUnsignedUnbranchedOpen, Scheme.Hom.resLE_eq_morphismRestrict] using
    (Scheme.Hom.isPullback_resLE S.normalizationTensorSquare_isPullback
      (US := S.baseNormalizationUnbranchedOpen) (UT := S.baseUnsignedUnbranchedOpen)
      (UX := S.signedCoverUnbranchedOpen) (UY := S.normalizationTensorUnbranchedOpen)
      le_rfl le_rfl rfl)

instance etale_tensorToSignedCoverUnbranchedMap : Etale S.tensorToSignedCoverUnbranchedMap :=
  MorphismProperty.of_isPullback S.normalizationTensorUnbranchedSquare_isPullback.flip
    (inferInstanceAs (Etale S.signedBaseUnbranchedMap))

instance finite_tensorToSignedCoverUnbranchedMap : IsFinite S.tensorToSignedCoverUnbranchedMap :=
  MorphismProperty.of_isPullback S.normalizationTensorUnbranchedSquare_isPullback.flip
    (inferInstanceAs (IsFinite S.signedBaseUnbranchedMap))

instance surjective_tensorToSignedCoverUnbranchedMap : Surjective S.tensorToSignedCoverUnbranchedMap :=
  MorphismProperty.of_isPullback S.normalizationTensorUnbranchedSquare_isPullback.flip
    (inferInstanceAs (Surjective S.signedBaseUnbranchedMap))

def normalizationTensorUnbranchedEtaleCover :
    Scheme.Cover.{u} (Scheme.precoverage (@Etale.{u})) S.signedCoverUnbranchedOpen.toScheme :=
  S.tensorToSignedCoverUnbranchedMap.cover (inferInstanceAs (Etale S.tensorToSignedCoverUnbranchedMap))

theorem normalizationTensorUnbranchedEtaleCover_finite
    (i : S.normalizationTensorUnbranchedEtaleCover.I₀) :
    IsFinite (S.normalizationTensorUnbranchedEtaleCover.f i) :=
  S.finite_tensorToSignedCoverUnbranchedMap

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
