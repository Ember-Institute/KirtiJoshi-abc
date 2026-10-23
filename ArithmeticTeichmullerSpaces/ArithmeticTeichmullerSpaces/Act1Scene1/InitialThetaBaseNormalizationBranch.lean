import ArithmeticTeichmullerSpaces.Act1Scene1.RamificationEquivSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseBranchMultiplicity

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original coordinate-normalization square and its proved ramification law.
fidelity: the existing signed base presentation has multiplicity two exactly
on the original two-torsion polynomial, and one elsewhere. The coordinate
comparison preserves the actual local ramification indices at closed points.
boundary: Scene1/Derived. This identifies ordinary affine presentation
multiplicities, without constructing arbitrary AG.Orbicurve objects or a core.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] basePresentationCoefficientAlgebra signedBaseNormalizationAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance baseBranchSMul :
    SMul (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
  S.signedBaseNormalizationAlgebra.toSMul

local instance baseBranchModule :
    Module (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
  S.signedBaseNormalizationAlgebra.toModule

theorem curveCoordinateRing_isDedekindDomain :
    IsDedekindDomain S.prime.EK.toAffine.CoordinateRing := by
  have : Module.Finite (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis S.prime.EK.toAffine)
  exact { IsNoetherianRing.of_finite (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing,
    Ring.DimensionLEOne.of_isIntegral (↥S.prime.torsionField)[X] S.prime.EK.toAffine.CoordinateRing,
    S.curveCoordinateRing_isIntegrallyClosed with }

def baseNormalizationBranchPolynomial : S.baseNormalizationRing true :=
  S.baseSignedNormalizationRingEquiv S.prime.EK.twoTorsionPolynomial.toPoly

theorem signedBaseNormalization_ramificationIdx_coordinate
    (w : Ideal (S.baseNormalizationRing false)) (hw : w.IsMaximal) :
    w.ramificationIdx (S.baseNormalizationRing true) =
      (w.comap S.curveNormalizationRingEquiv).ramificationIdx (↥S.prime.torsionField)[X] := by
  have : w.IsMaximal := hw
  have : Algebra.IsIntegral (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
    ⟨FunctionFieldNormalization.ringMap_isIntegral _⟩
  have : IsDedekindDomain S.prime.EK.toAffine.CoordinateRing :=
    S.curveCoordinateRing_isDedekindDomain
  have : IsDedekindDomain (S.baseNormalizationRing false) :=
    FunctionFieldNormalization.dedekindRing (Genuine.xG S.prime.EK)
      (Genuine.transcendental_xG S.prime.EK) _
  let p := w.under (S.baseNormalizationRing true)
  have hpmax : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal w
  have hp : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hpmax
    (Genuine.notField_coverCoordinateRing S.prime.EK 1 ⊥ true)
  have hpmap : p.map (algebraMap (S.baseNormalizationRing true)
      (S.baseNormalizationRing false)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)).not.mpr hp
  exact (RamificationEquivSquare.ramificationIdx_eq
    S.baseSignedNormalizationRingEquiv.toRingEquiv S.curveNormalizationRingEquiv.toRingEquiv
    S.curveNormalizationRingMap_algebraMap_poly p w hpmap).symm

theorem signedBaseNormalization_exists_maximal_over
    (p : Ideal (S.baseNormalizationRing true)) (hp : p.IsMaximal) :
    ∃ w : Ideal (S.baseNormalizationRing false), w.IsMaximal ∧ w.LiesOver p := by
  have : p.IsMaximal := hp
  have : Algebra.IsIntegral (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
    ⟨Genuine.signedNormalizationRingMap_isIntegral S.prime.EK 1 ⊥⟩
  have : FaithfulSMul (S.baseNormalizationRing true) (S.baseNormalizationRing false) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Genuine.signedNormalizationRingMap_injective S.prime.EK 1 ⊥)
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := S.baseNormalizationRing true) (S := S.baseNormalizationRing false) p

theorem baseNormalizationMultiplicity_eq_branch
    (p : Ideal (S.baseNormalizationRing true)) (hp : p.IsMaximal) :
    S.baseNormalizationMultiplicity true p =
      if S.baseNormalizationBranchPolynomial ∈ p then 2 else 1 := by
  have : p.IsMaximal := hp
  let w : Ideal (S.baseNormalizationRing false) :=
    Classical.choose (S.signedBaseNormalization_exists_maximal_over p hp)
  have hw : w.IsMaximal :=
    (Classical.choose_spec (S.signedBaseNormalization_exists_maximal_over p hp)).1
  have hwp : w.LiesOver p :=
    (Classical.choose_spec (S.signedBaseNormalization_exists_maximal_over p hp)).2
  have : w.IsMaximal := hw
  have : w.LiesOver p := hwp
  have hbranch := RamificationEquivSquare.mem_under_iff
    S.baseSignedNormalizationRingEquiv.toRingEquiv S.curveNormalizationRingEquiv.toRingEquiv
    S.curveNormalizationRingMap_algebraMap_poly p w S.prime.EK.twoTorsionPolynomial.toPoly
  have hm : S.baseNormalizationMultiplicity true p =
      w.ramificationIdx (S.baseNormalizationRing true) :=
    Genuine.signedNormalizationMultiplicity_eq_ramificationIdx S.prime.EK 1 ⊥ p w
  exact hm.trans ((S.signedBaseNormalization_ramificationIdx_coordinate w hw).trans
    ((S.curveCoordinate_ramificationIdx_eq (w.comap S.curveNormalizationRingEquiv)).trans
      (congrArg (fun b : Prop => if b then (2 : ℕ) else 1) (propext hbranch))))

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
