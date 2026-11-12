import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedGeometricPoints

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, signed/unsigned realization;
`refer/iut/.lake/packages/pi1/Pi1/Orbicurve/Subfield.lean`, homOfLE condition.
fidelity: constructs both affine orbicurve presentations from this seed's actual
normalization rings and multiplicities. Proves the ramification compatibility
at every closed point. The signed multiplicities equal actual geometric-point
stabilizer orders, and the coarse map is the original finite normalization map.
boundary: Scene1/Derived. A comparison with root stacks or arbitrary AG.Orbicurve,
the other covering maps, the global cartesian square, core and theta-root laws
remain open. No new geometry law is an input to this construction.
-/

namespace JoshiTeich.Act1Scene1

universe u
open scoped Classical

/-- Expose the existing coefficient algebra before substituting the large seed. -/
@[instance_reducible] noncomputable def normalizationCoefficientAlgebra
    {k : Type u} [Field k] [CharZero k]
    (E : WeierstrassCurve k) [E.IsElliptic] (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra k (JoshiTeich.ReferenceIut.Anabelian.Genuine.coverCoordinateRing E ell M pm) :=
  inferInstance

end JoshiTeich.Act1Scene1

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory
open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra
  signedCoverNormalizationGaloisAction coverNormalizationPointAction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance presentationCoefficientAlgebra (pm : Bool) :
    Algebra ↥S.prime.torsionField (S.coverNormalizationRing pm) :=
  normalizationCoefficientAlgebra S.prime.EK S.prime.ℓ S.prime.M pm

/-- Both presentations use the previously constructed actual normalization rings. -/
def coverOrbicurvePresentation (pm : Bool) : AffineOrbicurvePresentation ↥S.prime.torsionField where
  A := S.coverNormalizationRing pm
  finiteType := Genuine.finiteType_coverCoordinateRing S.prime.EK S.prime.ℓ S.prime.M pm
  not_isField := S.coverNormalizationRing_notField pm
  mult := S.coverNormalizationMultiplicity pm
  mult_pos := S.coverNormalizationMultiplicity_pos pm
  finite_mult := S.coverNormalizationMultiplicity_finite pm

theorem coverOrbicurvePresentation_coarseScheme (pm : Bool) :
    (S.coverOrbicurvePresentation pm).coarseScheme = S.coverNormalizationScheme pm := rfl

/-- Closed points contract to closed points along the actual integral inclusion. -/
theorem signedCoverNormalization_contraction_isMaximal
    (w : Ideal (S.coverNormalizationRing false)) (hw : w.IsMaximal) :
    (w.comap S.signedCoverNormalizationRingMap).IsMaximal := by
  have : w.IsMaximal := hw
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    S.signedCoverNormalizationRingMap.toRingHom
    S.signedCoverNormalizationRingMap_isIntegral w

/-- The branched cover satisfies the reference's full closed-point multiplicity law. -/
theorem signedCoverNormalization_ramificationCondition
    (w : Ideal (S.coverNormalizationRing false)) (hw : w.IsMaximal) :
    (letI := S.signedCoverNormalizationRingMap.toRingHom.toAlgebra;
      w.ramificationIdx (S.coverNormalizationRing true)) *
        S.coverNormalizationMultiplicity false w =
      S.coverNormalizationMultiplicity true (w.comap S.signedCoverNormalizationRingMap) := by
  have : w.IsMaximal := hw
  let p := w.comap S.signedCoverNormalizationRingMap.toRingHom
  have : w.LiesOver p := ⟨rfl⟩
  change w.ramificationIdx (S.coverNormalizationRing true) * 1 =
    S.signedCoverRamificationMultiplicity p
  exact (mul_one _).trans
    (S.signedCoverRamificationMultiplicity_eq_ramificationIdx p w).symm

/-- The actual signed inclusion as a cover of the two affine presentations. -/
def signedCoverOrbicurvePresentation :
    AffineOrbicurvePresentation.Cover
      (S.coverOrbicurvePresentation false) (S.coverOrbicurvePresentation true) where
  f := S.signedCoverNormalizationRingMap
  injective := S.signedCoverNormalizationRingMap_injective
  isIntegral := S.signedCoverNormalizationRingMap_isIntegral
  ramification := S.signedCoverNormalization_ramificationCondition

theorem signedCoverOrbicurvePresentation_coarseMap :
    S.signedCoverOrbicurvePresentation.coarseMap = S.signedCoverNormalizationMap := rfl

theorem signedCoverOrbicurvePresentation_coarseMap_finite :
    AlgebraicGeometry.IsFinite S.signedCoverOrbicurvePresentation.coarseMap :=
  S.finite_signedCoverNormalizationMap

/-- Presentation multiplicities are the proved orders of actual geometric stabilizers. -/
theorem coverOrbicurvePresentation_signed_mult_eq_stabilizer
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    (S.coverOrbicurvePresentation true).mult p =
      Nat.card (MulAction.stabilizer S.signedCoverQuotientGroup
        (S.coverNormalizationGeometricPoint P)) :=
  (S.coverNormalizationGeometricPoint_stabilizer_card p P).symm

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
