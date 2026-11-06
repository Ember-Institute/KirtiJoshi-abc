import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedFixedRing
import ArithmeticTeichmullerSpaces.Act1Scene1.FixedSubringDescent

/-!
source-id: JT-SCENE1-SIGNED-NORMALIZATION-QUOTIENT-DESCENT-20261106
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the quotient of the original covering by the actual signed action.
fidelity: an arbitrary coordinate-ring map into the unsigned normalization
has invariant image exactly when it factors uniquely through the original
signed inclusion. The same map and action appear on both sides.
Original proofs; no reference implementation copied.
boundary: the universal property for affine targets, without a root-stack,
fundamental-group, cusp, core or theta-root realization.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra signedCoverNormalizationGaloisAction

@[instance_reducible] private def signedDescentCoefficientAlgebraForCurve
    {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra k (Genuine.coverCoordinateRing E ell M pm) := inferInstance

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance signedDescentCoefficientAlgebra (pm : Bool) :
    Algebra ↥S.prime.torsionField (S.coverNormalizationRing pm) :=
  signedDescentCoefficientAlgebraForCurve S.prime.EK S.prime.ℓ S.prime.M pm

/-- Descent to the actual signed quotient, for any invariant coordinate-ring map. -/
theorem signedNormalization_invariant_factor_unique
    {C : Type*} [CommRing C] (f : C →+* S.coverNormalizationRing false)
    (hf : ∀ g : S.signedCoverQuotientGroup, ∀ c,
      S.signedCoverQuotientNormalizationAut g (f c) = f c) :
    ∃! q : C →+* S.coverNormalizationRing true,
      S.signedCoverNormalizationRingMap.toRingHom.comp q = f := by
  apply fixedSubring_factor_unique
    (FixedPoints.subsemiring (S.coverNormalizationRing false) S.signedCoverQuotientGroup)
    S.signedNormalizationFixedRingEquiv S.signedCoverNormalizationRingMap.toRingHom
    (fun a => S.signedNormalizationFixedRingEquiv_apply_coe a) f
  intro c
  change ∀ g : S.signedCoverQuotientGroup,
    S.signedCoverQuotientNormalizationAut g (f c) = f c
  exact fun g => hf g c

/-- The signed inclusion has exactly the invariant maps as its unique factorizations. -/
theorem signedNormalization_invariant_iff_unique_factor
    {C : Type*} [CommRing C] (f : C →+* S.coverNormalizationRing false) :
    (∀ g : S.signedCoverQuotientGroup, ∀ c,
      S.signedCoverQuotientNormalizationAut g (f c) = f c) ↔
    ∃! q : C →+* S.coverNormalizationRing true,
      S.signedCoverNormalizationRingMap.toRingHom.comp q = f := by
  refine ⟨S.signedNormalization_invariant_factor_unique f, ?_⟩
  rintro ⟨q, hq, _⟩ g c
  have hc := RingHom.congr_fun hq c
  exact (congrArg (S.signedCoverQuotientNormalizationAut g) hc).symm.trans
    ((S.signedCoverQuotientNormalizationAut_fixed_signed g (q c)).trans hc)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
