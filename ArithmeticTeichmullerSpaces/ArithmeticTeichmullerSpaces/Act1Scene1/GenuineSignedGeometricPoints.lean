import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPointInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationGalois

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's residue-field geometric point and inertia subgroup definitions.
fidelity: uses the actual signed quotient action and the actual unsigned
normalization ring. Its residue-closure geometric point has stabilizer equal
to inertia, hence order equal to the existing ramification multiplicity.
The action preserves restriction to the actual signed normalization ring.
boundary: Scene1/Derived. Orbicurve realization, etale covering comparison,
cartesianness, core and theta-root laws remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical
universe u v
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] normalizationUnsignedNormal signedNormalizationGaloisAction
  signedNormalizationAlgebra

@[instance_reducible] def normalizationPointAction (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) (C : Type v) [CommRing C] :
    MulAction (signedGaloisGroup E ell M) (coverCoordinateRing E ell M false →+* C) :=
  GeometricPointInertia.pointAction (signedGaloisGroup E ell M)
    (coverCoordinateRing E ell M false) C

attribute [local instance] normalizationPointAction

def normalizationGeometricPoint (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] :
    coverCoordinateRing E ell M false →+* AlgebraicClosure P.ResidueField :=
  GeometricPointInertia.residueGeometricPoint P

theorem normalizationGeometricPoint_ker (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] :
    RingHom.ker (normalizationGeometricPoint E ell M P) = P :=
  GeometricPointInertia.ker_residueGeometricPoint P

/-- The geometric point stabilizer is inertia, rather than the decomposition group. -/
theorem normalizationGeometricPoint_stabilizer (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] :
    MulAction.stabilizer (signedGaloisGroup E ell M) (normalizationGeometricPoint E ell M P) =
      P.inertia (signedGaloisGroup E ell M) :=
  (GeometricPointInertia.stabilizer_eq_inertia (signedGaloisGroup E ell M)
    (coverCoordinateRing E ell M false) (AlgebraicClosure P.ResidueField)
    (normalizationGeometricPoint E ell M P)).trans
      (congrArg (fun I : Ideal (coverCoordinateRing E ell M false) =>
        I.inertia (signedGaloisGroup E ell M)) (normalizationGeometricPoint_ker E ell M P))

/-- Actual geometric stabilizer orders are the previously defined cover multiplicities. -/
theorem normalizationGeometricPoint_stabilizer_card (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer (signedGaloisGroup E ell M)
      (normalizationGeometricPoint E ell M P)) =
        FunctionFieldNormalization.ramificationMultiplicity
          (normalizationField_signed_le_unsigned E ell M) p :=
  (congrArg (fun H : Subgroup (signedGaloisGroup E ell M) => Nat.card H)
    (normalizationGeometricPoint_stabilizer E ell M P)).trans
      (signedNormalization_card_inertia E ell M p P)

/-- The same signed normalization inclusion, exposed as a ring homomorphism. -/
def normalizationSignedRingHom (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    coverCoordinateRing E ell M true →+* coverCoordinateRing E ell M false :=
  (signedNormalizationRingMap E ell M).toRingHom

/-- Translating points leaves their restriction to the signed normalization ring fixed. -/
theorem normalizationPoint_preserves_signed (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (C : Type v) [CommRing C] (g : signedGaloisGroup E ell M)
    (f : coverCoordinateRing E ell M false →+* C) :
    (GeometricPointInertia.translatePoint (signedGaloisGroup E ell M)
      (coverCoordinateRing E ell M false) C g f).comp
        (normalizationSignedRingHom E ell M) =
      f.comp (normalizationSignedRingHom E ell M) := by
  apply RingHom.ext
  intro a
  change f (signedQuotientNormalizationAut E ell M g⁻¹
    (signedNormalizationRingMap E ell M a)) = f (signedNormalizationRingMap E ell M a)
  exact congrArg f (signedQuotientNormalizationAut_fixed_signed E ell M g⁻¹ a)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
