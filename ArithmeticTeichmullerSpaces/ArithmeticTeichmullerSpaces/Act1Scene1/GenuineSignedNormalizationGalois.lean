import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationAction
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationRamification
import Mathlib.RingTheory.Flat.TorsionFree

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib `Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.card_stabilizer_eq`.
fidelity: the actual signed quotient is a Galois group for the signed/unsigned
normalization-ring extension. Its inertia group at a prime above a base prime
has order equal to the actual ramification multiplicity. The decomposition
stabilizer has order equal to multiplicity times residue degree.
boundary: Scene1/Derived. This does not identify arithmetic prime stabilizers
with geometric point stabilizers, or prove the orbicurve/etale comparison.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped IntermediateField.algebraAdjoinAdjoin Classical Pointwise
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

local instance normalizationUnsignedNormal (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    ((Hgp E ell M false).subgroupOf (Hgp E ell M true)).Normal :=
  Hgp_false_normal E ell M true
attribute [local instance] finite_signedGaloisGroup

/-- Use exactly the existing inclusion of the two integral closures. -/
@[instance_reducible] def signedNormalizationAlgebra (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    Algebra (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  FunctionFieldNormalization.ringMapAlgebra (normalizationField_signed_le_unsigned E ell M)

attribute [local instance] signedNormalizationAlgebra

local instance normSMul (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    SMul (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  (signedNormalizationAlgebra E ell M).toSMul
local instance normModule (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  (signedNormalizationAlgebra E ell M).toModule

/-- The ring action is the previously proved actual quotient action. -/
@[instance_reducible] def signedNormalizationGaloisAction (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    MulSemiringAction (signedGaloisGroup E ell M) (coverCoordinateRing E ell M false) :=
  MulSemiringAction.compHom _ (signedQuotientNormalizationAut E ell M)

attribute [local instance] signedNormalizationGaloisAction

theorem signedNormalizationGaloisGroup (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    IsGaloisGroup (signedGaloisGroup E ell M)
      (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) where
  faithful := ⟨fun h => signedQuotientNormalizationAut_injective E ell M (RingEquiv.ext h)⟩
  commutes := ⟨fun g a x => by
    change (signedQuotientNormalizationAut E ell M g)
      (signedNormalizationRingMap E ell M a * x) =
        signedNormalizationRingMap E ell M a * (signedQuotientNormalizationAut E ell M g x)
    exact (map_mul (signedQuotientNormalizationAut E ell M g)
      (signedNormalizationRingMap E ell M a) x).trans
        (congrArg (fun z => z * (signedQuotientNormalizationAut E ell M g x))
          (signedQuotientNormalizationAut_fixed_signed E ell M g a))⟩
  isInvariant := ⟨fun x hx => (signedNormalizationInvariant_iff E ell M x).mp hx⟩

attribute [local instance] signedNormalizationGaloisGroup

local instance normFinite (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.Finite (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  FunctionFieldNormalization.moduleFinite_ringMap (transcendental_xG E)
    (normalizationField_signed_le_unsigned E ell M)

local instance normIntegral (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra.IsIntegral (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  ⟨signedNormalizationRingMap_isIntegral E ell M⟩

local instance normTorsionFree (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.IsTorsionFree (coverCoordinateRing E ell M true)
      (coverCoordinateRing E ell M false) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact signedNormalizationRingMap_injective E ell M

local instance normFlat (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.Flat (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) :=
  inferInstance

private theorem residueCharZero {K R : Type*} [Field K] [CharZero K]
    [CommRing R] [Algebra K R] (p : Ideal R) [p.IsPrime] : CharZero p.ResidueField := by
  let f : K →+* p.ResidueField := (algebraMap R p.ResidueField).comp (algebraMap K R)
  exact charZero_of_injective_ringHom f.injective

private theorem separableResiduesOfCharZero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    [CharZero p.ResidueField] : Algebra.HasSeparableResidueFieldsAt R S p := inferInstance

local instance normResidueCharZero (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime] : CharZero p.ResidueField :=
  residueCharZero (K := k) p

local instance normSeparableResidues (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime] :
    Algebra.HasSeparableResidueFieldsAt (coverCoordinateRing E ell M true)
      (coverCoordinateRing E ell M false) p := separableResiduesOfCharZero p

local instance normIdealAction (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    MulAction (signedGaloisGroup E ell M) (Ideal (coverCoordinateRing E ell M false)) :=
  (Ideal.pointwiseDistribMulAction (M := signedGaloisGroup E ell M)
    (R := coverCoordinateRing E ell M false)).toMulAction

/-- The chosen-prime multiplicity equals the index at every prime above the base prime. -/
theorem signedNormalizationMultiplicity_eq_ramificationIdx (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    FunctionFieldNormalization.ramificationMultiplicity
      (normalizationField_signed_le_unsigned E ell M) p =
        P.ramificationIdx (coverCoordinateRing E ell M true) :=
  Ideal.ramificationIdxIn_eq_ramificationIdx p P (signedGaloisGroup E ell M)

/-- The actual ramification multiplicity is the inertia-group order. -/
theorem signedNormalization_card_inertia (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    Nat.card (P.inertia (signedGaloisGroup E ell M)) =
      FunctionFieldNormalization.ramificationMultiplicity
        (normalizationField_signed_le_unsigned E ell M) p :=
  Ideal.card_inertia_eq_ramificationIdxIn (G := signedGaloisGroup E ell M) p P

/-- Arithmetic prime stabilizers also include the residue-degree factor. -/
theorem signedNormalization_card_stabilizer (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer (signedGaloisGroup E ell M) P) =
      FunctionFieldNormalization.ramificationMultiplicity
        (normalizationField_signed_le_unsigned E ell M) p *
          p.inertiaDegIn (coverCoordinateRing E ell M false) :=
  Ideal.card_stabilizer_eq (G := signedGaloisGroup E ell M) p P

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
