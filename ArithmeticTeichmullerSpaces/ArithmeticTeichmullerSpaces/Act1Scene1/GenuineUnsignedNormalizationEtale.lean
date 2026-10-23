import ArithmeticTeichmullerSpaces.Act1Scene1.DedekindEtale
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationRamification

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's ramification, flatness and etale-locus criteria.
fidelity: the actual unsigned normalization inclusion over the level-one
unsigned normalization is etale. All geometric laws used here are proved.
boundary: Scene1/Derived. Orbicurve realization, cartesianness, core and the
full geometric producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Use the actual inclusion of the level-one and covering normalization rings. -/
@[instance_reducible] def unsignedNormalizationAlgebra (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    Algebra (coverCoordinateRing E 1 ⊥ false) (coverCoordinateRing E ell M false) :=
  FunctionFieldNormalization.ringMapAlgebra (normalization_base_unsigned_le E ell M)

attribute [local instance] unsignedNormalizationAlgebra

theorem unsignedNormalization_etale (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra.Etale (coverCoordinateRing E 1 ⊥ false) (coverCoordinateRing E ell M false) := by
  letI : SMul (coverCoordinateRing E 1 ⊥ false) (coverCoordinateRing E ell M false) :=
    (unsignedNormalizationAlgebra E ell M).toSMul
  letI : Module (coverCoordinateRing E 1 ⊥ false) (coverCoordinateRing E ell M false) :=
    (unsignedNormalizationAlgebra E ell M).toModule
  have : Module.Finite (coverCoordinateRing E 1 ⊥ false)
      (coverCoordinateRing E ell M false) :=
    FunctionFieldNormalization.moduleFinite_ringMap (transcendental_xG E)
      (normalization_base_unsigned_le E ell M)
  exact DedekindEtale.etale_of_closed_ramificationIdx_one (K := k)
    (FunctionFieldNormalization.ringMap_injective (normalization_base_unsigned_le E ell M))
    (unsignedNormalization_ramificationIdx_one E ell M)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
