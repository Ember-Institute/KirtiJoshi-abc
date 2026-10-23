import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineCoordinateNormalizationMap
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassCoordinateDiscriminant
import ArithmeticTeichmullerSpaces.Act1Scene1.SquarefreeDiscriminantSurjectivity

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual finite normalization inclusion and squarefree Weierstrass basis discriminant.
fidelity: proves that the original coordinate ring maps onto the actual unsigned
base normalization. The comparison preserves the original ambient function field.
boundary: Scene1/Derived. This resolves the coordinate-ring comparison.
Orbicurve realization, cartesianness, core and the full producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

theorem polynomialNormalization_finite :
    Module.Finite k[X] (integralClosure k[X] E.toAffine.FunctionField) := by
  let e := polynomialNormalizationRingAlgEquiv E
  let g := signedNormalizationRingMap E 1 ⊥
  let p := signedBasePolynomialAlgEquiv E
  have he : e.symm.toRingHom.Finite := RingHom.Finite.of_surjective _ e.symm.surjective
  have hg : g.toRingHom.Finite :=
    FunctionFieldNormalization.ringMap_finite (transcendental_xG E) _
  have hp : p.toRingHom.Finite := RingHom.Finite.of_surjective _ p.surjective
  have hcomp : e.symm.toRingHom.comp (g.toRingHom.comp p.toRingHom) =
      algebraMap k[X] (integralClosure k[X] E.toAffine.FunctionField) := by
    apply RingHom.ext
    intro a
    exact e.injective (by
      change e (e.symm (g (p a))) = e (algebraMap k[X] _ a)
      rw [e.apply_symm_apply]
      exact (baseNormalizationRingEquiv_square E a).symm)
  exact RingHom.finite_algebraMap.mp (hcomp ▸ he.comp (hg.comp hp))

/-- The closure contains the original coordinates, so it has the same fraction field. -/
theorem polynomialNormalization_fractionField :
    IsFractionRing (integralClosure k[X] E.toAffine.FunctionField) E.toAffine.FunctionField := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective E.toAffine.CoordinateRing z
  exact ⟨coordinatePolynomialNormalizationMap E a, coordinatePolynomialNormalizationMap E b,
    hab.symm⟩

theorem coordinatePolynomialNormalizationMap_surjective :
    Function.Surjective (coordinatePolynomialNormalizationMap E) := by
  have := polynomialNormalization_finite E
  have := polynomialNormalization_fractionField E
  have : FaithfulSMul k[X] E.toAffine.FunctionField :=
    FaithfulSMul.trans k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField
  exact SquarefreeDiscriminantSurjectivity.surjective
    (L := E.toAffine.FunctionField) (coordinatePolynomialNormalizationMap E) (fun _ => rfl)
    2 (Affine.CoordinateRing.basis E.toAffine)
    (WeierstrassCoordinateDiscriminant.discr_basis_squarefree E)

theorem coordinateRing_isIntegralClosure :
    IsIntegralClosure E.toAffine.CoordinateRing k[X] E.toAffine.FunctionField where
  algebraMap_injective := IsFractionRing.injective _ _
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := coordinatePolynomialNormalizationMap_surjective E ⟨x, hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    · rintro ⟨a, rfl⟩
      exact (coordinateRing_isIntegral E).isIntegral a |>.algebraMap

theorem coordinateRing_isIntegrallyClosed : IsIntegrallyClosed E.toAffine.CoordinateRing := by
  have := coordinateRing_isIntegralClosure E
  have := coordinateRing_isIntegral E
  apply (isIntegrallyClosed_iff E.toAffine.FunctionField).mpr
  intro x hx
  exact (IsIntegralClosure.isIntegral_iff (A := E.toAffine.CoordinateRing) (R := k[X])).mp
    (isIntegral_trans (R := k[X]) x hx)

theorem coordinateToBaseNormalization_surjective :
    Function.Surjective (coordinateToBaseNormalization E) :=
  (polynomialNormalizationRingAlgEquiv E).surjective.comp
    (coordinatePolynomialNormalizationMap_surjective E)

/-- The equivalence is induced by the original natural coordinate-ring map. -/
def coordinateBaseNormalizationAlgEquiv :
    E.toAffine.CoordinateRing ≃ₐ[k] coverCoordinateRing E 1 ⊥ false :=
  AlgEquiv.ofBijective (coordinateToBaseNormalization E)
    ⟨coordinateToBaseNormalization_injective E, coordinateToBaseNormalization_surjective E⟩

@[simp] theorem coordinateBaseNormalizationAlgEquiv_apply (a : E.toAffine.CoordinateRing) :
    coordinateBaseNormalizationAlgEquiv E a = coordinateToBaseNormalization E a := rfl

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
