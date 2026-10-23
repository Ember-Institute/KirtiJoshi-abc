import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedCompositum
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationRamification

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's ramification tower formula and Galois multiplicity comparison.
fidelity: proves the closed-point multiplicity formula for the actual signed
normalization map to level one. The unsigned horizontal index is proved to be
one; the two vertical multiplicities are the actual Galois indices.
boundary: Scene1/Derived. This supplies the signed cover's presentation law.
Orbicurve realization, cartesianness, core and the full producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1 FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin
attribute [local instance 2000] Classical.propDecidable
attribute [local instance] signedNormalizationAlgebra normSMul normModule
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- A signed action on a division point induces the same sign on the generic point. -/
theorem normalization_base_signed_le (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    normalizationField E 1 ⊥ true ≤ normalizationField E ell M true := by
  apply rebaseField_mono (baseField_eq_xLine E)
  apply IntermediateField.fixedField_antitone
  rintro σ ⟨ε, hε, hT⟩
  refine ⟨ε, hε, ?_⟩
  rw [Qpt_one, act_generic_eq_sign E hT, sub_self]
  exact zero_mem _

/-- The horizontal signed map satisfies the full closed-point multiplicity law. -/
theorem signedNormalization_base_ramification (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (w : Ideal (coverCoordinateRing E ell M true)) (hw : w.IsMaximal) :
    ramificationIndex (normalization_base_signed_le E ell M) w *
      ramificationMultiplicity (normalizationField_signed_le_unsigned E ell M) w =
        ramificationMultiplicity (normalizationField_signed_le_unsigned E 1 ⊥)
          (w.comap (ringMap (normalization_base_signed_le E ell M))) := by
  have : w.IsMaximal := hw
  let hAB := normalizationField_signed_le_unsigned E 1 ⊥
  let hAC := normalization_base_signed_le E ell M
  let hBD := normalization_base_unsigned_le E ell M
  let hCD := normalizationField_signed_le_unsigned E ell M
  obtain ⟨q, hq, hqw⟩ := normalization_exists_maximal_over hCD w hw
  have : q.IsMaximal := hq
  have : q.LiesOver w := ⟨hqw.symm⟩
  have htop : ramificationMultiplicity hCD w = ramificationIndex hCD q :=
    signedNormalizationMultiplicity_eq_ramificationIdx E ell M w q
  let v := q.comap (ringMap hBD)
  have : v.IsMaximal := normalization_comap_isMaximal hBD q hq
  have : v.LiesOver (w.comap (ringMap hAC)) := ⟨by
    rw [← hqw]
    rfl⟩
  have hbase : ramificationMultiplicity hAB (w.comap (ringMap hAC)) =
      ramificationIndex hAB v :=
    signedNormalizationMultiplicity_eq_ramificationIdx E 1 ⊥ _ v
  have hsquare := ramificationIndex_square (transcendental_xG E) hAB hAC hBD hCD q
  have hunsigned : ramificationIndex hBD q = 1 :=
    unsignedNormalization_ramificationIdx_one E ell M q hq
  rw [hqw, hunsigned, mul_one] at hsquare
  exact (congrArg (fun n => ramificationIndex hAC w * n) htop).trans
    (hsquare.trans hbase.symm)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
