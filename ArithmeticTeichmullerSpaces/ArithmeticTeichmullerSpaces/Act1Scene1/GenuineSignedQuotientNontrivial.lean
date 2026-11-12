import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldBaseNegation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedCompositum
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedGalois

/-!
source-id: JT-SCENE1-GENUINE-SIGNED-QUOTIENT-NONTRIVIAL
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`,
the signed quotient of the actual division-point covering.
fidelity: uses a base-field-linear ambient extension of the original
division-field negation to produce an element in the signed subgroup
outside its unsigned subgroup. Thus the existing relative index, signed
Galois quotient order and fixed-field extension degree are exactly two
for the original level and torsion subgroup. No sign witness is assumed.
Original proofs; no reference implementation copied.
boundary: this is a statement about the existing actual function fields
and groups. The orbicurve realization, etale fundamental-group comparison,
Cartesian covering and full InitialThetaGeometryProducer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
noncomputable section
universe u
variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] signedFieldAlgebra

local instance actualSignedFieldModule (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  @Algebra.toModule _ _ _ _ (signedFieldAlgebra E ell M)

/-- Negation gives an actual signed element that is not a translation. -/
theorem exists_signed_not_unsigned (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    ∃ σ : Gal E, σ ∈ Hgp E ell M true ∧ σ ∉ Hgp E ell M false := by
  obtain ⟨σ, hσ⟩ := exists_ambient_divisionPoint_negation E
    (effLevel ell) (effLevel_pos ell)
  have hlevel : effLevel (effLevel ell) = effLevel ell :=
    if_neg (Nat.ne_of_gt (effLevel_pos ell))
  have hQ : Qpt E (effLevel ell) = Qpt E ell := congrArg (divSys E) hlevel
  rw [hQ] at hσ
  have ht : act E σ (Qpt E ell) - (-1 : ℤ) • Qpt E ell ∈ Mbar E ell M := by
    rw [hσ, neg_one_zsmul, sub_self]
    exact zero_mem _
  refine ⟨σ, ⟨-1, Or.inr ⟨rfl, rfl⟩, ht⟩, ?_⟩
  intro hu
  have hneg : act E σ (genericPoint E) = -genericPoint E := by
    simpa only [neg_one_zsmul] using act_generic_eq_sign E ht
  exact genericPoint_ne_neg E ((act_generic_of_unsigned E hu).symm.trans hneg)

/-- The actual signed/unsigned relative index is two, rather than merely a divisor of two. -/
theorem Hgp_false_relIndex_eq_two (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (Hgp E ell M false).relIndex (Hgp E ell M true) = 2 := by
  obtain ⟨σ, hs, hn⟩ := exists_signed_not_unsigned E ell M
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨σ, hs, hn, ?_⟩
  intro τ hτ
  by_cases hu : τ ∈ Hgp E ell M false
  · exact Or.inr hu
  · exact Or.inl (Hgp_mul_mem_false_of_not_mem E hτ hs hu hn)

/-- The existing quotient group has precisely the two sign classes. -/
theorem signedGaloisGroup_card_eq_two (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Nat.card (signedGaloisGroup E ell M) = 2 :=
  Hgp_false_relIndex_eq_two E ell M

/-- The actual unsigned fixed field is quadratic over the signed fixed field. -/
theorem signedField_finrank_eq_two (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.finrank (stabilizerField E ell M true) (stabilizerField E ell M false) = 2 := by
  rw [signedField_finrank_eq_card, signedGaloisGroup_card_eq_two]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
