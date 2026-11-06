import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotientNontrivial
import Mathlib.FieldTheory.LinearDisjoint

/-!
source-id: JT-SCENE1-GENUINE-SIGNED-LINEAR-DISJOINT
source: IUT I Definition 3.1(d), the Cartesian covering diagram;
Joshi III `ss:theta-data-fixing2`; Mathlib
`IntermediateField.LinearDisjoint.of_finrank_sup`.
fidelity: the actual signed covering field and original unsigned elliptic
field are linearly disjoint over the actual x-line. Their compositum is the
original unsigned covering field, and its degree over the x-line is twice
the signed covering degree. The proof uses the established ambient negation
and exact signed quotient order; no degree or disjointness law is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. These are function-field results. Injectivity of
the normalization-ring tensor map, normality of that tensor ring, orbicurve
realization, the Cartesian covering law and the full producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
noncomputable section
universe u
variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] signedFieldAlgebra signedField_finiteDimensional

local instance linearDisjointSignedFieldModule (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  @Algebra.toModule _ _ _ _ (signedFieldAlgebra E ell M)

local instance actualSignedFieldTower (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    IsScalarTower (baseField E) (stabilizerField E ell M true)
      (stabilizerField E ell M false) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance linearDisjointBaseFieldFree (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Module.Free (baseField E) (stabilizerField E ell M pm) :=
  Module.Free.of_divisionRing _ _

local instance linearDisjointSignedFieldFree (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    Module.Free (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  Module.Free.of_divisionRing _ _

/-- The signed base field is exactly the coefficient x-line. -/
theorem stabilizerField_one_signed_eq_bot : stabilizerField E 1 ⊥ true = ⊥ := by
  rw [stabilizerField, Hgp_one_bot_true, ← IntermediateField.fixingSubgroup_bot,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- The original elliptic function field is quadratic over the x-line. -/
theorem stabilizerField_one_unsigned_finrank :
    Module.finrank (baseField E) (stabilizerField E 1 ⊥ false) = 2 := by
  have hbase : Module.finrank (baseField E) (stabilizerField E 1 ⊥ true) = 1 := by
    rw [stabilizerField_one_signed_eq_bot]
    exact IntermediateField.finrank_bot
  have h := Module.finrank_mul_finrank (baseField E)
    (stabilizerField E 1 ⊥ true) (stabilizerField E 1 ⊥ false)
  rw [hbase, signedField_finrank_eq_two, one_mul] at h
  exact h.symm

/-- Removing the sign doubles the actual covering degree over the x-line. -/
theorem stabilizerField_unsigned_finrank (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.finrank (baseField E) (stabilizerField E ell M false) =
      Module.finrank (baseField E) (stabilizerField E ell M true) * 2 := by
  rw [← Module.finrank_mul_finrank (baseField E) (stabilizerField E ell M true)
    (stabilizerField E ell M false), signedField_finrank_eq_two]

/-- The signed covering and original elliptic field introduce independent extensions. -/
theorem stabilizerFields_signed_linearDisjoint (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    (stabilizerField E ell M true).LinearDisjoint (stabilizerField E 1 ⊥ false) := by
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [← stabilizerField_unsigned_eq_sup E ell M, stabilizerField_unsigned_finrank,
    stabilizerField_one_unsigned_finrank]

/-- The same independence holds for the actual normalization fields over the x-line. -/
theorem normalizationFields_signed_linearDisjoint (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    (normalizationField E ell M true).LinearDisjoint (normalizationField E 1 ⊥ false) := by
  have hrebase {B B' : IntermediateField k (Ω E)} (h : B = B')
      (F Z : IntermediateField B (Ω E)) (hFZ : F.LinearDisjoint Z) :
      (FunctionFieldNormalization.rebaseField h F).LinearDisjoint
        (FunctionFieldNormalization.rebaseField h Z) := by
    subst B'
    exact hFZ
  exact hrebase (baseField_eq_xLine E) _ _ (stabilizerFields_signed_linearDisjoint E ell M)

/-- The two normalization fields share only their x-line. -/
theorem normalizationFields_signed_inf_eq_bot (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    normalizationField E ell M true ⊓ normalizationField E 1 ⊥ false = ⊥ :=
  (normalizationFields_signed_linearDisjoint E ell M).inf_eq_bot

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
