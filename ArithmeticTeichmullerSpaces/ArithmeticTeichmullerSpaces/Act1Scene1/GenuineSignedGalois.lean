import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedFieldAction
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib `IsGaloisGroup.isGalois`, `finiteDimensional`, `mulEquivAlgEquiv`.
fidelity: identifies the actual signed quotient with all automorphisms of the
unsigned fixed field over the signed fixed field. Proves that this extension
is finite Galois and that its degree equals the quotient order, which divides two.
boundary: Scene1/Derived. This does not prove an orbicurve realization,
etale covering comparison or ramification-stabilizer identity.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

local instance unsignedNormal (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    ((Hgp E ell M false).subgroupOf (Hgp E ell M true)).Normal :=
  Hgp_false_normal E ell M true

/-- The quotient of the actual signed subgroup by its unsigned subgroup. -/
abbrev signedGaloisGroup (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :=
  Hgp E ell M true ⧸ (Hgp E ell M false).subgroupOf (Hgp E ell M true)

theorem finite_signedGaloisGroup (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Finite (signedGaloisGroup E ell M) := by
  apply Nat.finite_of_card_ne_zero
  have hdvd : Nat.card (signedGaloisGroup E ell M) ∣ 2 := Hgp_false_relIndex_dvd_two E ell M
  exact (Nat.pos_of_dvd_of_pos hdvd (by decide)).ne'

attribute [local instance] signedFieldAlgebra finite_signedGaloisGroup

local instance signedFieldModule (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  @Algebra.toModule _ _ _ _ (signedFieldAlgebra E ell M)

local instance signedFieldFaithfulSMul (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    FaithfulSMul (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  (faithfulSMul_iff_algebraMap_injective
    (stabilizerField E ell M true) (stabilizerField E ell M false)).mpr
      (algebraMap (stabilizerField E ell M true) (stabilizerField E ell M false)).injective

/-- Use the proved quotient homomorphism for the field action. -/
@[instance_reducible] def signedGaloisFieldAction (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    MulSemiringAction (signedGaloisGroup E ell M) (stabilizerField E ell M false) :=
  MulSemiringAction.compHom _ (signedQuotientFieldAut E ell M)

attribute [local instance] signedGaloisFieldAction

/-- Faithfulness and the exact fixed field hold for this actual action. -/
@[instance_reducible] def signedFieldGaloisGroup (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    IsGaloisGroup (signedGaloisGroup E ell M)
      (stabilizerField E ell M true) (stabilizerField E ell M false) where
  faithful := ⟨fun h => signedQuotientFieldAut_injective E ell M (AlgEquiv.ext h)⟩
  commutes := ⟨fun g a x => by
    change (signedQuotientFieldAut E ell M g) (a • x) =
      a • ((signedQuotientFieldAut E ell M g) x)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]⟩
  isInvariant := ⟨fun x hx => by
    have hfield : x.val ∈ stabilizerField E ell M true := by
      rw [stabilizerField, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg Subtype.val (hx (QuotientGroup.mk' _ ⟨g, hg⟩))
    exact ⟨⟨x.val, hfield⟩, Subtype.ext rfl⟩⟩

attribute [local instance] signedFieldGaloisGroup

theorem signedField_isGalois (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    IsGalois (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  IsGaloisGroup.isGalois (signedGaloisGroup E ell M) _ _

theorem signedField_finiteDimensional (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    FiniteDimensional (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  IsGaloisGroup.finiteDimensional (signedGaloisGroup E ell M) _ _

/-- Every automorphism over the signed fixed field comes from the signed quotient. -/
theorem signedQuotientFieldAut_surjective (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Function.Surjective (signedQuotientFieldAut E ell M) := by
  intro f
  obtain ⟨q, hq⟩ := (IsGaloisGroup.mulEquivAlgEquiv (signedGaloisGroup E ell M)
    (stabilizerField E ell M true) (stabilizerField E ell M false)).surjective f
  exact ⟨q, AlgEquiv.ext fun x => AlgEquiv.congr_fun hq x⟩

/-- The original field action is the full Galois-group equivalence. -/
def signedFieldGaloisEquiv (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    signedGaloisGroup E ell M ≃*
      (stabilizerField E ell M false ≃ₐ[stabilizerField E ell M true]
        stabilizerField E ell M false) :=
  MulEquiv.ofBijective (signedQuotientFieldAut E ell M)
    ⟨signedQuotientFieldAut_injective E ell M, signedQuotientFieldAut_surjective E ell M⟩

@[simp] theorem signedFieldGaloisEquiv_apply (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (q : signedGaloisGroup E ell M) :
    signedFieldGaloisEquiv E ell M q = signedQuotientFieldAut E ell M q := rfl

theorem signedField_finrank_eq_card (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.finrank (stabilizerField E ell M true) (stabilizerField E ell M false) =
      Nat.card (signedGaloisGroup E ell M) :=
  (IsGaloisGroup.card_eq_finrank (signedGaloisGroup E ell M) _ _).symm

theorem signedField_finrank_dvd_two (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Module.finrank (stabilizerField E ell M true) (stabilizerField E ell M false) ∣ 2 := by
  rw [signedField_finrank_eq_card]
  exact Hgp_false_relIndex_dvd_two E ell M

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
