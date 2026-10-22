/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbifold/GaloisData.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `89c37fa8bf42349a5e14b6ca81375edbf50d72ec`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package Apache-2.0 LICENSE; the source has no
copyright header and the package has no NOTICE file.
modification: specializes `Coord.mem_fixedField_of_normalizes` to the actual
signed/unsigned torsion subgroups. Constructs field automorphisms over the
signed fixed field and proves the exact kernel and faithful quotient action.
No reference package is imported.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`Pi1/Orbifold/GaloisData.lean`, `Coord.mem_fixedField_of_normalizes`.
fidelity: the signed quotient acts faithfully on the actual unsigned fixed
field over the actual signed fixed field, using their proved inclusion.
boundary: Scene1/Derived. Surjectivity onto all field automorphisms,
normalization-cover automorphisms and ramification stabilizers remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Signed automorphisms preserve the actual unsigned fixed field. -/
lemma signed_mem_unsignedField {ell : ℕ} {M : AddSubgroup E.toAffine.Point}
    {g : Gal E} (hg : g ∈ Hgp E ell M true) {x : Ω E}
    (hx : x ∈ stabilizerField E ell M false) :
    g x ∈ stabilizerField E ell M false := by
  rw [stabilizerField, IntermediateField.mem_fixedField_iff] at hx ⊢
  intro n hn
  have h := hx _ (conj_mem_Hgp_false E ((Hgp E ell M true).inv_mem hg) hn)
  simp only [inv_inv, AlgEquiv.mul_apply] at h
  calc n (g x) = g ((g⁻¹ : Gal E) (n (g x))) := by simp
    _ = g x := by rw [h]

/-- The algebra structure is the proved inclusion of these two fixed fields. -/
@[instance_reducible] def signedFieldAlgebra (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra (stabilizerField E ell M true) (stabilizerField E ell M false) :=
  (IntermediateField.inclusion (stabilizerField_signed_le_unsigned E ell M)).toAlgebra

attribute [local instance] signedFieldAlgebra

/-- Restrict the signed ambient action to the unsigned field over the signed field. -/
def signedFieldAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Hgp E ell M true →*
      (stabilizerField E ell M false ≃ₐ[stabilizerField E ell M true]
        stabilizerField E ell M false) where
  toFun g :=
    { toFun := fun x => ⟨g.val x.val, signed_mem_unsignedField E g.property x.property⟩
      invFun := fun x => ⟨g.val⁻¹ x.val,
        signed_mem_unsignedField E ((Hgp E ell M true).inv_mem g.property) x.property⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul g.val x.val y.val)
      map_add' := fun x y => Subtype.ext (map_add g.val x.val y.val)
      commutes' := fun x => Subtype.ext (by
        change g.val x.val = x.val
        exact (IntermediateField.mem_fixedField_iff (Hgp E ell M true) (x : Ω E)).mp
          x.property g.val g.property) }
  map_one' := AlgEquiv.ext fun x => Subtype.ext rfl
  map_mul' g h := AlgEquiv.ext fun x => Subtype.ext rfl

@[simp] lemma coe_signedFieldAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (g : Hgp E ell M true) (x : stabilizerField E ell M false) :
    ((signedFieldAut E ell M g x : stabilizerField E ell M false) : Ω E) =
      g.val x.val := rfl

/-- Exactly the unsigned subgroup acts trivially on the unsigned fixed field. -/
theorem signedFieldAut_ker (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (signedFieldAut E ell M).ker = (Hgp E ell M false).subgroupOf (Hgp E ell M true) := by
  ext g
  change signedFieldAut E ell M g = 1 ↔ g.val ∈ Hgp E ell M false
  rw [← fixingSubgroup_stabilizerField E ell M false,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (AlgEquiv.congr_fun h ⟨x, hx⟩)
  · intro h
    exact AlgEquiv.ext fun x => Subtype.ext (h x.val x.property)

/-- Descend the actual field action to the signed/unsigned quotient. -/
def signedQuotientFieldAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    letI := Hgp_false_normal E ell M true
    Hgp E ell M true ⧸ (Hgp E ell M false).subgroupOf (Hgp E ell M true) →*
      (stabilizerField E ell M false ≃ₐ[stabilizerField E ell M true]
        stabilizerField E ell M false) := by
  letI := Hgp_false_normal E ell M true
  exact QuotientGroup.lift _ (signedFieldAut E ell M) (signedFieldAut_ker E ell M).ge

theorem signedQuotientFieldAut_injective (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Function.Injective (signedQuotientFieldAut E ell M) := by
  let := Hgp_false_normal E ell M true
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr (signedFieldAut_ker E ell M).symm

@[simp] lemma signedQuotientFieldAut_mk (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (g : Hgp E ell M true) :
    letI := Hgp_false_normal E ell M true
    signedQuotientFieldAut E ell M (QuotientGroup.mk g) = signedFieldAut E ell M g := rfl

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
