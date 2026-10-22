/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbifold/GaloisData.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `89c37fa8bf42349a5e14b6ca81375edbf50d72ec`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package Apache-2.0 LICENSE; the source has no
copyright header and the package has no NOTICE file.
modification: adapts `CoordRing.mem_fixingSubgroup_of_forall` and the coordinate
ring action. Uses Mathlib's integral-closure restriction, proves the exact
kernel and faithful quotient action, and fixes the signed normalization image.
No reference package is imported.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedFieldAction
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`Pi1/Orbifold/GaloisData.lean`, coordinate-ring action and fraction-field argument.
fidelity: the same signed quotient acts faithfully on the actual unsigned
normalization ring and fixes the actual signed normalization inclusion.
boundary: Scene1/Derived. Full automorphism-group identification, etaleness,
orbicurve realization and ramification-stabilizer identities remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
attribute [local instance] signedFieldAlgebra

private lemma fixes_polynomialBase (g : Gal E)
    (a : FunctionFieldNormalization.polynomialBase k (xG E)) : g a.val = a.val := by
  have h : Algebra.adjoin k {xG E} ≤ (baseField E).toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact xG_mem_baseField E
  exact g.commutes ⟨a.val, h a.property⟩

/-- The actual field action preserves the polynomial base used for normalization. -/
def signedNormalizationFieldAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (g : Hgp E ell M true) :
    normalizationField E ell M false ≃ₐ[FunctionFieldNormalization.polynomialBase k (xG E)]
      normalizationField E ell M false where
  toRingEquiv := (signedFieldAut E ell M g).toRingEquiv
  commutes' a := Subtype.ext (fixes_polynomialBase E g.val a)

/-- Restrict the signed field action to the actual integral closure. -/
def signedNormalizationAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Hgp E ell M true →*
      RingAut (coverCoordinateRing E ell M false) where
  toFun g := (signedNormalizationFieldAut E ell M g).mapIntegralClosure.toRingEquiv
  map_one' := RingEquiv.ext fun _x => Subtype.ext (Subtype.ext rfl)
  map_mul' _g _h := RingEquiv.ext fun _x => Subtype.ext (Subtype.ext rfl)

@[simp] lemma coe_signedNormalizationAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (g : Hgp E ell M true) (x : coverCoordinateRing E ell M false) :
    (((signedNormalizationAut E ell M g x : coverCoordinateRing E ell M false) :
      normalizationField E ell M false) : Ω E) = g.val x.val.val := rfl

/-- The fraction-field identity detects the kernel on the normalization ring. -/
theorem signedNormalizationAut_ker (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (signedNormalizationAut E ell M).ker =
      (Hgp E ell M false).subgroupOf (Hgp E ell M true) := by
  ext g
  change signedNormalizationAut E ell M g = 1 ↔ g.val ∈ Hgp E ell M false
  constructor
  · intro h
    have hfix : g.val ∈ (stabilizerField E ell M false).fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      intro x hx
      have hg (a : coverCoordinateRing E ell M false) : g.val a.val.val = a.val.val :=
        congrArg (fun z : coverCoordinateRing E ell M false => z.val.val)
          (RingEquiv.congr_fun h a)
      obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective
        (A := coverCoordinateRing E ell M false) (⟨x, hx⟩ : normalizationField E ell M false)
      have hx' := congrArg (fun z : normalizationField E ell M false => (z : Ω E)) hab
      change a.val.val / b.val.val = x at hx'
      rw [← hx', map_div₀, hg a, hg b]
    rwa [fixingSubgroup_stabilizerField] at hfix
  · intro h
    have hfix : g.val ∈ (stabilizerField E ell M false).fixingSubgroup :=
      (fixingSubgroup_stabilizerField E ell M false).symm ▸ h
    have hpoint := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix
    exact RingEquiv.ext fun x => Subtype.ext (Subtype.ext (hpoint x.val.val x.val.property))

/-- The signed quotient acts on the unsigned normalization ring. -/
def signedQuotientNormalizationAut (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    letI := Hgp_false_normal E ell M true
    Hgp E ell M true ⧸ (Hgp E ell M false).subgroupOf (Hgp E ell M true) →*
      RingAut (coverCoordinateRing E ell M false) := by
  letI := Hgp_false_normal E ell M true
  exact QuotientGroup.lift _ (signedNormalizationAut E ell M)
    (signedNormalizationAut_ker E ell M).ge

theorem signedQuotientNormalizationAut_injective (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    Function.Injective (signedQuotientNormalizationAut E ell M) := by
  let := Hgp_false_normal E ell M true
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr (signedNormalizationAut_ker E ell M).symm

/-- The action fixes the image of the actual signed normalization inclusion. -/
theorem signedQuotientNormalizationAut_fixed_signed (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    letI := Hgp_false_normal E ell M true
    ∀ q, ∀ a : coverCoordinateRing E ell M true,
      signedQuotientNormalizationAut E ell M q (signedNormalizationRingMap E ell M a) =
        signedNormalizationRingMap E ell M a := by
  let := Hgp_false_normal E ell M true
  intro q a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
  apply Subtype.ext
  apply Subtype.ext
  exact (IntermediateField.mem_fixedField_iff (Hgp E ell M true) a.val.val).mp
    a.val.property g.val g.property

/-- The quotient-fixed elements of the unsigned normalization ring. -/
def signedNormalizationInvariant (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (x : coverCoordinateRing E ell M false) :
    letI := Hgp_false_normal E ell M true
    Prop := by
  letI := Hgp_false_normal E ell M true
  exact ∀ q, signedQuotientNormalizationAut E ell M q x = x

@[simp] lemma coe_signedQuotientNormalizationAut_mk
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (g : Hgp E ell M true) (x : coverCoordinateRing E ell M false) :
    letI := Hgp_false_normal E ell M true
    (((signedQuotientNormalizationAut E ell M (QuotientGroup.mk' _ g) x :
      coverCoordinateRing E ell M false) : normalizationField E ell M false) : Ω E) =
      g.val x.val.val := rfl

/-- The invariant ring is exactly the signed normalization image. -/
theorem signedNormalizationInvariant_iff
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (x : coverCoordinateRing E ell M false) :
    letI := Hgp_false_normal E ell M true
    signedNormalizationInvariant E ell M x ↔
      ∃ a : coverCoordinateRing E ell M true,
        signedNormalizationRingMap E ell M a = x := by
  letI := Hgp_false_normal E ell M true
  constructor
  · intro hx
    have hpoint : ∀ g : Hgp E ell M true, g.val x.val.val = x.val.val := by
      intro g
      have h := congrArg (fun z : coverCoordinateRing E ell M false =>
        (z.val.val : Ω E)) (hx (QuotientGroup.mk' _ g))
      exact h
    have hfield : x.val.val ∈ stabilizerField E ell M true := by
      rw [stabilizerField, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact hpoint ⟨g, hg⟩
    have hi : IsIntegral (FunctionFieldNormalization.polynomialBase k (xG E))
        x.val.val := by
      let f : normalizationField E ell M false →ₐ[
          FunctionFieldNormalization.polynomialBase k (xG E)] Ω E :=
        (IntermediateField.val (normalizationField E ell M false)).restrictScalars _
      apply (isIntegral_algHom_iff f f.injective).mpr
      exact x.property
    let y : normalizationField E ell M true := ⟨x.val.val, hfield⟩
    have hiy : IsIntegral (FunctionFieldNormalization.polynomialBase k (xG E)) y := by
      let f : normalizationField E ell M true →ₐ[
          FunctionFieldNormalization.polynomialBase k (xG E)] Ω E :=
        (IntermediateField.val (normalizationField E ell M true)).restrictScalars _
      apply (isIntegral_algHom_iff f f.injective).mp
      exact hi
    let a : coverCoordinateRing E ell M true := ⟨y, hiy⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · rintro ⟨a, rfl⟩
    intro q
    exact signedQuotientNormalizationAut_fixed_signed E ell M q a

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
