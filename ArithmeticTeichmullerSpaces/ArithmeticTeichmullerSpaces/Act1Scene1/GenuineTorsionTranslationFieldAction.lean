import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineTorsionTranslationQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved torsion-translation displacement kernel and the actual fixed fields.
fidelity: restricts the actual ambient automorphisms in the full translation
subgroup to the line-translation fixed field. The exact kernel is the proved
line subgroup, so the quotient acts faithfully over the full-translation fixed
field. No new normalization, ramification, or geometry law is supplied.
boundary: Scene1/Derived; this is the actual field action, before any boundary
or cusp comparison. Original proof following the existing signed-action proof.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Inclusion of the actual line-translation subgroup in the full translation subgroup. -/
private theorem torsionTranslationLine_le (n : ℕ) (TK M : AddSubgroup E.toAffine.Point)
    (hM : M ≤ TK) : Hgp E n M false ≤ Hgp E n TK false :=
  Hgp_le E (n := 1) Nat.one_pos (one_mul n)
    (fun P hP => by simpa only [one_nsmul] using hM hP) (fun h => h)

private theorem torsionTranslationField_le (n : ℕ) (TK M : AddSubgroup E.toAffine.Point)
    (hM : M ≤ TK) :
    stabilizerField E n TK false ≤ stabilizerField E n M false :=
  IntermediateField.fixedField_antitone (torsionTranslationLine_le E n TK M hM)

private theorem torsionTranslation_conj_mem (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK)
    {g a : Gal E} (hg : g ∈ Hgp E n TK false) (ha : a ∈ Hgp E n M false) :
    g * a * g⁻¹ ∈ Hgp E n M false :=
  (Subgroup.normal_subgroupOf_iff (torsionTranslationLine_le E n TK M hM)).mp
    (torsionTranslationKernel_normal E n hn TK hTK M hM) a g ha hg

private theorem torsionTranslation_mem_lineField (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK)
    {g : Gal E} (hg : g ∈ Hgp E n TK false) {x : Ω E}
    (hx : x ∈ stabilizerField E n M false) :
    g x ∈ stabilizerField E n M false := by
  rw [stabilizerField, IntermediateField.mem_fixedField_iff] at hx ⊢
  intro a ha
  have h := hx _ (torsionTranslation_conj_mem E n hn TK hTK M hM
    ((Hgp E n TK false).inv_mem hg) ha)
  simp only [inv_inv, AlgEquiv.mul_apply] at h
  calc a (g x) = g ((g⁻¹ : Gal E) (a (g x))) := by simp
    _ = g x := by rw [h]

/-- The actual inclusion algebra for the two translation fixed fields. -/
@[instance_reducible] def torsionTranslationFieldAlgebra (n : ℕ)
    (TK : AddSubgroup E.toAffine.Point)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
  (IntermediateField.inclusion (torsionTranslationField_le E n TK M hM)).toAlgebra

/-- Ambient translation automorphisms restrict to the line fixed field. -/
def torsionTranslationFieldAut (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationFieldAlgebra E n TK M hM
    Hgp E n TK false →*
      (stabilizerField E n M false ≃ₐ[stabilizerField E n TK false]
        stabilizerField E n M false) := by
  letI := torsionTranslationFieldAlgebra E n TK M hM
  refine {
    toFun := fun g => {
      toFun := fun x => ⟨g.val x.val,
        torsionTranslation_mem_lineField E n hn TK hTK M hM g.property x.property⟩
      invFun := fun x => ⟨g.val⁻¹ x.val,
        torsionTranslation_mem_lineField E n hn TK hTK M hM
          ((Hgp E n TK false).inv_mem g.property) x.property⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul g.val x.val y.val)
      map_add' := fun x y => Subtype.ext (map_add g.val x.val y.val)
      commutes' := fun x => Subtype.ext (by
        change g.val x.val = x.val
        exact (IntermediateField.mem_fixedField_iff (Hgp E n TK false) (x : Ω E)).mp
          x.property g.val g.property) }
    map_one' := AlgEquiv.ext fun x => Subtype.ext rfl
    map_mul' g h := AlgEquiv.ext fun x => Subtype.ext rfl }

@[simp] theorem coe_torsionTranslationFieldAut
    (n : ℕ) (hn : 0 < n) (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK)
    (g : Hgp E n TK false) (x : stabilizerField E n M false) :
    letI := torsionTranslationFieldAlgebra E n TK M hM
    ((torsionTranslationFieldAut E n hn TK hTK M hM g x :
      stabilizerField E n M false) : Ω E) = g.val x.val := rfl

/-- The kernel is exactly the original line-translation subgroup. -/
theorem torsionTranslationFieldAut_ker (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationFieldAlgebra E n TK M hM
    (torsionTranslationFieldAut E n hn TK hTK M hM).ker =
      (Hgp E n M false).subgroupOf (Hgp E n TK false) := by
  letI := torsionTranslationFieldAlgebra E n TK M hM
  ext g
  change torsionTranslationFieldAut E n hn TK hTK M hM g = 1 ↔
    g.val ∈ Hgp E n M false
  rw [← fixingSubgroup_stabilizerField E n M false,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (AlgEquiv.congr_fun h ⟨x, hx⟩)
  · intro h
    exact AlgEquiv.ext fun x => Subtype.ext (h x.val x.property)

/-- The actual quotient acts over the full-translation fixed field. -/
def torsionTranslationQuotientFieldAut (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI := torsionTranslationFieldAlgebra E n TK M hM
    Hgp E n TK false ⧸ (Hgp E n M false).subgroupOf (Hgp E n TK false) →*
      (stabilizerField E n M false ≃ₐ[stabilizerField E n TK false]
        stabilizerField E n M false) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI := torsionTranslationFieldAlgebra E n TK M hM
  exact QuotientGroup.lift _ (torsionTranslationFieldAut E n hn TK hTK M hM)
    (torsionTranslationFieldAut_ker E n hn TK hTK M hM).ge

theorem torsionTranslationQuotientFieldAut_injective (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI := torsionTranslationFieldAlgebra E n TK M hM
    Function.Injective (torsionTranslationQuotientFieldAut E n hn TK hTK M hM) :=
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI := torsionTranslationFieldAlgebra E n TK M hM
  (QuotientGroup.injective_lift_iff _ _ _).mpr
    (torsionTranslationFieldAut_ker E n hn TK hTK M hM).symm

@[simp] theorem torsionTranslationQuotientFieldAut_mk (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) (g : Hgp E n TK false) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI := torsionTranslationFieldAlgebra E n TK M hM
    torsionTranslationQuotientFieldAut E n hn TK hTK M hM (QuotientGroup.mk g) =
      torsionTranslationFieldAut E n hn TK hTK M hM g := rfl

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
