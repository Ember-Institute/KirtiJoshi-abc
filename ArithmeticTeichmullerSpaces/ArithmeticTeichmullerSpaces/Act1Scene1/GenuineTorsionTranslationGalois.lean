import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineTorsionTranslationFieldAction
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the proved actual torsion-translation quotient action and Mathlib IsGaloisGroup.
fidelity: proves that the actual translation quotient is the full Galois group
of the line fixed field over the full-translation fixed field. Its degree is
the cardinality of the actual torsion quotient. Finiteness follows from the
proved openness of the original Hgp subgroups; no extra finite-carrier or
Galois-source assumption is introduced.
boundary: Scene1/Derived. Normalization action, infinity fibers, cusp comparison,
and the geometry producer are not constructed here.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The quotient of the two original actual translation subgroups. -/
abbrev torsionTranslationGaloisGroup (n : ℕ) (TK M : AddSubgroup E.toAffine.Point) :=
  Hgp E n TK false ⧸ (Hgp E n M false).subgroupOf (Hgp E n TK false)

theorem finite_torsionTranslationGaloisGroup (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    Finite (torsionTranslationGaloisGroup E n TK M) :=
  by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  exact Subgroup.quotient_finite_of_isOpen' (Hgp E n TK false)
    ((Hgp E n M false).subgroupOf (Hgp E n TK false))
    (isOpen_Hgp E n TK false)
    ((isOpen_Hgp E n M false).preimage continuous_subtype_val)

/-- Use the proved quotient action on the actual line fixed field. -/
@[instance_reducible] def torsionTranslationGaloisFieldAction (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  exact MulSemiringAction.compHom _ (torsionTranslationQuotientFieldAut E n hn TK hTK M hM)

/-- The exact fixed field follows from invariance under the same ambient subgroup. -/
theorem torsionTranslationFieldGaloisGroup (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  exact {
  faithful := ⟨fun h => torsionTranslationQuotientFieldAut_injective E n hn TK hTK M hM
    (AlgEquiv.ext h)⟩
  commutes := ⟨fun g a x => by
    change (torsionTranslationQuotientFieldAut E n hn TK hTK M hM g) (a • x) =
      a • ((torsionTranslationQuotientFieldAut E n hn TK hTK M hM g) x)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]⟩
  isInvariant := ⟨fun x hx => by
    have hfield : x.val ∈ stabilizerField E n TK false := by
      rw [stabilizerField, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg Subtype.val (hx (QuotientGroup.mk' _ ⟨g, hg⟩))
    exact ⟨⟨x.val, hfield⟩, Subtype.ext rfl⟩⟩
  }

theorem torsionTranslationField_isGalois (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
      finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    IsGalois (stabilizerField E n TK false) (stabilizerField E n M false) :=
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
    finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  IsGaloisGroup.isGalois (torsionTranslationGaloisGroup E n TK M) _ _

theorem torsionTranslationField_finiteDimensional (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
      finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    FiniteDimensional (stabilizerField E n TK false) (stabilizerField E n M false) :=
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
    finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  IsGaloisGroup.finiteDimensional (torsionTranslationGaloisGroup E n TK M) _ _

/-- The faithful actual quotient action exhausts the field automorphisms. -/
theorem torsionTranslationQuotientFieldAut_surjective (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
      finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    Function.Surjective (torsionTranslationQuotientFieldAut E n hn TK hTK M hM) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
    finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  intro f
  obtain ⟨q, hq⟩ := (IsGaloisGroup.mulEquivAlgEquiv
    (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false)).surjective f
  exact ⟨q, AlgEquiv.ext fun x => AlgEquiv.congr_fun hq x⟩

def torsionTranslationFieldGaloisEquiv (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
      finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    torsionTranslationGaloisGroup E n TK M ≃*
      (stabilizerField E n M false ≃ₐ[stabilizerField E n TK false]
        stabilizerField E n M false) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Finite (torsionTranslationGaloisGroup E n TK M) :=
    finite_torsionTranslationGaloisGroup E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  exact MulEquiv.ofBijective (torsionTranslationQuotientFieldAut E n hn TK hTK M hM)
    ⟨torsionTranslationQuotientFieldAut_injective E n hn TK hTK M hM,
      torsionTranslationQuotientFieldAut_surjective E n hn TK hTK M hM⟩

/-- Degree is the size of the same original translation quotient. -/
theorem torsionTranslationField_finrank_eq_card (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    Module.finrank (stabilizerField E n TK false) (stabilizerField E n M false) =
      Nat.card (torsionTranslationGaloisGroup E n TK M) :=
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  (IsGaloisGroup.card_eq_finrank (torsionTranslationGaloisGroup E n TK M) _ _).symm

/-- The field degree is the cardinality of the actual global torsion quotient TK/M. -/
theorem torsionTranslationField_finrank_eq_card_torsionQuotient (n : ℕ) (hn : 0 < n)
    (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (M : AddSubgroup E.toAffine.Point) (hM : M ≤ TK) :
    letI := torsionTranslationKernel_normal E n hn TK hTK M hM
    letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldAlgebra E n TK M hM
    letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
      @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
    letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n M false) :=
      torsionTranslationGaloisFieldAction E n hn TK hTK M hM
    letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
        (stabilizerField E n TK false) (stabilizerField E n M false) :=
      torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
    Module.finrank (stabilizerField E n TK false) (stabilizerField E n M false) =
      Nat.card (↥TK ⧸ M.addSubgroupOf TK) := by
  letI := torsionTranslationKernel_normal E n hn TK hTK M hM
  letI : Algebra (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldAlgebra E n TK M hM
  letI : Module (stabilizerField E n TK false) (stabilizerField E n M false) :=
    @Algebra.toModule _ _ _ _ (torsionTranslationFieldAlgebra E n TK M hM)
  letI : MulSemiringAction (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n M false) :=
    torsionTranslationGaloisFieldAction E n hn TK hTK M hM
  letI : IsGaloisGroup (torsionTranslationGaloisGroup E n TK M)
      (stabilizerField E n TK false) (stabilizerField E n M false) :=
    torsionTranslationFieldGaloisGroup E n hn TK hTK M hM
  rw [torsionTranslationField_finrank_eq_card E n hn TK hTK M hM]
  change Nat.card (Hgp E n TK false ⧸
    (Hgp E n M false).subgroupOf (Hgp E n TK false)) = _
  exact Hgp_relIndex_eq_card_torsionQuotient E n hn TK hTK M hM

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
