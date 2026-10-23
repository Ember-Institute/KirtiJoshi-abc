import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationFields
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d), the cartesian covering diagram;
Joshi III `ss:theta-data-fixing2`; Mathlib infinite Galois correspondence and
`WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self`.
fidelity: the actual unsigned field is the compositum of the actual signed
field and the original elliptic field. The generic point is not two-torsion.
boundary: Scene1/Derived. This is a function-field identity. The orbicurve
cartesian square, its realization, core and the full producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
attribute [local instance 2000] Classical.propDecidable
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The transcendental generic x-coordinate cannot be a two-torsion root. -/
theorem genericPoint_ne_neg : genericPoint E ≠ -genericPoint E := by
  intro h
  have hP : genericPoint E + genericPoint E = 0 := by
    nth_rw 1 [h]
    exact neg_add_cancel _
  have hr := Affine.Point.isRoot_twoTorsionPolynomial_of_add_self
    (nonsingular_generic E) hP
  let p : k[X] := C 4 * X ^ 3 + C E.b₂ * X ^ 2 + C (2 * E.b₄) * X + C E.b₆
  apply transcendental_xG E
  refine ⟨p, ?_, ?_⟩
  · intro hp
    have hc := congrArg (fun q : k[X] => q.coeff 3) hp
    norm_num [p] at hc
  · have hr' : 4 * xG E ^ 3 + algebraMap k (Ω E) E.b₂ * xG E ^ 2 +
        2 * algebraMap k (Ω E) E.b₄ * xG E + algebraMap k (Ω E) E.b₆ = 0 := by
      simpa only [IsRoot.def, eval_toPoly_twoTorsionPolynomial, baseChange,
        map_b₂, map_b₄, map_b₆] using hr
    simpa only [p, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ofNat] using hr'

/-- The sign in a signed division-point action is also its sign on the generic point. -/
theorem act_generic_eq_sign {ell : ℕ} {M : AddSubgroup E.toAffine.Point}
    {σ : Gal E} {ε : ℤ}
    (hT : act E σ (Qpt E ell) - ε • Qpt E ell ∈ Mbar E ell M) :
    act E σ (genericPoint E) = ε • genericPoint E := by
  have ht := effLevel_nsmul_Mbar E ell M hT
  have hn : effLevel ell • Qpt E ell = genericPoint E :=
    nsmul_divSys E (effLevel ell) (effLevel_pos ell)
  rw [nsmul_sub, ← map_nsmul, smul_comm (effLevel ell) ε, hn] at ht
  exact sub_eq_zero.mp ht

/-- Fixing the original generic point selects exactly the unsigned subgroup. -/
theorem Hgp_unsigned_eq_signed_inf_base (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Hgp E ell M false = Hgp E ell M true ⊓ Hgp E 1 ⊥ false := by
  ext σ
  constructor
  · intro hσ
    exact ⟨Hgp_false_le E ell M true hσ,
      (mem_Hgp_bot_false_iff E 1 σ).mpr (by
        rw [Qpt_one]
        exact act_generic_of_unsigned E hσ)⟩
  · rintro ⟨⟨ε, hε, hT⟩, hbase⟩
    have hg : act E σ (genericPoint E) = genericPoint E := by
      simpa only [Qpt_one] using (mem_Hgp_bot_false_iff E 1 σ).mp hbase
    rcases hε with rfl | ⟨_, rfl⟩
    · exact ⟨1, Or.inl rfl, hT⟩
    · have hn := act_generic_eq_sign E hT
      rw [hg, neg_one_zsmul] at hn
      exact False.elim (genericPoint_ne_neg E hn)

/-- The exact compositum required by the global covering diagram at the field level. -/
theorem stabilizerField_unsigned_eq_sup (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    stabilizerField E ell M false =
      stabilizerField E ell M true ⊔ stabilizerField E 1 ⊥ false := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup
    (stabilizerField E ell M true ⊔ stabilizerField E 1 ⊥ false),
    IntermediateField.fixingSubgroup_sup, fixingSubgroup_stabilizerField,
    fixingSubgroup_stabilizerField, ← Hgp_unsigned_eq_signed_inf_base]
  rfl

/-- Rebasing preserves the compositum because it preserves the underlying subfields. -/
theorem normalizationField_unsigned_eq_sup (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    normalizationField E ell M false =
      normalizationField E ell M true ⊔ normalizationField E 1 ⊥ false := by
  have h := stabilizerField_unsigned_eq_sup E ell M
  have hrebase {B B' : IntermediateField k (Ω E)} (heq : B = B')
      (F L : IntermediateField B (Ω E)) :
      FunctionFieldNormalization.rebaseField heq (F ⊔ L) =
        FunctionFieldNormalization.rebaseField heq F ⊔
          FunctionFieldNormalization.rebaseField heq L := by
    subst B'
    rfl
  unfold normalizationField
  rw [h, hrebase]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
