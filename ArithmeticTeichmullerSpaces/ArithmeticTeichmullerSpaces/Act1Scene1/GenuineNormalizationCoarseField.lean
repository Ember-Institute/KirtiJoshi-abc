import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization

/-!
source-id: JT-SCENE1-INITIAL-THETA-COARSE-FIELD-IDENTIFICATION
source: `refer/iut/Iut/Anabelian/Genuine/Realize.lean`, `fullSub` and `coarseField`;
`ReferenceIut/Iut/Anabelian/Genuine/Normalization.lean`.
fidelity: proves that the actual fixed field transported to the x-line is the same
fixed field used by the reference realization. The proof uses the equality of
Galois bases and does not assume an orbicurve or covering law.
boundary: Scene1/Derived.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)
  [E.IsElliptic]

private def galEquivOfEq {F F' : IntermediateField k (Ω E)} (h : F = F') :
    (Ω E ≃ₐ[F] Ω E) ≃* (Ω E ≃ₐ[F'] Ω E) := by
  subst F'
  exact MulEquiv.refl _

private def galHom : (Ω E ≃ₐ[xLine E] Ω E) →* (Ω E ≃ₐ[baseField E] Ω E) :=
  (galEquivOfEq E (baseField_eq_xLine E)).symm.toMonoidHom

private lemma galEquivOfEq_apply {F F' : IntermediateField k (Ω E)}
    (h : F = F') (σ : Ω E ≃ₐ[F] Ω E) (x : Ω E) :
    galEquivOfEq E h σ x = σ x := by
  subst F'
  rfl

private lemma galEquivOfEq_symm_apply {F F' : IntermediateField k (Ω E)}
    (h : F = F') (σ : Ω E ≃ₐ[F'] Ω E) (x : Ω E) :
    (galEquivOfEq E h).symm σ x = σ x := by
  subst F'
  rfl

private lemma galHom_apply (σ : Ω E ≃ₐ[xLine E] Ω E) (x : Ω E) :
    galHom E σ x = σ x := by
  change (galEquivOfEq E (baseField_eq_xLine E)).symm σ x = σ x
  exact galEquivOfEq_symm_apply E (baseField_eq_xLine E) σ x

private lemma galEquiv_apply (σ : Ω E ≃ₐ[baseField E] Ω E) (x : Ω E) :
    galEquivOfEq E (baseField_eq_xLine E) σ x = σ x := by
  exact galEquivOfEq_apply E (baseField_eq_xLine E) σ x

private lemma galHom_galEquiv (σ : Ω E ≃ₐ[baseField E] Ω E) :
    galHom E (galEquivOfEq E (baseField_eq_xLine E) σ) = σ := by
  exact (galEquivOfEq E (baseField_eq_xLine E)).symm_apply_apply σ

/-- The subgroup fixing the coarse realization field, transported to the x-line. -/
def fullSubOnXLine (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Subgroup (Ω E ≃ₐ[xLine E] Ω E) :=
  (Hgp E ell M pm).comap (galHom E)

/-- The coarse function field of the model orbicurve. -/
def coarseFieldOnXLine (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IntermediateField (xLine E) (Ω E) :=
  IntermediateField.fixedField (fullSubOnXLine E ell M pm)

/-- The normalization field and the coarse field have the same underlying subfield of `Ω`. -/
theorem normalizationField_eq_coarseFieldOnXLine
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    normalizationField E ell M pm = coarseFieldOnXLine E ell M pm := by
  ext x
  rw [mem_normalizationField]
  change x ∈ IntermediateField.fixedField (Hgp E ell M pm) ↔
    x ∈ IntermediateField.fixedField (fullSubOnXLine E ell M pm)
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx σ hσ
    simpa only [galHom_apply] using hx (galHom E σ) hσ
  · intro hx σ hσ
    have hfix := hx (galEquivOfEq E (baseField_eq_xLine E) σ) ?_
    · simpa only [galEquiv_apply] using hfix
    · change galHom E (galEquivOfEq E (baseField_eq_xLine E) σ) ∈ Hgp E ell M pm
      rw [galHom_galEquiv]
      exact hσ

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
