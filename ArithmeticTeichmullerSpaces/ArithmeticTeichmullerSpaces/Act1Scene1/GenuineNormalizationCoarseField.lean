import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Orbifold

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
  change x ∈ IntermediateField.fixedField (Hgp E ell M pm) ↔ _
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx σ hσ
    simpa only [galEquiv_symm_apply] using hx (galHom E σ) hσ
  · intro hx σ hσ
    have hfix := hx (galEquiv E σ) ?_
    · simpa only [galEquiv_apply] using hfix
    · change galHom E (galEquiv E σ) ∈ Hgp E ell M pm
      rw [galHom_galEquiv]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
