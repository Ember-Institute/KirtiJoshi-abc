/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Punctured.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source notice and Apache-2.0 LICENSE before copying.
No NOTICE file occurs in the reference tree. Retain the original notice below.
modifications: use the actual local normalization fields. Identify the signed
base ring with k[X] as a coefficient algebra, and prove compatibility with the
original unsigned base inclusion. Use the frozen Mathlib integral-map API.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineBaseNormalizationRings

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Punctured.lean, coarseField_one_bot and coarseRingEquiv.
fidelity: the signed level-one field is the actual x-line, and its normalization
ring is k[X]. The resulting equivalences preserve the signed-to-unsigned map.
boundary: Scene1/Derived. This identifies the ordinary base normalization
diagram. The orbicurve comparison, cartesianness, core and producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
attribute [local instance 2000] Classical.propDecidable
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

theorem act_generic_eq_or_neg (σ : Gal E) :
    act E σ (genericPoint E) = genericPoint E ∨ act E σ (genericPoint E) = -genericPoint E := by
  have hx : σ (xG E) = xG E := σ.commutes ⟨_, xG_mem_baseField E⟩
  obtain ⟨h', hact⟩ : ∃ h', act E σ (genericPoint E) =
      Affine.Point.some (σ (xG E)) (σ (yG E)) h' := ⟨_, rfl⟩
  rcases Affine.Y_eq_of_X_eq h'.1 (nonsingular_generic E).1 hx with hy | hy
  · left
    rw [hact, genericPoint]
    congr 1
  · right
    rw [hact, genericPoint, Affine.Point.neg_some]
    congr 1

theorem Hgp_one_bot_true : Hgp E 1 ⊥ true = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rcases act_generic_eq_or_neg E σ with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Qpt_one, h, one_smul, sub_self]
    exact zero_mem _
  · refine ⟨-1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [Qpt_one, h, neg_one_zsmul, sub_neg_eq_add, neg_add_cancel]
    exact zero_mem _

theorem normalizationField_one_signed_eq_bot :
    normalizationField E 1 ⊥ true = ⊥ := by
  have hfield : stabilizerField E 1 ⊥ true = ⊥ := by
    rw [stabilizerField, Hgp_one_bot_true, ← IntermediateField.fixingSubgroup_bot,
      InfiniteGalois.fixedField_fixingSubgroup]
  have hbot {B B' : IntermediateField k (Ω E)} (h : B = B') :
      FunctionFieldNormalization.rebaseField h ⊥ = ⊥ := by
    subst B'
    rfl
  unfold normalizationField
  rw [hfield]
  exact hbot _

theorem signedBaseNormalization_algebraMap_bijective :
    Function.Bijective (algebraMap (Algebra.adjoin k {xG E}) (coverCoordinateRing E 1 ⊥ true)) := by
  refine ⟨fun a b h => Subtype.ext (congrArg (fun c : coverCoordinateRing E 1 ⊥ true =>
    ((c : normalizationField E 1 ⊥ true) : Ω E)) h), ?_⟩
  intro b
  have hb : ((b : normalizationField E 1 ⊥ true) : Ω E) ∈
      (⊥ : IntermediateField (xLine E) (Ω E)) := by
    rw [← normalizationField_one_signed_eq_bot E]
    exact (b : normalizationField E 1 ⊥ true).2
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hb
  have := FunctionFieldNormalization.principalBase (xG E) (transcendental_xG E)
  have : IsScalarTower (Algebra.adjoin k {xG E}) (xLine E) (Ω E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hzint : IsIntegral (Algebra.adjoin k {xG E}) z := by
    have hi : IsIntegral (Algebra.adjoin k {xG E})
        ((b : normalizationField E 1 ⊥ true) : Ω E) :=
      b.2.map ((normalizationField E 1 ⊥ true).val.restrictScalars (Algebra.adjoin k {xG E}))
    rw [← hz] at hi
    exact isIntegral_algebraMap_iff.mp hi
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff
    (R := Algebra.adjoin k {xG E}) (K := xLine E)).mp hzint
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  rw [← hz, ← ha]
  rfl

def signedBasePolynomialAlgEquiv : k[X] ≃ₐ[k] coverCoordinateRing E 1 ⊥ true :=
  (normalizationPolynomialEquiv E).trans
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (Algebra.adjoin k {xG E})
      (coverCoordinateRing E 1 ⊥ true)) (signedBaseNormalization_algebraMap_bijective E))

@[simp] theorem coe_signedBasePolynomialAlgEquiv (p : k[X]) :
    (((signedBasePolynomialAlgEquiv E p : coverCoordinateRing E 1 ⊥ true) :
      normalizationField E 1 ⊥ true) : Ω E) = aeval (xG E) p :=
  coe_normalizationPolynomialEquiv E p

/-- Both base-ring equivalences preserve the original polynomial inclusion. -/
theorem baseNormalizationRingEquiv_square (p : k[X]) :
    polynomialNormalizationRingAlgEquiv E
        (algebraMap k[X] (integralClosure k[X] E.toAffine.FunctionField) p) =
      signedNormalizationRingMap E 1 ⊥ (signedBasePolynomialAlgEquiv E p) := by
  apply Subtype.ext
  apply Subtype.ext
  change ιF E (algebraMap k[X] E.toAffine.FunctionField p) =
    (((signedBasePolynomialAlgEquiv E p : coverCoordinateRing E 1 ⊥ true) :
      normalizationField E 1 ⊥ true) : Ω E)
  exact (ιF_algebraMap_poly E p).trans (coe_signedBasePolynomialAlgEquiv E p).symm

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
