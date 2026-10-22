/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Homs.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
additional-source: `refer/iut/Iut/Anabelian/Genuine/Cover.lean`, effLevel_smul_Mbar,
commit `7b3756ff3fde46bbd4daa89076fd4bc9c4e60baf` (same author and license).
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source copyright and Apache-2.0 license before
copying. No NOTICE file occurs in the reference tree. Retain the notice below.
modifications: use the proved local prime-inertia theorem and the actual
normalization fields. Build the finite Galois closure of the full division
field. Prove unramifiedness above the level-one unsigned field.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineNormalizationPrimeInertia
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Cover.lean and Genuine/Homs.lean, unsigned generic point and Galois closure.
fidelity: the actual unsigned fields contain the actual level-one elliptic field.
Their full division-coordinate field has an actual finite Galois closure.
boundary: Scene1/Derived. These field identities supply the unramifiedness proof;
no covering, core or producer law is assumed.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
attribute [local instance 2000] Classical.propDecidable
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

omit [CharZero k] [E.IsElliptic] in
lemma effLevel_nsmul_Mbar (ell : ℕ) (M : AddSubgroup E.toAffine.Point) {T : Pt E}
    (hT : T ∈ Mbar E ell M) : effLevel ell • T = 0 := by
  obtain ⟨T₀, ⟨_, hT₀⟩, rfl⟩ := hT
  rw [← map_nsmul, (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀, map_zero]

/-- Unsigned stabilizers fix the actual base-curve generic point. -/
theorem act_generic_of_unsigned {ell : ℕ} {M : AddSubgroup E.toAffine.Point} {σ : Gal E}
    (hσ : σ ∈ Hgp E ell M false) : act E σ (genericPoint E) = genericPoint E := by
  obtain ⟨ε, hε, hT⟩ := hσ
  have hε1 : ε = 1 := by
    rcases hε with h | ⟨h, _⟩
    · exact h
    · cases h
  subst ε
  have hT' : act E σ (Qpt E ell) - Qpt E ell ∈ Mbar E ell M := by
    simpa only [one_smul] using hT
  have ht := effLevel_nsmul_Mbar E ell M hT'
  have hnQ : effLevel ell • Qpt E ell = genericPoint E :=
    nsmul_divSys E (effLevel ell) (effLevel_pos ell)
  calc
    act E σ (genericPoint E) = act E σ (effLevel ell • Qpt E ell) := congrArg (act E σ) hnQ.symm
    _ = effLevel ell • act E σ (Qpt E ell) := map_nsmul _ _ _
    _ = effLevel ell • Qpt E ell := sub_eq_zero.mp (by simpa only [nsmul_sub] using ht)
    _ = genericPoint E := hnQ

theorem normalization_yG_mem_unsigned (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    yG E ∈ normalizationField E ell M false := by
  change yG E ∈ stabilizerField E ell M false
  rw [stabilizerField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := congrArg ptY (act_generic_of_unsigned E hσ)
  rw [ptY_act] at h
  exact h

/-- The original elliptic function field is contained in every actual unsigned field. -/
theorem normalization_base_unsigned_le (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    normalizationField E 1 ⊥ false ≤ normalizationField E ell M false := by
  rw [normalizationFullDivision_eq_adjoin, Qpt_one]
  change IntermediateField.adjoin (xLine E) {xG E, yG E} ≤ normalizationField E ell M false
  rw [IntermediateField.adjoin_le_iff]
  rintro a (rfl | rfl)
  · exact (normalizationField E ell M false).algebraMap_mem ⟨xG E, xG_mem_xLine E⟩
  · exact normalization_yG_mem_unsigned E ell M

/-- The actual finite Galois closure of the full division-coordinate field. -/
def divisionNormalClosure (ell : ℕ) : IntermediateField (xLine E) (Ω E) :=
  IntermediateField.normalClosure (xLine E) (normalizationField E ell ⊥ false) (Ω E)

local instance finite_divisionNormalClosure (ell : ℕ) :
    FiniteDimensional (xLine E) (divisionNormalClosure E ell) := by
  unfold divisionNormalClosure
  infer_instance

local instance galois_divisionNormalClosure (ell : ℕ) :
    IsGalois (xLine E) (divisionNormalClosure E ell) := by
  unfold divisionNormalClosure
  have : IsGalois (xLine E) (Ω E) := by
    rw [← baseField_eq_xLine E]
    infer_instance
  infer_instance

theorem normalizationFull_le_divisionNormalClosure (ell : ℕ) :
    normalizationField E ell ⊥ false ≤ divisionNormalClosure E ell :=
  IntermediateField.le_normalClosure (normalizationField E ell ⊥ false)

theorem normalization_unsigned_le_divisionNormalClosure (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    normalizationField E ell M false ≤ divisionNormalClosure E ell :=
  (normalizationField_le_fullDivision E ell M false).trans
    (normalizationFull_le_divisionNormalClosure E ell)

attribute [local instance] primeNormalizationSeparable

lemma normalization_maximal_ne_bot (N : IntermediateField (xLine E) (Ω E))
    [FiniteDimensional (xLine E) N] (w : Ideal (FunctionFieldNormalization.coordRing (xG E) N))
    (hw : w.IsMaximal) : w ≠ ⊥ := by
  intro h
  subst w
  exact FunctionFieldNormalization.notFieldRing (xG E) (transcendental_xG E) N
    (Ring.isField_iff_maximal_bot.mpr hw)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
