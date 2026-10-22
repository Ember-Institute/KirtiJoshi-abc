/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Homs.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source copyright and Apache-2.0 license before
copying. No NOTICE file occurs in the reference tree. Retain the notice below.
modifications: use the local actual normalization fields and split the
coordinate and field-fixation proofs. Apply the proved prime-valuation
comparison to membership in Mathlib's actual Ideal.inertia. Remove the
reference's file-wide proof-budget increases.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineNormalizationPrimeValuation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineIntegralDivisionPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.DivisionPointInertia

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Homs.lean, inertia_fixes_Q.
fidelity: actual inertia of a nonzero normalization prime in a finite extension,
when it fixes the base-curve y coordinate, fixes both actual division coordinates
and the full division-coordinate field, hence the unsigned cover field.
boundary: Scene1/Derived. This supplies the inertia input to the ramification
comparison. The ramification index and covering-etale conclusion remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
attribute [local instance 2000] Classical.propDecidable
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

omit [CharZero k] [E.IsElliptic] in
private theorem rebaseField_adjoin {B B' : IntermediateField k (Ω E)} (h : B = B')
    (T : Set (Ω E)) :
    FunctionFieldNormalization.rebaseField h (IntermediateField.adjoin B T) =
      IntermediateField.adjoin B' T := by
  subst B'
  ext a
  rfl

/-- The full unsigned normalization field is the actual division-coordinate field. -/
theorem normalizationFullDivision_eq_adjoin (ell : ℕ) :
    normalizationField E ell ⊥ false =
      IntermediateField.adjoin (xLine E) {ptX (Qpt E ell), ptY (Qpt E ell)} := by
  unfold normalizationField
  rw [stabilizerField_bot_false_eq_QField]
  exact rebaseField_adjoin E (baseField_eq_xLine E) _

theorem normalizationField_le_fullDivision (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (pm : Bool) : normalizationField E ell M pm ≤ normalizationField E ell ⊥ false := by
  intro a ha
  change a ∈ stabilizerField E ell ⊥ false
  rw [stabilizerField_bot_false_eq_QField]
  exact stabilizerField_le_QField E ell M pm ha

attribute [local instance] primeNormalizationSeparable primeNormalizationCoeffComm
  normalizationFieldRingAction primeNormalizationDedekind primeNormalizationFraction

variable (N : IntermediateField (xLine E) (Ω E)) [FiniteDimensional (xLine E) N]

/-- Apply actual prime inertia to division points already expressed over N. -/
theorem normalizationPrime_inertia_fixes_point
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (τ : N ≃ₐ[xLine E] N) (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[xLine E] N))
    {xg yg : N} (hG : (E⁄N).toAffine.Nonsingular xg yg)
    (hxg : xg ∈ normalizationCoeffSubalgebra E N)
    (hτG : Affine.Point.map (W' := E) (S := k) (τ.toAlgHom.restrictScalars k)
      (Affine.Point.some xg yg hG) = Affine.Point.some xg yg hG)
    (Q : (E⁄N).toAffine.Point) (n : ℕ) (hn : 0 < n)
    (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E) (S := k) (τ.toAlgHom.restrictScalars k) Q = Q :=
  DivisionPointInertia.inertia_fixes_of_nsmul E
    (normalizationCoeffSubalgebra E N) (normalizationCoeffSubalgebra_integrallyClosed E N)
    (normalizationPrimeSubring E N p)
    (fun a ha => normalization_mem_primeSubring E N p ⟨a, ha⟩)
    (τ.toAlgHom.restrictScalars k)
    (fun a ha => normalizationPrime_inertia_lt_one E N p τ hτ ⟨a, ha⟩)
    n hn hG hxg hτG Q hQ

/-- Actual prime inertia over the base curve fixes both actual division coordinates. -/
theorem normalizationPrime_inertia_fixes_coordinates (ell : ℕ)
    (hN : normalizationField E ell ⊥ false ≤ N) (hyN : yG E ∈ N)
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (τ : N ≃ₐ[xLine E] N) (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[xLine E] N))
    (hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩) :
    τ ⟨ptX (Qpt E ell), hN (Qpt_coordinates_mem_normalizationField E ell).1⟩ =
        ⟨ptX (Qpt E ell), hN (Qpt_coordinates_mem_normalizationField E ell).1⟩ ∧
      τ ⟨ptY (Qpt E ell), hN (Qpt_coordinates_mem_normalizationField E ell).2⟩ =
        ⟨ptY (Qpt E ell), hN (Qpt_coordinates_mem_normalizationField E ell).2⟩ := by
  obtain ⟨x, y, h, hQ⟩ : ∃ (x y : Ω E) (h : (E⁄(Ω E)).toAffine.Nonsingular x y),
      Qpt E ell = Affine.Point.some x y h := by
    rcases hq : Qpt E ell with _ | ⟨x, y, h⟩
    · exact False.elim (divSys_ne_zero E (effLevel ell) (effLevel_pos ell) hq)
    · exact ⟨x, y, h, rfl⟩
  have hxQ : x ∈ normalizationField E ell ⊥ false := by
    simpa only [hQ, ptX] using (Qpt_coordinates_mem_normalizationField E ell).1
  have hyQ : y ∈ normalizationField E ell ⊥ false := by
    simpa only [hQ, ptY] using (Qpt_coordinates_mem_normalizationField E ell).2
  have hxN : xG E ∈ N := N.algebraMap_mem ⟨xG E, xG_mem_xLine E⟩
  let ι : N →ₐ[k] Ω E := N.val.restrictScalars k
  have hQN : (E⁄N).toAffine.Nonsingular (⟨x, hN hxQ⟩ : N) ⟨y, hN hyQ⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) Subtype.val_injective _ _).mp h
  have hGN : (E⁄N).toAffine.Nonsingular (⟨xG E, hxN⟩ : N) ⟨yG E, hyN⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) Subtype.val_injective _ _).mp
      (nonsingular_generic E)
  have hmapQ : Affine.Point.map (W' := E) (S := k) ι (Affine.Point.some _ _ hQN) =
      Qpt E ell := by rw [hQ]; rfl
  have hmapG : Affine.Point.map (W' := E) (S := k) ι (Affine.Point.some _ _ hGN) =
      genericPoint E := rfl
  have hnQN : effLevel ell • Affine.Point.some _ _ hQN = Affine.Point.some _ _ hGN := by
    apply Affine.Point.map_injective (W' := E) (S := k) ι
    rw [map_nsmul, hmapQ, hmapG]
    exact nsmul_divSys E (effLevel ell) (effLevel_pos ell)
  let σ : N →ₐ[k] N := τ.toAlgHom.restrictScalars k
  have hxgR : (⟨xG E, hxN⟩ : N) ∈ normalizationCoeffSubalgebra E N :=
    isIntegral_algebraMap (R := Algebra.adjoin k {xG E}) (A := N)
      (x := ⟨xG E, Algebra.self_mem_adjoin_singleton k (xG E)⟩)
  have hσG : Affine.Point.map (W' := E) (S := k) σ (Affine.Point.some _ _ hGN) =
      Affine.Point.some _ _ hGN :=
    some_ext (τ.commutes ⟨xG E, xG_mem_xLine E⟩) hτy
  have key := normalizationPrime_inertia_fixes_point E N p τ hτ hGN hxgR hσG
    (Affine.Point.some _ _ hQN) (effLevel ell) (effLevel_pos ell) hnQN
  have hcoords := Affine.Point.some.inj key
  change τ (⟨x, hN hxQ⟩ : N) = ⟨x, hN hxQ⟩ ∧
    τ (⟨y, hN hyQ⟩ : N) = ⟨y, hN hyQ⟩ at hcoords
  simpa only [hQ, ptX, ptY] using hcoords

/-- Actual prime inertia fixes the full division-coordinate field, not only its generators. -/
theorem normalizationPrime_inertia_fixes_fullDivision (ell : ℕ)
    (hN : normalizationField E ell ⊥ false ≤ N) (hyN : yG E ∈ N)
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (τ : N ≃ₐ[xLine E] N) (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[xLine E] N))
    (hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩) :
    ∀ a : N, (a : Ω E) ∈ normalizationField E ell ⊥ false → τ a = a := by
  have hc := normalizationPrime_inertia_fixes_coordinates E N ell hN hyN p τ hτ hτy
  let F' : IntermediateField (xLine E) (Ω E) :=
    { carrier := {b | ∃ hb : b ∈ N, τ ⟨b, hb⟩ = ⟨b, hb⟩}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by
          have ht := congrArg₂ (· * ·) ha' hb'
          simpa [← map_mul] using ht⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨add_mem ha hb, by
          have ht := congrArg₂ (· + ·) ha' hb'
          simpa [← map_add] using ht⟩
      algebraMap_mem' := fun c => ⟨N.algebraMap_mem c, τ.commutes c⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        change τ ((⟨a, ha⟩ : N)⁻¹) = (⟨a, ha⟩ : N)⁻¹
        rw [map_inv₀, ha'] }
  have hle : normalizationField E ell ⊥ false ≤ F' := by
    rw [normalizationFullDivision_eq_adjoin, IntermediateField.adjoin_le_iff]
    rintro a (rfl | rfl)
    · exact ⟨hN (Qpt_coordinates_mem_normalizationField E ell).1, hc.1⟩
    · exact ⟨hN (Qpt_coordinates_mem_normalizationField E ell).2, hc.2⟩
  intro a ha
  obtain ⟨_, hfix⟩ := hle ha
  exact hfix

/-- Consequently this prime inertia fixes each actual unsigned covering field. -/
theorem normalizationPrime_inertia_fixes_unsignedField (ell : ℕ)
    (hN : normalizationField E ell ⊥ false ≤ N) (hyN : yG E ∈ N)
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (τ : N ≃ₐ[xLine E] N) (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[xLine E] N))
    (hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩) (M : AddSubgroup E.toAffine.Point)
    (a : N) (ha : (a : Ω E) ∈ normalizationField E ell M false) : τ a = a :=
  normalizationPrime_inertia_fixes_fullDivision E N ell hN hyN p τ hτ hτy a
    (normalizationField_le_fullDivision E ell M false ha)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
