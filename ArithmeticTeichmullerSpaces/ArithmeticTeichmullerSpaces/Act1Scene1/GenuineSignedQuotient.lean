/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Orbifold.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `a772c5e73c0f632a34d1c866063e72f388f9352b`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source notice and reference Apache-2.0 LICENSE.
modification: extracts the unsigned-subgroup conjugation proof into the local
namespace, and proves normality inside the actual signed subgroup. No orbifold
comparison, tempered fundamental group, or reference package is imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionGroups
import Mathlib.GroupTheory.Index

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Orbifold.lean`, `conj_mem_Hgp_false`.
fidelity: proves normality of the actual torsion-translation subgroup inside
the signed group, and proves that the quotient order divides two. This concerns
the same division system and torsion line.
boundary: Scene1/Derived. It does not assert an orbicurve realization or an
identity between ramification indices and stabilizer orders.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

lemma mem_Hgp_false {ell : ℕ} {M : AddSubgroup E.toAffine.Point} {σ : Gal E} :
    σ ∈ Hgp E ell M false ↔ act E σ (Qpt E ell) - Qpt E ell ∈ Mbar E ell M := by
  constructor
  · rintro ⟨ε, hε, h⟩
    rcases hε with rfl | ⟨h', -⟩
    · simpa using h
    · exact absurd h' Bool.false_ne_true
  · intro h
    exact ⟨1, Or.inl rfl, by simpa using h⟩

lemma Hgp_false_le (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Hgp E ell M false ≤ Hgp E ell M pm := by
  rintro σ ⟨ε, hε, h⟩
  refine ⟨ε, ?_, h⟩
  rcases hε with h' | ⟨h', -⟩
  · exact Or.inl h'
  · exact absurd h' Bool.false_ne_true

lemma conj_mem_Hgp_false {ell : ℕ} {M : AddSubgroup E.toAffine.Point}
    {pm : Bool} {σ n : Gal E} (hσ : σ ∈ Hgp E ell M pm)
    (hn : n ∈ Hgp E ell M false) : σ * n * σ⁻¹ ∈ Hgp E ell M false := by
  rw [mem_Hgp_false] at hn ⊢
  obtain ⟨η, -, hη⟩ := (Hgp E ell M pm).inv_mem hσ
  have h1 : act E σ⁻¹ (Qpt E ell) =
      η • Qpt E ell + (act E σ⁻¹ (Qpt E ell) - η • Qpt E ell) := by abel
  have h2 : act E n (Qpt E ell) = Qpt E ell + (act E n (Qpt E ell) - Qpt E ell) := by abel
  have hQ : η • act E σ (Qpt E ell) +
      (act E σ⁻¹ (Qpt E ell) - η • Qpt E ell) = Qpt E ell := by
    have := congrArg (act E σ) h1
    rw [← act_mul, mul_inv_cancel, act_one, map_add, map_zsmul,
      act_mem_Mbar E σ hη] at this
    exact this.symm
  rw [act_mul, act_mul, h1, map_add (act E n), map_zsmul, h2, act_mem_Mbar E n hη,
    map_add, map_zsmul, map_add, act_mem_Mbar E σ hn, act_mem_Mbar E σ hη]
  have e : η • (act E σ (Qpt E ell) + (act E n (Qpt E ell) - Qpt E ell)) +
      (act E σ⁻¹ (Qpt E ell) - η • Qpt E ell) - Qpt E ell =
      η • (act E n (Qpt E ell) - Qpt E ell) := by
    conv_lhs => rw [zsmul_add, add_comm (η • act E σ (Qpt E ell)), add_assoc, hQ]
    abel
  rw [e]
  exact zsmul_mem hn η

/-- The unsigned subgroup is normal in each signed/unsigned ambient cover group. -/
theorem Hgp_false_normal (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    ((Hgp E ell M false).subgroupOf (Hgp E ell M pm)).Normal :=
  (Subgroup.normal_subgroupOf_iff (Hgp_false_le E ell M pm)).mpr
    (fun _ _ hn hσ => conj_mem_Hgp_false E hσ hn)

private lemma neg_translation_of_not_mem_unsigned {ell : ℕ}
    {M : AddSubgroup E.toAffine.Point} {σ : Gal E}
    (hσ : σ ∈ Hgp E ell M true) (hne : σ ∉ Hgp E ell M false) :
    act E σ (Qpt E ell) + Qpt E ell ∈ Mbar E ell M := by
  obtain ⟨ε, hε, h⟩ := hσ
  rcases hε with rfl | ⟨-, rfl⟩
  · exact False.elim (hne ⟨1, Or.inl rfl, h⟩)
  · simpa only [neg_one_zsmul, sub_neg_eq_add] using h

/-- Two non-translation signed elements compose to an unsigned translation. -/
theorem Hgp_mul_mem_false_of_not_mem {ell : ℕ} {M : AddSubgroup E.toAffine.Point}
    {σ τ : Gal E} (hσ : σ ∈ Hgp E ell M true) (hτ : τ ∈ Hgp E ell M true)
    (hnσ : σ ∉ Hgp E ell M false) (hnτ : τ ∉ Hgp E ell M false) :
    σ * τ ∈ Hgp E ell M false := by
  have hσT := neg_translation_of_not_mem_unsigned E hσ hnσ
  have hτT := neg_translation_of_not_mem_unsigned E hτ hnτ
  apply (mem_Hgp_false E).mpr
  have hτQ : act E τ (Qpt E ell) =
      -Qpt E ell + (act E τ (Qpt E ell) + Qpt E ell) := by abel
  rw [act_mul, hτQ, map_add, map_neg, act_mem_Mbar E σ hτT]
  convert sub_mem hτT hσT using 1 <;> abel

/-- Only the positive and negative sign cosets can occur. -/
theorem Hgp_false_relIndex_dvd_two (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (Hgp E ell M false).relIndex (Hgp E ell M true) ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  by_cases hle : Hgp E ell M true ≤ Hgp E ell M false
  · exact ⟨1, one_mem _, fun b hb => Or.inr (hle hb)⟩
  · change ¬ ∀ a, a ∈ Hgp E ell M true → a ∈ Hgp E ell M false at hle
    push_neg at hle
    obtain ⟨a, ha, hna⟩ := hle
    refine ⟨a, ha, ?_⟩
    intro b hb
    by_cases hnb : b ∈ Hgp E ell M false
    · exact Or.inr hnb
    · exact Or.inl (Hgp_mul_mem_false_of_not_mem E hb ha hnb hna)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
