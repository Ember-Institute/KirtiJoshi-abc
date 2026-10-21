/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Pi1.lean` (Hgp, QField,
openness, and cover inclusions); `Genuine/Realize.lean` (finite fixed field).
original-author: Christian Merten <lana@merten.dev>
original-commit: `7b3756ff3fde46bbd4daa89076fd4bc9c4e60baf` (Pi1.lean)
additional-original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1` (Realize.lean)
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source files' 2026 iut contributors notices and
Apache-2.0 license before copying. Original notice retained below.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`.
fidelity: actual Galois subgroups of the function-field closure, their open/closed
laws, finite fixed fields, and contravariant inclusions. Uses the proved
compatible division system, without a supplied compatibility law. The zero-level
normalization is explicit; actual admissible primes have positive level.
boundary: Scene1/Derived. Affine normalization, etaleness, fundamental-group
comparison, core, and theta-root realization remain separate obligations.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionPoints
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.VariableChangePoint
import Mathlib.Tactic.Module
import Mathlib.Tactic.NthRewrite

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The effective level (the degenerate level `0` is replaced by `1`). -/
def effLevel (ℓ : ℕ) : ℕ := if ℓ = 0 then 1 else ℓ

lemma effLevel_pos (ℓ : ℕ) : 0 < effLevel ℓ := by
  unfold effLevel; split_ifs with h
  · exact one_pos
  · exact Nat.pos_of_ne_zero h

/-- The division point `Q_ℓ` at the effective level. -/
def Qpt (ℓ : ℕ) : Pt E := divSys E (effLevel ℓ)

/-- The subgroup `M ∩ E(k)[ℓ]`, as a subgroup of `E(Ω)`. -/
def Mbar (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : AddSubgroup (Pt E) :=
  (M ⊓ AddSubgroup.torsionBy E.toAffine.Point (effLevel ℓ)).map (base E)

/-- The admissible signs: `+1`, and `−1` when the `±`-flag is set. -/
def SignOK (pm : Bool) (ε : ℤ) : Prop := ε = 1 ∨ (pm = true ∧ ε = -1)

omit [E.IsElliptic] in
lemma act_mem_Mbar (σ : Gal E) {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {T : Pt E}
    (hT : T ∈ Mbar E ℓ M) : act E σ T = T := by
  obtain ⟨T', -, rfl⟩ := hT
  exact act_base E σ T'

/-- **`Aut(Ω / F_X)`** for `X = (E, ℓ, M, ±)`: the automorphisms `σ` with
`σ(Q_ℓ) = ±Q_ℓ + T`, `T ∈ M` (sign `−` only with the `±`-flag). -/
def Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) : Subgroup (Gal E) where
  carrier := {σ | ∃ ε : ℤ, SignOK pm ε ∧ act E σ (Qpt E ℓ) - ε • Qpt E ℓ ∈ Mbar E ℓ M}
  one_mem' := ⟨1, Or.inl rfl, by simp [act_one]⟩
  mul_mem' := by
    rintro σ τ ⟨ε, hε, hσ⟩ ⟨η, hη, hτ⟩
    refine ⟨ε * η, ?_, ?_⟩
    · rcases hε with rfl | ⟨hpm, rfl⟩ <;> rcases hη with rfl | ⟨hpm', rfl⟩ <;>
        simp_all [SignOK]
    · set T := act E σ (Qpt E ℓ) - ε • Qpt E ℓ
      set T' := act E τ (Qpt E ℓ) - η • Qpt E ℓ
      have hτQ : act E τ (Qpt E ℓ) = η • Qpt E ℓ + T' := by simp [T']
      have hσQ : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + T := by simp [T]
      have : act E (σ * τ) (Qpt E ℓ) - (ε * η) • Qpt E ℓ = η • T + T' := by
        rw [act_mul, hτQ, map_add, map_zsmul, hσQ, act_mem_Mbar E σ hτ]
        module
      rw [this]
      exact add_mem (zsmul_mem hσ η) hτ
  inv_mem' := by
    rintro σ ⟨ε, hε, hσ⟩
    refine ⟨ε, hε, ?_⟩
    set T := act E σ (Qpt E ℓ) - ε • Qpt E ℓ
    have hσQ : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + T := by simp [T]
    have hεε : ε * ε = 1 := by rcases hε with rfl | ⟨-, rfl⟩ <;> norm_num
    have h1 : Qpt E ℓ = act E σ⁻¹ (act E σ (Qpt E ℓ)) := by rw [← act_mul, inv_mul_cancel, act_one]
    have e : Qpt E ℓ = ε • act E σ⁻¹ (Qpt E ℓ) + T := by
      conv_lhs => rw [h1]
      rw [hσQ, map_add, map_zsmul, act_mem_Mbar E σ⁻¹ hσ]
    have : act E σ⁻¹ (Qpt E ℓ) - ε • Qpt E ℓ = -(ε • T) := by
      nth_rw 2 [e]
      simp only [zsmul_add, smul_smul, hεε, one_smul]
      abel
    rw [this]
    exact neg_mem (zsmul_mem hσ ε)


/-! ### Openness -/

/-- The subfield generated over `P` by the coordinates of `Q_ℓ`. -/
def QField (ℓ : ℕ) : IntermediateField (baseField E) (Ω E) :=
  IntermediateField.adjoin (baseField E) {ptX (Qpt E ℓ), ptY (Qpt E ℓ)}

instance finiteDimensional_QField (ℓ : ℕ) : FiniteDimensional (baseField E) (QField E ℓ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := baseField E) x).isIntegral)

omit [E.IsElliptic] in
lemma act_eq_self_of_fix (σ : Gal E) (Q : Pt E) (hx : σ (ptX Q) = ptX Q)
    (hy : σ (ptY Q) = ptY Q) : act E σ Q = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · change Affine.Point.some _ _ _ = _
    simp only [ptX, ptY] at hx hy
    congr 1

lemma QField_fixing_le (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (QField E ℓ).fixingSubgroup ≤ Hgp E ℓ M pm := by
  intro σ hσ
  have hfix : ∀ a ∈ ({ptX (Qpt E ℓ), ptY (Qpt E ℓ)} : Set (Ω E)), σ a = a := fun a ha =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ a
      (IntermediateField.subset_adjoin _ _ ha)
  refine ⟨1, Or.inl rfl, ?_⟩
  rw [act_eq_self_of_fix E σ _ (hfix _ (by simp)) (hfix _ (by simp)), one_smul, sub_self]
  exact zero_mem _

lemma isOpen_Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsOpen (Hgp E ℓ M pm : Set (Gal E)) :=
  Subgroup.isOpen_mono (QField_fixing_le E ℓ M pm) (QField E ℓ).fixingSubgroup_isOpen

lemma isClosed_Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsClosed (Hgp E ℓ M pm : Set (Gal E)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_Hgp E ℓ M pm)

lemma Qpt_of_compatible {n ℓ ℓ' : ℕ} (hn : 0 < n)
    (hℓ : n * ℓ' = ℓ) (hℓ' : 0 < ℓ') : Qpt E ℓ' = n • Qpt E ℓ := by
  have hℓ0 : ℓ ≠ 0 := by subst hℓ; exact (Nat.mul_pos hn hℓ').ne'
  simp only [Qpt, effLevel, if_neg hℓ0, if_neg hℓ'.ne']
  rw [← hℓ, (compatible_divSys E).2 n ℓ' hn hℓ']

omit [E.IsElliptic] in
lemma nsmul_mem_Mbar {n ℓ ℓ' : ℕ} (hℓ : n * ℓ' = ℓ) (hℓ' : 0 < ℓ')
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {T : Pt E}
    (hT : T ∈ Mbar E ℓ M) : n • T ∈ Mbar E ℓ' M' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_nsmul]; exact zero_mem _
  have hℓ0 : ℓ ≠ 0 := by subst hℓ; exact (Nat.mul_pos hn hℓ').ne'
  obtain ⟨T₀, ⟨hT₀M, hT₀t⟩, rfl⟩ := hT
  have e1 : effLevel ℓ = ℓ := if_neg hℓ0
  have e2 : effLevel ℓ' = ℓ' := if_neg hℓ'.ne'
  refine ⟨n • T₀, ⟨hM T₀ hT₀M, ?_⟩, map_nsmul _ _ _⟩
  rw [e1] at hT₀t
  rw [e2]
  have h1 := (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀t
  refine (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mpr ?_
  rw [smul_smul, mul_comm, hℓ, h1]

omit [E.IsElliptic] in
lemma Mbar_zero (M : AddSubgroup E.toAffine.Point) {T : Pt E} (hT : T ∈ Mbar E 0 M) : T = 0 := by
  obtain ⟨T₀, ⟨-, hT₀t⟩, rfl⟩ := hT
  have e : effLevel 0 = 1 := if_pos rfl
  rw [e] at hT₀t
  have h1 := (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀t
  rw [one_smul] at h1
  rw [h1, map_zero]

/-- The groups attached to a cover are nested (for a compatible system of division points). -/
theorem Hgp_le {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' := by
  rintro σ ⟨ε, hε, hσ⟩
  have hε' : SignOK pm' ε := by
    rcases hε with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨hpm h, h'⟩
  rcases Nat.eq_zero_or_pos ℓ' with rfl | hℓ'
  · have hℓ0 : ℓ = 0 := by simpa using hℓ.symm
    subst hℓ0
    refine ⟨ε, hε', ?_⟩
    rw [Mbar_zero E M hσ]
    exact zero_mem _
  · refine ⟨ε, hε', ?_⟩
    rw [Qpt_of_compatible E hn hℓ hℓ', map_nsmul]
    have e : n • act E σ (Qpt E ℓ) - ε • (n • Qpt E ℓ) =
        n • (act E σ (Qpt E ℓ) - ε • Qpt E ℓ) := by module
    rw [e]
    exact nsmul_mem_Mbar E hℓ hℓ' hM hσ

/-- At positive level the selected point is the actual division point. -/
lemma Qpt_eq_divSys {ℓ : ℕ} (hℓ : 0 < ℓ) : Qpt E ℓ = divSys E ℓ := by
  simp only [Qpt, effLevel, if_neg hℓ.ne']

/-- The actual fixed field of the signed torsion-translation subgroup. -/
def stabilizerField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IntermediateField (baseField E) (Ω E) :=
  IntermediateField.fixedField (Hgp E ℓ M pm)

/-- The field determines exactly the subgroup used to construct it. -/
lemma fixingSubgroup_stabilizerField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (stabilizerField E ℓ M pm).fixingSubgroup = Hgp E ℓ M pm :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨Hgp E ℓ M pm, isClosed_Hgp E ℓ M pm⟩

instance finiteDimensional_stabilizerField (ℓ : ℕ)
    (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    FiniteDimensional (baseField E) (stabilizerField E ℓ M pm) := by
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_stabilizerField]
  exact isOpen_Hgp E ℓ M pm

/-- These fixed fields lie in the concrete field generated by the division coordinates. -/
lemma stabilizerField_le_QField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    stabilizerField E ℓ M pm ≤ QField E ℓ := by
  have h := IntermediateField.fixedField_antitone (QField_fixing_le E ℓ M pm)
  exact h.trans_eq (InfiniteGalois.fixedField_fixingSubgroup (QField E ℓ))

/-- A subgroup inclusion induced by a level map reverses on the fixed fields. -/
theorem stabilizerField_le_of_cover {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M')
    {pm pm' : Bool} (hpm : pm = true → pm' = true) :
    stabilizerField E ℓ' M' pm' ≤ stabilizerField E ℓ M pm :=
  IntermediateField.fixedField_antitone (Hgp_le E hn hℓ hM hpm)

/-- Passing to the signed quotient enlarges the subgroup and shrinks its fixed field. -/
lemma stabilizerField_signed_le_unsigned (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    stabilizerField E ℓ M true ≤ stabilizerField E ℓ M false :=
  stabilizerField_le_of_cover E (n := 1) Nat.one_pos (one_mul ℓ)
    (fun _ h => by simpa only [one_nsmul] using h) (fun h => False.elim (Bool.false_ne_true h))

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
