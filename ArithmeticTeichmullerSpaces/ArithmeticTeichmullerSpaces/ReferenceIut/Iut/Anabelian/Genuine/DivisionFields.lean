/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Punctured.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source's 2026 iut contributors notice and Apache-2.0
license before copying. Original notice retained below.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`.
fidelity: adapted the level-one function-field identification and polynomial
coordinate compatibility to the actual `stabilizerField` over `baseField`.
Proved the trivial-line stabilizer identity and its equality with the actual
division-coordinate field. No geometric identity is a supplied parameter.
boundary: Scene1/Derived. Affine normalization, etaleness, core, and theta-root
realization remain separate obligations.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionGroups

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The Galois action applies the same automorphism to the x coordinate. -/
lemma ptX_act (σ : Gal E) (Q : Pt E) : ptX (act E σ Q) = σ (ptX Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rfl

lemma ptY_act (σ : Gal E) (Q : Pt E) : ptY (act E σ Q) = σ (ptY Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rfl

lemma act_eq_self_iff_coordinates (σ : Gal E) (Q : Pt E) :
    act E σ Q = Q ↔ σ (ptX Q) = ptX Q ∧ σ (ptY Q) = ptY Q := by
  constructor
  · intro h
    exact ⟨by rw [← ptX_act E σ Q, h], by rw [← ptY_act E σ Q, h]⟩
  · rintro ⟨hx, hy⟩
    exact act_eq_self_of_fix E σ Q hx hy

/-- Fixing the two division coordinates is equivalent to fixing their generated field. -/
lemma mem_QField_fixing_iff (ℓ : ℕ) (σ : Gal E) :
    σ ∈ (QField E ℓ).fixingSubgroup ↔
      σ (ptX (Qpt E ℓ)) = ptX (Qpt E ℓ) ∧
        σ (ptY (Qpt E ℓ)) = ptY (Qpt E ℓ) := by
  constructor
  · intro h
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ σ).mp h _
      (IntermediateField.subset_adjoin _ _ (by simp)),
      (IntermediateField.mem_fixingSubgroup_iff _ σ).mp h _
        (IntermediateField.subset_adjoin _ _ (by simp))⟩
  · rintro ⟨hx, hy⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    change z ∈ IntermediateField.adjoin (baseField E)
      {ptX (Qpt E ℓ), ptY (Qpt E ℓ)} at hz
    refine IntermediateField.adjoin_induction (baseField E) (p := fun z _ => σ z = z)
      ?_ ?_ ?_ ?_ ?_ hz
    · rintro z (rfl | rfl)
      · exact hx
      · exact hy
    · intro c
      exact σ.commutes c
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro x _ hx
      rw [map_inv₀, hx]
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy]

lemma mem_Hgp_bot_false_iff (ℓ : ℕ) (σ : Gal E) :
    σ ∈ Hgp E ℓ ⊥ false ↔ act E σ (Qpt E ℓ) = Qpt E ℓ := by
  simp [Hgp, SignOK, Mbar, sub_eq_zero]

/-- The trivial-line unsigned stabilizer is exactly the coordinate-field fixing group. -/
lemma Hgp_bot_false_eq_QField_fixing (ℓ : ℕ) :
    Hgp E ℓ ⊥ false = (QField E ℓ).fixingSubgroup := by
  ext σ
  rw [mem_Hgp_bot_false_iff, mem_QField_fixing_iff]
  exact act_eq_self_iff_coordinates E σ (Qpt E ℓ)

/-- The corresponding fixed field is the concrete division-coordinate field itself. -/
theorem stabilizerField_bot_false_eq_QField (ℓ : ℕ) :
    stabilizerField E ℓ ⊥ false = QField E ℓ := by
  unfold stabilizerField
  rw [Hgp_bot_false_eq_QField_fixing]
  exact InfiniteGalois.fixedField_fixingSubgroup (QField E ℓ)

@[simp] lemma Qpt_one : Qpt E 1 = genericPoint E := by
  rw [Qpt_eq_divSys E Nat.one_pos, divSys_one]

lemma QField_one_coordinates :
    QField E 1 = IntermediateField.adjoin (baseField E) {xG E, yG E} := by
  simp only [QField, Qpt_one, genericPoint, ptX, ptY]

/-- The perfect-closure base equals the x-line and lies in the embedded curve function field. -/
lemma baseField_le_functionFieldRange : baseField E ≤ (ιF E).fieldRange := by
  rw [baseField_eq_xLine, xLine, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff]
  exact ⟨xF E, rfl⟩

/-- Every level-one coordinate-field element comes from the actual curve function field. -/
lemma QField_one_le_range (z : Ω E) (hz : z ∈ QField E 1) : ∃ f, ιF E f = z := by
  let L : IntermediateField (baseField E) (Ω E) :=
    (ιF E).fieldRange.toSubfield.toIntermediateField
      (fun x => baseField_le_functionFieldRange E x.2)
  have h : QField E 1 ≤ L := by
    rw [QField_one_coordinates, IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact ⟨xF E, rfl⟩
    · exact ⟨yF E, rfl⟩
  exact h hz

lemma ιF_mem_QField_one (f : E.toAffine.FunctionField) : ιF E f ∈ QField E 1 := by
  let L : IntermediateField (xLine E) (Ω E) :=
    (QField E 1).toSubfield.toIntermediateField (fun x => by
      have hx : (x : Ω E) ∈ baseField E := by
        rw [baseField_eq_xLine]
        exact x.2
      exact (QField E 1).algebraMap_mem ⟨x, hx⟩)
  have h : fnField E ≤ L := by
    rw [fnField, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change yG E ∈ QField E 1
    rw [QField_one_coordinates]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  exact h (ιF_mem_fnField E f)

/-- The base-curve fixed field is the original elliptic function field, via its actual embedding. -/
def baseFunctionFieldEquiv :
    E.toAffine.FunctionField ≃+* stabilizerField E 1 ⊥ false :=
  RingEquiv.ofBijective ((ιF E).toRingHom.codRestrict (stabilizerField E 1 ⊥ false)
      (fun f => by rw [stabilizerField_bot_false_eq_QField]; exact ιF_mem_QField_one E f))
    ⟨fun a b h => (ιF E).injective (congrArg Subtype.val h), fun z => by
      have hz : (z : Ω E) ∈ QField E 1 := by
        rw [← stabilizerField_bot_false_eq_QField]
        exact z.2
      obtain ⟨f, hf⟩ := QField_one_le_range E z hz
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] lemma coe_baseFunctionFieldEquiv (f : E.toAffine.FunctionField) :
    ((baseFunctionFieldEquiv E f : stabilizerField E 1 ⊥ false) : Ω E) = ιF E f := rfl

omit [CharZero k] [E.IsElliptic] in
lemma ιF_algebraMap_poly (p : k[X]) :
    ιF E (algebraMap k[X] E.toAffine.FunctionField p) = aeval (xG E) p := by
  have h : ((ιF E).comp (IsScalarTower.toAlgHom k k[X] E.toAffine.FunctionField)) =
      aeval (xG E) := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    change ιF E (algebraMap k[X] E.toAffine.FunctionField X) = xG E
    rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField]
    rfl
  exact congrArg (fun φ : k[X] →ₐ[k] Ω E => φ p) h

/-- The identification preserves the polynomial x-coordinate embedding used for normalization. -/
lemma baseFunctionFieldEquiv_algebraMap_poly (p : k[X]) :
    ((baseFunctionFieldEquiv E (algebraMap k[X] E.toAffine.FunctionField p) :
      stabilizerField E 1 ⊥ false) : Ω E) = aeval (xG E) p := by
  rw [coe_baseFunctionFieldEquiv]
  exact ιF_algebraMap_poly E p

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
