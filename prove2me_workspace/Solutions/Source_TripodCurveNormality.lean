/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors

Adapted from Iut/Tripod/Galois.lean at 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PointMap
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Solutions.Source_ReferenceIutVariableChangePoint
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Solutions.Source_TripodTorsionAction
import Solutions.Source_TripodTpdGalois
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut WeierstrassCurve WeierstrassCurve.Affine Polynomial
open JoshiTeich.ReferenceIut.Anabelian (pointMap pointMap_some)
open scoped Classical IntermediateField

private theorem sqrtNegOne_mem_fieldOf' (l : Qbar) : sqrtNegOne ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

private theorem sqrtLam_mem_fieldOf' (l : Qbar) : sqrtLam l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

private theorem sqrtOneSubLam_mem_fieldOf' (l : Qbar) : sqrtOneSubLam l ∈ fieldOf' l :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl (by simp)))

/-! ### The Legendre curves of `1 − λ` and `1/λ` as changes of variables of `E_λ` -/

/-- `E_{1−λ} = ⟨√−1, 1, 0, 0⟩ • E_λ`: the change of variables `(x, y) ↦ (1 − x, √−1·y)`. -/
private theorem legendre_vc_one_sub {i : Qbar} (hi : i ^ 2 = -1) (hi0 : i ≠ 0) (l : Qbar) :
    (⟨Units.mk0 i hi0, 1, 0, 0⟩ : VariableChange Qbar) • legendre l = legendre (1 - l) := by
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hi]; norm_num
  ext
  · simp [variableChange_a₁]
  · simp only [variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hi,
      legendre_a₂, legendre_a₁]
    ring
  · simp [variableChange_a₃]
  · simp only [variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4,
      legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring
  · simp only [variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h6,
      legendre_a₆, legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring

/-- `E_{1/λ} = ⟨√λ, 0, 0, 0⟩ • E_λ`: the change of variables `(x, y) ↦ (λx, λ√λ·y)`. -/
private theorem legendre_vc_inv {u l : Qbar} (hu : u ^ 2 = l) (hu0 : u ≠ 0) :
    (⟨Units.mk0 u hu0, 0, 0, 0⟩ : VariableChange Qbar) • legendre l = legendre l⁻¹ := by
  have hl : l ≠ 0 := by rw [← hu]; exact pow_ne_zero _ hu0
  have h4 : u ^ 4 = l ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu]
  ext
  · simp [variableChange_a₁]
  · simp only [variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu,
      legendre_a₂, legendre_a₁]
    field_simp
    ring
  · simp [variableChange_a₃]
  · simp only [variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4,
      legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    field_simp
    ring
  · simp only [variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow,
      legendre_a₆, legendre_a₄, legendre_a₃, legendre_a₂, legendre_a₁]
    ring

/-! ### Transport of the torsion coordinates along a change of variables -/

/-- Torsion is transported along an equality of curves. -/
private theorem nsmul_some_eq_zero_of_eq {W W' : WeierstrassCurve Qbar} (h : W = W') {x y : Qbar}
    (hW : W.toAffine.Nonsingular x y) (hW' : W'.toAffine.Nonsingular x y) (n : ℕ)
    (hP : n • Affine.Point.some x y hW = 0) : n • Affine.Point.some x y hW' = 0 := by
  subst h
  exact hP

/-- **The torsion coordinates of `E_μ` lie in `F` if those of `E_λ` do**, when
`E_μ = C • E_λ` for a change of variables `C = (u, r, s, t)` with `u, r, s, t ∈ F`: the
isomorphism `E_λ(ℚ̄) ≅ E_μ(ℚ̄)` maps `E_λ[n]` onto `E_μ[n]`, and the coordinates
`((x − r)/u², (y − t − s(x − r))/u³)` of the image of `(x, y)` lie in `F`. -/
private theorem torsionCoords_subset_of_vc {l m : Qbar} {C : VariableChange Qbar}
    (h : C • legendre l = legendre m) (F : IntermediateField ℚ Qbar)
    (huF : (C.u : Qbar) ∈ F) (hrF : C.r ∈ F) (hsF : C.s ∈ F) (htF : C.t ∈ F) {n : ℕ}
    (hl : torsionCoords l n ⊆ F) : torsionCoords m n ⊆ F := by
  intro c hc
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
  cases P with
  | zero => exact absurd hcP id
  | some x' y' hxy' =>
    have hxy'' : (C • legendre l).toAffine.Nonsingular x' y' := h ▸ hxy'
    have hP' : n • Affine.Point.some x' y' hxy'' = 0 :=
      nsmul_some_eq_zero_of_eq h.symm hxy' hxy'' n hP
    obtain ⟨Q, hQP⟩ := Anabelian.vcPoint_surjective C (legendre l) (Affine.Point.some x' y' hxy'')
    have hQn : n • Q = 0 := by
      apply Anabelian.vcPoint_injective C (legendre l)
      change Anabelian.vcHom C (legendre l) (n • Q) = Anabelian.vcHom C (legendre l) 0
      rw [map_nsmul, map_zero, Anabelian.vcHom_apply, hQP]
      exact hP'
    cases Q with
    | zero => exact absurd hQP.symm (Affine.Point.some_ne_zero hxy'')
    | some x y hxy =>
      rw [Anabelian.vcPoint_some, Affine.Point.some.injEq] at hQP
      have hx : x ∈ F := hl (mem_torsionCoords hQn (Set.mem_insert _ _))
      have hy : y ∈ F := hl (mem_torsionCoords hQn (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      rcases hcP with rfl | rfl
      · rw [← hQP.1]
        exact div_mem (sub_mem hx hrF) (pow_mem huF 2)
      · rw [← hQP.2]
        exact div_mem (sub_mem (sub_mem hy htF) (mul_mem hsF (sub_mem hx hrF))) (pow_mem huF 3)

/-! ### The six conjugates of `λ` over `ℚ(j)` -/

/-- **The conjugates of `λ` over `ℚ(j)`**: `μ ∈ {λ, 1 − λ, 1/λ, 1/(1 − λ), 1 − 1/λ,
1 − 1/(1 − λ)}`. -/
private def Conj (l m : Qbar) : Prop :=
  m = l ∨ m = 1 - l ∨ m = l⁻¹ ∨ m = (1 - l)⁻¹ ∨ m = 1 - l⁻¹ ∨ m = 1 - (1 - l)⁻¹

/-- The conjugates of `λ` are closed under `μ ↦ 1 − μ`. -/
private theorem conj_one_sub {l m : Qbar} (h : Conj l m) : Conj l (1 - m) := by
  rcases h with h | h | h | h | h | h <;> subst m
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (sub_sub_cancel 1 l)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inl (sub_sub_cancel 1 l⁻¹)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_sub_cancel 1 (1 - l)⁻¹))))

/-- The conjugates of `λ` lie in every subfield containing `λ`. -/
private theorem conj_mem {l m : Qbar} (h : Conj l m) {F : IntermediateField ℚ Qbar} (hl : l ∈ F) :
    m ∈ F := by
  rcases h with h | h | h | h | h | h <;> subst m
  · exact hl
  · exact sub_mem (one_mem _) hl
  · exact inv_mem hl
  · exact inv_mem (sub_mem (one_mem _) hl)
  · exact sub_mem (one_mem _) (inv_mem hl)
  · exact sub_mem (one_mem _) (inv_mem (sub_mem (one_mem _) hl))

/-- **`F_λ` contains a square root of every conjugate of `λ`**: `√(1/λ) = 1/√λ`,
`√(1/(1 − λ)) = 1/√(1 − λ)`, `√(1 − 1/λ) = √−1·√(1 − λ)/√λ`,
`√(1 − 1/(1 − λ)) = √−1·√λ/√(1 − λ)`. -/
private theorem conj_exists_sq {l m : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h : Conj l m) :
    ∃ s ∈ fieldOf' l, s ^ 2 = m := by
  have h1 : (1 : Qbar) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hs0 : sqrtLam l ≠ 0 := fun h0 ↦ hl0 (by rw [← sqrtLam_sq l, h0]; ring)
  have hs1 : sqrtOneSubLam l ≠ 0 := fun h0 ↦ h1 (by rw [← sqrtOneSubLam_sq l, h0]; ring)
  have hi := sqrtNegOne_mem_fieldOf' l
  have hs := sqrtLam_mem_fieldOf' l
  have hs' := sqrtOneSubLam_mem_fieldOf' l
  rcases h with h | h | h | h | h | h <;> subst m
  · exact ⟨sqrtLam l, hs, sqrtLam_sq l⟩
  · exact ⟨sqrtOneSubLam l, hs', sqrtOneSubLam_sq l⟩
  · exact ⟨(sqrtLam l)⁻¹, inv_mem hs, by rw [inv_pow, sqrtLam_sq]⟩
  · exact ⟨(sqrtOneSubLam l)⁻¹, inv_mem hs', by rw [inv_pow, sqrtOneSubLam_sq]⟩
  · refine ⟨sqrtNegOne * sqrtOneSubLam l / sqrtLam l, div_mem (mul_mem hi hs') hs, ?_⟩
    rw [div_pow, mul_pow, sqrtNegOne_sq, sqrtOneSubLam_sq, sqrtLam_sq]
    field_simp
    ring
  · refine ⟨sqrtNegOne * sqrtLam l / sqrtOneSubLam l, div_mem (mul_mem hi hs) hs', ?_⟩
    rw [div_pow, mul_pow, sqrtNegOne_sq, sqrtOneSubLam_sq, sqrtLam_sq]
    field_simp
    ring

/-- **The torsion coordinates of the conjugate curves lie in `F_λ`**: `E_μ ≅ E_λ` over
`F_λ` for every conjugate `μ` of `λ`, by the changes of variables `legendre_vc_one_sub` and
`legendre_vc_inv` with `u ∈ {√−1, √λ, √(1 − λ)}`, `r ∈ {0, 1}`. -/
private theorem conj_torsionCoords_subset {l m : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h : Conj l m)
    {n : ℕ} (hn : torsionCoords l n ⊆ fieldOf' l) : torsionCoords m n ⊆ fieldOf' l := by
  have h1 : (1 : Qbar) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hi0 : sqrtNegOne ≠ 0 := fun h0 ↦ by
    have := sqrtNegOne_sq
    rw [h0, zero_pow two_ne_zero] at this
    exact one_ne_zero (neg_eq_zero.mp this.symm)
  have hs0 : sqrtLam l ≠ 0 := fun h0 ↦ hl0 (by rw [← sqrtLam_sq l, h0]; ring)
  have hs1 : sqrtOneSubLam l ≠ 0 := fun h0 ↦ h1 (by rw [← sqrtOneSubLam_sq l, h0]; ring)
  have hi := sqrtNegOne_mem_fieldOf' l
  have hs := sqrtLam_mem_fieldOf' l
  have hs' := sqrtOneSubLam_mem_fieldOf' l
  -- the chain `λ → 1 − λ → 1/(1 − λ) → 1 − 1/(1 − λ)` and `λ → 1/λ → 1 − 1/λ`
  have h2 : torsionCoords (1 - l) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l) _ hi (one_mem _)
      (zero_mem _) (zero_mem _) hn
  have h3 : torsionCoords l⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtLam_sq l) hs0) _ hs (zero_mem _)
      (zero_mem _) (zero_mem _) hn
  have h4 : torsionCoords (1 - l)⁻¹ n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_inv (sqrtOneSubLam_sq l) hs1) _ hs' (zero_mem _)
      (zero_mem _) (zero_mem _) h2
  have h5 : torsionCoords (1 - l⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 l⁻¹) _ hi (one_mem _)
      (zero_mem _) (zero_mem _) h3
  have h6 : torsionCoords (1 - (1 - l)⁻¹) n ⊆ fieldOf' l :=
    torsionCoords_subset_of_vc (legendre_vc_one_sub sqrtNegOne_sq hi0 (1 - l)⁻¹) _ hi
      (one_mem _) (zero_mem _) (zero_mem _) h4
  rcases h with h | h | h | h | h | h <;> subst m
  · exact hn
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

private noncomputable abbrev fieldOfJ (l : Qbar) : IntermediateField ℚ Qbar :=
  ℚ⟮legendreJ l⟯

private theorem fieldOfJ_le_fieldOf' (l : Qbar) : fieldOfJ l ≤ fieldOf' l := by
  have hl := mem_fieldOfExtended_self l
  have h256 : (256 : Qbar) ∈ fieldOf' l := by
    have : (256 : Qbar) = ((256 : ℕ) : Qbar) := by norm_num
    rw [this]
    exact IntermediateField.natCast_mem _ _
  apply IntermediateField.adjoin_simple_le_iff.mpr
  unfold legendreJ
  exact div_mem (mul_mem h256 (pow_mem (add_mem (sub_mem (pow_mem hl 2) hl) (one_mem _)) 3))
    (mul_mem (pow_mem hl 2) (pow_mem (sub_mem hl (one_mem _)) 2))

/-- The image of the Legendre parameter under an automorphism fixing its j-invariant
is one of its six transforms. -/
private theorem conj_of_gal {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) : Conj l (σ l) := by
  have hj : σ (legendreJ l) = legendreJ l :=
    σ.commutes ⟨_, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hj' : legendreJ (σ l) = legendreJ l := (map_legendreJ σ l).symm.trans hj
  have hm0 : σ l ≠ 0 := fun h => hl0 (σ.injective (by rw [h, map_zero]))
  have hm1 : σ l ≠ 1 := fun h => hl1 (σ.injective (by rw [h, map_one]))
  have hroot : sexticEval (legendreJ l) (σ l) = 0 := by
    rw [← hj']
    unfold sexticEval legendreJ
    rw [div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hm0)
      (pow_ne_zero _ (sub_ne_zero.mpr hm1))), sub_self]
  have h₁ : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have h₂ : 1 - l ≠ 0 := sub_ne_zero.mpr hl1.symm
  have ht : l / (l - 1) = 1 - (1 - l)⁻¹ := by
    field_simp <;> ring
  have ht' : (l - 1) / l = 1 - l⁻¹ := by
    field_simp <;> ring
  have h := eq_of_sexticEval_legendreJ_eq_zero hl0 h₁ hroot
  rw [ht, ht'] at h
  unfold Conj
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem legendre_map (l : Qbar) (f : Qbar →+* Qbar) :
    (legendre l).map f = legendre (f l) := by
  ext <;> simp [legendre, WeierstrassCurve.map]

/-- `σ` maps the coordinates of `E_λ[n]` to coordinates of `E_{σ(λ)}[n]`. -/
private theorem torsionCoords_map_subset {l : Qbar} (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) {n : ℕ} {c : Qbar}
    (hc : c ∈ torsionCoords l n) : σ c ∈ torsionCoords (σ l) n := by
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hc
  cases P with
  | zero => exact absurd hcP id
  | some x y hxy =>
    have hQ : n • pointMap (legendre l) σ.toAlgHom.toRingHom
        (Point.some x y hxy) = 0 := by
      rw [← map_nsmul, hP, map_zero]
    rw [pointMap_some] at hQ
    have hxy' : (legendre (σ l)).toAffine.Nonsingular (σ x) (σ y) :=
      legendre_map l σ.toAlgHom.toRingHom ▸
        ((legendre l).toAffine.map_nonsingular σ.injective x y).mpr hxy
    have hQ' : n • Point.some (σ x) (σ y) hxy' = 0 :=
      nsmul_some_eq_zero_of_eq (legendre_map l σ.toAlgHom.toRingHom) _ hxy' n hQ
    rcases hcP with rfl | rfl
    · exact mem_torsionCoords hQ' (Set.mem_insert _ _)
    · exact mem_torsionCoords hQ' (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- **`F_λ` is stable under `Gal(ℚ̄/ℚ(j))`.** -/
private theorem gal_map_mem_fieldOf' {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (σ : Qbar ≃ₐ[fieldOfJ l] Qbar) {a : Qbar} (ha : a ∈ fieldOf' l) : σ a ∈ fieldOf' l := by
  have hconj := conj_of_gal hl0 hl1 σ
  have hsq : ∀ {s t : Qbar}, s ^ 2 = t ^ 2 → t ∈ fieldOf' l → s ∈ fieldOf' l := by
    intro s t h ht
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
    · rw [h']; exact ht
    · rw [h']; exact neg_mem ht
  unfold fieldOf' at ha
  induction ha using IntermediateField.adjoin_induction with
  | mem c hc =>
    rcases hc with (hc | hc) | hc
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with hc | hc | hc | hc <;> subst c
      · exact conj_mem hconj (mem_fieldOfExtended_self l)
      · refine hsq (t := sqrtNegOne) ?_ (sqrtNegOne_mem_fieldOf' l)
        rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
      · obtain ⟨s, hs, hs2⟩ := conj_exists_sq hl0 hl1 hconj
        refine hsq (t := s) ?_ hs
        rw [← map_pow, sqrtLam_sq, hs2]
      · obtain ⟨s, hs, hs2⟩ := conj_exists_sq hl0 hl1 (conj_one_sub hconj)
        refine hsq (t := s) ?_ hs
        rw [← map_pow, sqrtOneSubLam_sq, hs2, map_sub, map_one]
    · refine conj_torsionCoords_subset hl0 hl1 hconj ?_ (torsionCoords_map_subset σ hc)
      exact fun _ hx => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inr hx))
    · refine conj_torsionCoords_subset hl0 hl1 hconj ?_ (torsionCoords_map_subset σ hc)
      exact fun _ hx => IntermediateField.subset_adjoin ℚ _ (Or.inr hx)
  | algebraMap r =>
    have h := (σ.toAlgHom.restrictScalars ℚ).commutes r
    change σ (algebraMap ℚ Qbar r) = _ at h
    rw [h]
    exact IntermediateField.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **`F_λ/ℚ(j)` is normal.** -/
private theorem fieldOf'_normal {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    Normal (fieldOfJ l) (IntermediateField.extendScalars (fieldOfJ_le_fieldOf' l)) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  rintro σ _ ⟨a, ha, rfl⟩
  exact gal_map_mem_fieldOf' hl0 hl1 σ ha

/-- **`F_λ/ℚ(j)` is Galois.** -/
private theorem fieldOf'_isGalois {l : Qbar} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    IsGalois (fieldOfJ l) (IntermediateField.extendScalars (fieldOfJ_le_fieldOf' l)) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable (fieldOfJ l) _ Qbar
  to_normal := fieldOf'_normal hl0 hl1

/-! ### Transfer between intermediate fields of `F` and of `ℚ̄` -/

/-- The identification of `L ⊆ ℚ̄` with itself as an extension of `M' ≤ L`. -/
private def extendScalarsEquiv {L M' : IntermediateField ℚ Qbar} (h : M' ≤ L) :
    IntermediateField.extendScalars h ≃+* L where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `L/M` is Galois for `M ⊆ L ⊆ ℚ̄` if `L` is Galois over the lift `M' ⊆ ℚ̄` of `M`. -/
private theorem isGalois_of_lift_eq {L : IntermediateField ℚ Qbar} {M : IntermediateField ℚ L}
    {M' : IntermediateField ℚ Qbar} (hM : IntermediateField.lift M = M') (h : M' ≤ L)
    [IsGalois M' (IntermediateField.extendScalars h)] : IsGalois M L := by
  subst hM
  exact IsGalois.of_equiv_equiv (f := (IntermediateField.liftAlgEquiv M).symm.toRingEquiv)
    (g := extendScalarsEquiv h) (RingHom.ext fun _ ↦ rfl)

private theorem lift_fieldOfModuli (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IntermediateField.lift (modC x h3 h5) = fieldOfJ x.1 := by
  let L := fieldOf' x.1
  let j : L := (curveOf x h3 h5).E.j
  have hj : j = legendreJ (gen' x.1) := j_eq x h3 h5
  have hval : L.val j = legendreJ x.1 :=
    (congrArg L.val hj).trans (map_legendreJ L.val (gen' x.1))
  exact (IntermediateField.lift_adjoin_simple ℚ L j).trans
    (congrArg (fun a : Qbar => ℚ⟮a⟯) hval)

/-- The Legendre field of definition is Galois over the field generated by j. -/
theorem isGalois_curveOf_moduli (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    IsGalois (modC x h3 h5) (curveOf x h3 h5).F := by
  letI := fieldOf'_isGalois x.2.1 x.2.2
  exact isGalois_of_lift_eq (lift_fieldOfModuli x h3 h5) (fieldOfJ_le_fieldOf' x.1)

end AbcAdaptation.Tripod
