/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableOdd.lean
-/
import Solutions.Source_ReferenceIutStableModel
import Solutions.Source_TripodFinitePlaceArithmetic
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
open scoped Classical

/-! ## The Legendre model at a place of odd residue characteristic -/

section Legendre


variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ)

/-- The Legendre model of an integral parameter is integral. -/
private lemma isIntegralModel_legendre {l : K} (hl : v l ≤ 1) : IsIntegralModel v (legendre l) := by
  refine ⟨by simp, ?_, by simp, hl, by simp⟩
  rw [legendre_a₂, ← Valuation.mem_integer_iff] at *
  exact neg_mem (add_mem (one_mem _) hl)

/-- `v(λ² − λ + 1) = 1` if `v(λ) < 1`. -/
private lemma valuation_sq_sub_add_one_eq_one_of_lt {l : K} (hl : v l < 1) : v (l ^ 2 - l + 1) = 1 := by
  have h : v (l ^ 2 - l) < v 1 := by
    rw [map_one]
    refine lt_of_le_of_lt (Valuation.map_sub v _ _) (max_lt ?_ hl)
    rw [map_pow]
    exact pow_lt_one₀ zero_le hl (by norm_num)
  rw [Valuation.map_add_eq_of_lt_right v h, map_one]

/-- `v(λ² − λ + 1) = 1` if `v(λ) ≤ 1` and `v(λ − 1) < 1`. -/
private lemma valuation_sq_sub_add_one_eq_one_of_sub_lt {l : K} (hl : v l ≤ 1) (hl1 : v (l - 1) < 1) :
    v (l ^ 2 - l + 1) = 1 := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  have h : v (l * (l - 1)) < v 1 := by
    rw [map_one, map_mul]
    exact (mul_le_of_le_one_left zero_le hl).trans_lt hl1
  rw [e, Valuation.map_add_eq_of_lt_right v h, map_one]

/-- **The Legendre model at a place of odd residue characteristic** (`v(2) = 1`) with
`v(λ) ≤ 1`: it is good if `λ` and `λ − 1` are units, and satisfies the multiplicative model inequalities otherwise. -/
private lemma isStableModel_legendre (h2 : v 2 = 1) {l : K} (hl : v l ≤ 1) :
    IsStableModel v (legendre l) := by
  have h16 : v 16 = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have hint := isIntegralModel_legendre v hl
  have hl1 : v (l - 1) ≤ 1 := by
    rw [← Valuation.mem_integer_iff] at *
    exact sub_mem hl (one_mem _)
  have hΔ : v (legendre l).Δ = v l ^ 2 * v (l - 1) ^ 2 := by
    rw [legendre_Δ, map_mul, map_mul, map_pow, map_pow, h16, one_mul]
  by_cases hu : v l = 1 ∧ v (l - 1) = 1
  · left
    refine ⟨hint, ?_⟩
    rw [hΔ, hu.1, hu.2, one_pow, one_mul]
  · right
    refine ⟨hint, ?_, ?_⟩
    · rw [hΔ]
      rcases not_and_or.mp hu with h | h
      · have hlt : v l < 1 := lt_of_le_of_ne hl h
        exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hl1)).trans_lt
          (pow_lt_one₀ zero_le hlt (by norm_num))
      · have hlt : v (l - 1) < 1 := lt_of_le_of_ne hl1 h
        exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hl)).trans_lt
          (pow_lt_one₀ zero_le hlt (by norm_num))
    · rw [legendre_c₄, map_mul, h16, one_mul]
      rcases not_and_or.mp hu with h | h
      · exact valuation_sq_sub_add_one_eq_one_of_lt v (lt_of_le_of_ne hl h)
      · exact valuation_sq_sub_add_one_eq_one_of_sub_lt v hl (lt_of_le_of_ne hl1 h)

/-- **The change of variables `x = λX`, `y = λ√λ Y`** (`u = √λ`) transforms the Legendre
curve `E_λ` into `E_{1/λ}`. -/
private lemma legendre_variableChange {s l : K} (hs : s ^ 2 = l) (hs0 : s ≠ 0) :
    (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange K) • legendre l = legendre l⁻¹ := by
  subst hs
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  · ring
  · field_simp
    ring
  · ring
  · field_simp
    ring
  · ring

end Legendre

section LegendrePlace

variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- **Stable reduction of a Legendre curve at a place of odd residue characteristic**, for a
parameter `λ ≠ 0` with `√λ ∈ F`: the Legendre model itself if `λ` is `w`-integral, the
model `E_{1/λ}` otherwise. -/
theorem hasStableReductionAt_legendre (hw : residueChar w ≠ 2) {l : F} (h0 : l ≠ 0) {s : F}
    (hs : s ^ 2 = l) : HasStableReductionAt (legendre l) w := by
  have h2 := valuation_two_eq_one_of_ne hw
  by_cases hl : w.maximalIdeal.valuation F l ≤ 1
  · refine hasStableReductionAt_of_isStableModel _ w 1 ?_
    rw [one_smul]
    exact isStableModel_legendre _ h2 hl
  · have hs0 : s ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hs]; ring)
    refine hasStableReductionAt_of_isStableModel _ w ⟨Units.mk0 s hs0, 0, 0, 0⟩ ?_
    rw [legendre_variableChange hs hs0]
    refine isStableModel_legendre _ h2 ?_
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hl))

end LegendrePlace

/-- The actual Legendre curve has stable reduction at every finite place of odd residue
characteristic. -/
theorem stable_reduction_of_residueChar_ne_two (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (w : FinitePlace (curveOf x h3 h5).F) (hw : residueChar w ≠ 2) :
    HasStableReductionAt (curveOf x h3 h5).E w := by
  let s : (curveOf x h3 h5).F :=
    ⟨sqrtLam x.1, IntermediateField.subset_adjoin ℚ _
      (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))⟩
  exact hasStableReductionAt_legendre w hw (gen'_ne_zero x.2.1)
    (show s ^ 2 = gen' x.1 from Subtype.ext (sqrtLam_sq x.1))

end AbcAdaptation.Tripod
