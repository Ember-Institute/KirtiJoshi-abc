/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicArch.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

/-- The statement of `Heights.exists_torsion_x_bound` at revision
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`, from `Heights/TorsionArchimedean.lean`. -/
def ComplexTorsionXBound : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] {N : ℕ}, 1 ≤ N →
    ∀ {x y : ℂ} (h : W.toAffine.Nonsingular x y),
      N • (Affine.Point.some x y h : W.toAffine.Point) = 0 →
      ‖x + W.b₂ / 12‖ ^ 6 ≤ A * ‖W.Δ‖ * max ‖W.j‖ 1 *
        (2 * N ^ 2 + B * (Real.log (max ‖W.j‖ (Real.exp 1)) + 1) ^ 2) ^ 6

private lemma norm_bounds_of_abs_log_le {z : ℂ} (hz : z ≠ 0) {c : ℝ}
    (hc : |Real.log ‖z‖| ≤ c) : ‖z‖ ≤ Real.exp c ∧ 1 ≤ Real.exp c * ‖z‖ := by
  rw [← Real.exp_log (norm_pos_iff.mpr hz)]
  refine ⟨Real.exp_le_exp.mpr (abs_le.mp hc).2, ?_⟩
  rw [← Real.exp_add]
  exact Real.one_le_exp (by linarith only [(abs_le.mp hc).1])

private lemma legendre_j_norm_le {l : ℂ} [(legendre l).IsElliptic] {E : ℝ} (hE : 0 < E)
    (hl : ‖l‖ ≤ E) (hlo : 1 ≤ E * ‖l‖) (hlo1 : 1 ≤ E * ‖l - 1‖) :
    ‖(legendre l).j‖ ≤ 256 * (E ^ 2 + E + 1) ^ 3 * E ^ 4 := by
  have : NeZero (2 : ℂ) := ⟨two_ne_zero⟩
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl10 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  have hden : 0 < ‖l‖ ^ 2 * ‖l - 1‖ ^ 2 := by positivity
  have hq : ‖l ^ 2 - l + 1‖ ≤ E ^ 2 + E + 1 := by
    calc
      ‖l ^ 2 - l + 1‖ ≤ ‖l ^ 2‖ + ‖l‖ + ‖(1 : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ E ^ 2 + E + 1 := by rw [norm_pow, norm_one]; gcongr
  have hden' : 1 ≤ E ^ 4 * (‖l‖ ^ 2 * ‖l - 1‖ ^ 2) := by
    calc
      1 = (1 : ℝ) ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ (E * ‖l‖) ^ 2 * (E * ‖l - 1‖) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ zero_le_one hlo 2) (pow_le_pow_left₀ zero_le_one hlo1 2)
          (by norm_num) (sq_nonneg _)
      _ = _ := by ring
  have h256 : ‖(256 : ℂ)‖ = 256 := by norm_num
  rw [legendre_j, norm_div, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, h256,
    div_le_iff₀ hden]
  calc
    256 * ‖l ^ 2 - l + 1‖ ^ 3 ≤ 256 * (E ^ 2 + E + 1) ^ 3 := by gcongr
    _ ≤ 256 * (E ^ 2 + E + 1) ^ 3 * (E ^ 4 * (‖l‖ ^ 2 * ‖l - 1‖ ^ 2)) :=
      le_mul_of_one_le_right (by positivity) hden'
    _ = _ := by ring

private lemma legendre_discriminant_norm_le {l : ℂ} {E : ℝ}
    (hl : ‖l‖ ≤ E) (hl1 : ‖l - 1‖ ≤ E) : ‖(legendre l).Δ‖ ≤ 16 * E ^ 4 := by
  have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  rw [legendre_Δ, norm_mul, norm_mul, norm_pow, norm_pow, h16]
  calc
    16 * ‖l‖ ^ 2 * ‖l - 1‖ ^ 2 ≤ 16 * E ^ 2 * E ^ 2 := by gcongr
    _ = 16 * E ^ 4 := by ring

private lemma legendre_b₂_norm_le {l : ℂ} {E : ℝ} (hl : ‖l‖ ≤ E) :
    ‖(legendre l).b₂ / 12‖ ≤ (1 + E) / 3 := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
  rw [legendre_b₂, norm_div, norm_mul, norm_neg, h4, h12]
  have hsum : ‖1 + l‖ ≤ 1 + E := (norm_add_le _ _).trans (by rw [norm_one]; gcongr)
  calc
    4 * ‖1 + l‖ / 12 ≤ 4 * (1 + E) / 12 := by gcongr
    _ = (1 + E) / 3 := by ring

/-- Specialize the uniform complex torsion estimate to the bounded Legendre family. -/
theorem legendre_torsion_x_le_of_complex (hcomplex : ComplexTorsionXBound) (c : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound c C₀ := by
  obtain ⟨A, B, hA, hB, hbound⟩ := hcomplex
  set E : ℝ := Real.exp c with hE
  have hE0 : 0 < E := Real.exp_pos c
  set J : ℝ := 256 * (E ^ 2 + E + 1) ^ 3 * E ^ 4 with hJ
  set M : ℝ := A * (16 * E ^ 4) * max J 1 with hM
  set Bj : ℝ := B * (Real.log (max J (Real.exp 1)) + 1) ^ 2 with hBj
  have hBj0 : 0 ≤ Bj := mul_nonneg hB (sq_nonneg _)
  have hmax : 1 ≤ max 1 M := le_max_left _ _
  have hmax0 : 0 ≤ max 1 M := zero_le_one.trans hmax
  refine ⟨max 1 M * (2 + Bj) + (1 + E) / 3, by positivity, ?_⟩
  intro l hl hl1 W _ hW N hN x y h hP
  subst W
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl10 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  obtain ⟨hup, hlow⟩ := norm_bounds_of_abs_log_le hl0 hl
  obtain ⟨hup1, hlow1⟩ := norm_bounds_of_abs_log_le hl10 hl1
  have hj : ‖(legendre l).j‖ ≤ J := legendre_j_norm_le hE0 hup hlow hlow1
  have hΔ := legendre_discriminant_norm_le hup hup1
  have hb₂ := legendre_b₂_norm_le hup
  set Q : ℝ := 2 * N ^ 2 + Bj with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hlogj : Real.log (max ‖(legendre l).j‖ (Real.exp 1)) ≤
      Real.log (max J (Real.exp 1)) :=
    Real.log_le_log (lt_max_of_lt_right (Real.exp_pos 1)) (max_le_max hj le_rfl)
  have hlogj0 : 0 ≤ Real.log (max ‖(legendre l).j‖ (Real.exp 1)) :=
    Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (le_max_right _ _))
  have h6 : ‖x + (legendre l).b₂ / 12‖ ^ 6 ≤ M * Q ^ 6 := by
    refine (hbound (legendre l) hN h hP).trans ?_
    rw [hM, hQ, hBj]
    gcongr
  have hmM : M ≤ max 1 M ^ 6 :=
    (le_max_right _ _).trans (le_self_pow₀ hmax (by norm_num))
  have hshift : ‖x + (legendre l).b₂ / 12‖ ≤ max 1 M * Q := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (mul_nonneg hmax0 hQ0) ?_
    calc
      ‖x + (legendre l).b₂ / 12‖ ^ 6 ≤ M * Q ^ 6 := h6
      _ ≤ max 1 M ^ 6 * Q ^ 6 := mul_le_mul_of_nonneg_right hmM (pow_nonneg hQ0 _)
      _ = (max 1 M * Q) ^ 6 := (mul_pow _ _ _).symm
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hN
  have hQle : Q ≤ (2 + Bj) * (N : ℝ) ^ 2 := by
    calc
      Q = 2 * (N : ℝ) ^ 2 + Bj := hQ
      _ ≤ 2 * (N : ℝ) ^ 2 + Bj * (N : ℝ) ^ 2 :=
        add_le_add le_rfl (le_mul_of_one_le_right hBj0 hN1)
      _ = _ := by ring
  calc
    ‖x‖ = ‖(x + (legendre l).b₂ / 12) - (legendre l).b₂ / 12‖ := by
      rw [add_sub_cancel_right]
    _ ≤ ‖x + (legendre l).b₂ / 12‖ + ‖(legendre l).b₂ / 12‖ := norm_sub_le _ _
    _ ≤ max 1 M * Q + (1 + E) / 3 := add_le_add hshift hb₂
    _ ≤ max 1 M * ((2 + Bj) * (N : ℝ) ^ 2) + ((1 + E) / 3) * (N : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hQle hmax0)
        (le_mul_of_one_le_right (by positivity) hN1)
    _ = _ := by ring

end AbcAdaptation.Tripod
