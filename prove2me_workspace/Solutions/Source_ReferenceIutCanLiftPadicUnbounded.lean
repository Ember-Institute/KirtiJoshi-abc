/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as stated in the upstream source header.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/PadicUnbounded.lean
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic.Abel
import Solutions.Source_ReferenceIutCanLiftPadicCharacteristicRoots
import Solutions.Source_ReferenceIutCanLiftThreePoint

set_option autoImplicit false

/-!
# Degenerate limits of powers of a p-adic matrix

Distinct norms of the characteristic roots give a dominant term in the formula for the powers.
The matrix in this term has rank one. At least two points of the standard triple have the same
projective limit.
-/

open Filter OnePoint OnePoint.Proj Topology
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

section MatrixIdentities

variable {k : Type*} [Field k]

private theorem mul_sub_smul_one_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) :
    M * (M - μ₂ • 1) = μ₁ • (M - μ₂ • 1) := by
  rw [Matrix.trace_fin_two] at hs
  rw [Matrix.det_fin_two] at hp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination (-M 0 0) * hs + hp
  · linear_combination (-M 0 1) * hs
  · linear_combination (-M 1 0) * hs
  · linear_combination (-M 1 1) * hs + hp

private theorem pow_mul_sub_smul_one_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) (n : ℕ) :
    M ^ n * (M - μ₂ • 1) = μ₁ ^ n • (M - μ₂ • 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, mul_sub_smul_one_eq hs hp, Matrix.mul_smul, ih, smul_smul,
      pow_succ']

private theorem sub_smul_pow_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) (n : ℕ) :
    (μ₁ - μ₂) • M ^ n = μ₁ ^ n • (M - μ₂ • 1) - μ₂ ^ n • (M - μ₁ • 1) := by
  have hdiff : (μ₁ - μ₂) • (1 : Matrix (Fin 2) (Fin 2) k) =
      (M - μ₂ • 1) - (M - μ₁ • 1) := by
    rw [sub_smul]
    abel
  rw [← mul_one (M ^ n), ← Matrix.mul_smul, hdiff, mul_sub, pow_mul_sub_smul_one_eq hs hp,
    pow_mul_sub_smul_one_eq ((add_comm μ₂ μ₁).trans hs) ((mul_comm μ₂ μ₁).trans hp)]

private theorem det_sub_smul_one_eq_zero {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) : (M - μ₂ • 1).det = 0 := by
  rw [Matrix.trace_fin_two] at hs
  rw [Matrix.det_fin_two] at hp ⊢
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, mul_one, sub_zero]
  linear_combination μ₂ * hs - hp

private theorem br_mv_padic (A : Matrix (Fin 2) (Fin 2) k) (u w : k × k) :
    br (mv A u) (mv A w) = A.det * br u w := by
  simp only [br, mv, Matrix.det_fin_two]
  ring

end MatrixIdentities

/-- If the determinant norm is smaller than the squared trace norm, the images of
`(0, 1, ∞)` under the powers converge to a triple with a repeated point. -/
theorem Padic.exists_degenerate_limit {p : ℕ} [Fact p.Prime] [DecidableEq ℚ_[p]]
    (R : GL (Fin 2) ℚ_[p])
    (h : ‖(R : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ <
      ‖(R : Matrix (Fin 2) (Fin 2) ℚ_[p]).trace‖ ^ 2) :
    ∃ τ : Triple ℚ_[p], ¬ Distinct3 τ ∧
      Tendsto (fun n : ℕ ↦ smul3 (R ^ n) e₃) atTop (𝓝 τ) := by
  set M : Matrix (Fin 2) (Fin 2) ℚ_[p] := ↑R with hM
  obtain ⟨μ₁, μ₂, hs, hp, hlt⟩ := Padic.exists_roots_of_norm_lt h
  have hμ₁ : μ₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hlt)
  have hμ₂ : μ₂ ≠ 0 := by
    rintro rfl
    exact R.det_ne_zero (by rw [← hM, ← hp, mul_zero])
  have h12 : μ₁ - μ₂ ≠ 0 := sub_ne_zero.mpr fun he ↦
    (ne_of_lt hlt) (congrArg norm he.symm)
  set A := M - μ₂ • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hA
  set B := M - μ₁ • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])
  set q := μ₂ / μ₁ with hq
  have hqNorm : ‖q‖ < 1 := by
    rw [hq, norm_div, div_lt_one₀ (norm_pos_iff.mpr hμ₁)]
    exact hlt
  have hq0 : q ≠ 0 := div_ne_zero hμ₂ hμ₁
  have hmob (n : ℕ) (w : OnePoint ℚ_[p]) :
      (R ^ n) • w = proj (mv A (lift w) - q ^ n • mv B (lift w)) := by
    have hpow : (μ₁ - μ₂) • M ^ n = μ₁ ^ n • A - μ₂ ^ n • B :=
      sub_smul_pow_eq hs hp n
    have hscaled : (μ₁ ^ n)⁻¹ • (μ₁ ^ n • A - μ₂ ^ n • B) = A - q ^ n • B := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hμ₁), one_smul,
        hq, div_pow, div_eq_inv_mul]
    rw [gl_smul_eq_mob, Units.val_pow_eq_pow_val, ← hM, ← mob_smul_matrix h12, hpow,
      ← mob_smul_matrix (inv_ne_zero (pow_ne_zero n hμ₁)), hscaled, mob]
    congr 1
    simp only [mv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk,
      Prod.mk_sub_mk]
    congr 1 <;> ring
  let φ : OnePoint ℚ_[p] → OnePoint ℚ_[p] := fun w ↦
    if mv A (lift w) = 0 then proj (mv B (lift w)) else proj (mv A (lift w))
  have hlim (w : OnePoint ℚ_[p]) : Tendsto (fun n : ℕ ↦ (R ^ n) • w) atTop (𝓝 (φ w)) := by
    simp only [hmob, φ]
    split_ifs with hAw
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [hAw, zero_sub, ← neg_smul, proj_smul (neg_ne_zero.mpr (pow_ne_zero n hq0))]
    · have hqn : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqNorm
      have hv : Tendsto (fun n : ℕ ↦ mv A (lift w) - q ^ n • mv B (lift w)) atTop
          (𝓝 (mv A (lift w))) := by
        simpa only [zero_smul, sub_zero] using
          (tendsto_const_nhds (x := mv A (lift w))).sub (hqn.smul_const (mv B (lift w)))
      exact (continuousAt_proj hAw).tendsto.comp hv
  refine ⟨(φ (0 : ℚ_[p]), φ (1 : ℚ_[p]), φ ∞), ?_, ?_⟩
  · have hdetA : A.det = 0 := det_sub_smul_one_eq_zero hs hp
    have hsame {u w : ℚ_[p] × ℚ_[p]} (hu : mv A u ≠ 0) (hw : mv A w ≠ 0) :
        proj (mv A u) = proj (mv A w) := by
      rw [proj_eq_proj_iff hu hw, br_mv_padic, hdetA, zero_mul]
    have hnot : ¬ (mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) = 0 ∧
        mv A (lift (∞ : OnePoint ℚ_[p])) = 0) := by
      rintro ⟨h0, hinfty⟩
      simp only [lift_coe, lift_infty, mv, hA, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, Prod.ext_iff, Prod.fst_zero,
        Prod.snd_zero, Matrix.one_apply_eq,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero, sub_eq_zero] at h0 hinfty
      have htrace := hs
      rw [Matrix.trace_fin_two, hinfty.1, h0.2] at htrace
      exact (ne_of_lt hlt) (congrArg norm (add_right_cancel htrace).symm)
    have hsum : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) =
        mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) + mv A (lift (∞ : OnePoint ℚ_[p])) := by
      simp only [lift_coe, lift_infty, mv, Prod.mk_add_mk]
      congr 1 <;> ring
    simp only [Distinct3, not_and_or, not_not]
    by_cases h0 : mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) = 0
    · have hinfty : mv A (lift (∞ : OnePoint ℚ_[p])) ≠ 0 := fun hh ↦ hnot ⟨h0, hh⟩
      have h1 : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) ≠ 0 := by
        rwa [hsum, h0, zero_add]
      right
      right
      simp only [φ, if_neg h1, if_neg hinfty]
      exact hsame h1 hinfty
    · by_cases hinfty : mv A (lift (∞ : OnePoint ℚ_[p])) = 0
      · have h1 : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) ≠ 0 := by
          rwa [hsum, hinfty, add_zero]
        left
        simp only [φ, if_neg h1, if_neg h0]
        exact hsame h0 h1
      · right
        left
        simp only [φ, if_neg h0, if_neg hinfty]
        exact hsame h0 hinfty
  · exact (hlim _).prodMk_nhds ((hlim _).prodMk_nhds (hlim _))

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
