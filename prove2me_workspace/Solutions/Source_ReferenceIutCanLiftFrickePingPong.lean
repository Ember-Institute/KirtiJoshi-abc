/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/PingPong.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Tactic.FinCases
import Solutions.Source_ReferenceIutCanLiftFrickeNormalForm

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Topology
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

/-- The basic Möbius computation. -/
private theorem normSq_mul_re_smul_sub (g : SL(2, ℝ)) (v : ℝ) (hv : g 0 1 = v * g 1 1) (w : ℍ) :
    Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) * ((g • w).re - v) =
      g 1 0 * (g 0 0 - v * g 1 0) * Complex.normSq (w : ℂ) + w.re := by
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
    simpa [UpperHalfPlane.denom] using this
  have hN : Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  have hre : (g • w).re = ((g 0 0 * (w : ℂ) + g 0 1) / (g 1 0 * (w : ℂ) + g 1 1)).re := by
    rw [UpperHalfPlane.re, coe_specialLinearGroup_apply]; simp
  set N := Complex.normSq (g 1 0 * (w : ℂ) + g 1 1)
  have hNe : N = (g 1 0 * w.re + g 1 1) ^ 2 + (g 1 0 * w.im) ^ 2 := by
    simp only [N, Complex.normSq_apply]; simp; ring
  have key : (g • w).re = ((g 0 0 * w.re + g 0 1) * (g 1 0 * w.re + g 1 1) +
      (g 0 0 * w.im) * (g 1 0 * w.im)) / N := by
    rw [hre, Complex.div_re]
    simp only [N]
    simp [Complex.normSq_apply]
    ring
  rw [key, mul_sub, mul_div_cancel₀ _ hN, hNe, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [hv]
  rw [hv] at hdet
  linear_combination (w.re) * hdet

/-- The sign form: with `κ = c(a - vc) ≠ 0` and `m = -1/(2κ)`, `Re(g w) - v` has the sign of
`κ (|w - m|² - m²)`. -/
private theorem re_smul_sub_eq (g : SL(2, ℝ)) (v κ : ℝ) (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ ≠ 0) (w : ℍ) :
    ∃ N > 0, N * ((g • w).re - v) =
      κ * (Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) - (1 / (2 * κ)) ^ 2) := by
  refine ⟨Complex.normSq (g 1 0 * (w : ℂ) + g 1 1), ?_, ?_⟩
  · have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
      simpa [UpperHalfPlane.denom] using this
    exact Complex.normSq_pos.mpr hden
  rw [normSq_mul_re_smul_sub g v hv w, hκ]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp [hκ0] <;> ring

private theorem re_gt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    v < (g • w).re := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' w
  have : 0 < N * ((g • w).re - v) := by rw [h]; exact mul_pos hκ0 (by linarith)
  have := (pos_iff_pos_of_mul_pos this).mp hN
  linarith

private theorem re_lt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    (g • w).re < v := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne w
  have : N * ((g • w).re - v) < 0 := by rw [h]; exact mul_neg_of_neg_of_pos hκ0 (by linarith)
  by_contra hc; push Not at hc; nlinarith

private theorem in_of_re_lt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ} (hw : w.re < v) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : N * (w.re - v) < 0 := mul_neg_of_pos_of_neg hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

private theorem in_of_re_gt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ} (hw : v < w.re) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : 0 < N * (w.re - v) := mul_pos hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

/-- Points of a closed disc `|w - m|² ≤ m²` have real part between `0` and `2m`. -/
private theorem re_mem_of_normSq_le {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) ≤ m ^ 2) :
    min 0 (2 * m) ≤ w.re ∧ w.re ≤ max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 ≤ m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

private theorem re_mem_of_normSq_lt {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) < m ^ 2) :
    min 0 (2 * m) < w.re ∧ w.re < max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 < m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

section NormalForm

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The four ping-pong regions and the open quadrilateral. With `v₁ = -y/(xz)`, `v₃ = x/(yz)`:
`mA = v₁/2`, `mB = v₃/2`. -/
noncomputable def ppX (x y z : ℝ) : Fin 2 × Bool → Set ℍ
  | (0, true) => {w | x / (y * z) < w.re}
  | (0, false) => {w | Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) <
      (-y / (2 * x * z)) ^ 2}
  | (1, true) => {w | w.re < -y / (x * z)}
  | (1, false) => {w | Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) <
      (x / (2 * y * z)) ^ 2}

/-- The open fundamental quadrilateral. -/
def ppQ (x y z : ℝ) : Set ℍ :=
  {w | (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) ∧
    (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) ∧
    -y / (x * z) < w.re ∧ w.re < x / (y * z)}

/-- The generators as letters. -/
noncomputable def ppGen : Fin 2 × Bool → SL(2, ℝ)
  | (0, true) => nA hz hrel
  | (0, false) => (nA hz hrel)⁻¹
  | (1, true) => nB hz hrel
  | (1, false) => (nB hz hrel)⁻¹

include hx hy in
private theorem nA_hv : (nA hz hrel : SL(2, ℝ)) 0 1 = x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
private theorem nA_hκ : (nA hz hrel : SL(2, ℝ)) 1 0 * ((nA hz hrel : SL(2, ℝ)) 0 0 -
    x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 0) = x * z / y := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp [hx.ne', hy.ne', hz.ne']
  grind

include hx hy in
private theorem nB_hv : (nB hz hrel : SL(2, ℝ)) 0 1 = -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
private theorem nB_hκ : (nB hz hrel : SL(2, ℝ)) 1 0 * ((nB hz hrel : SL(2, ℝ)) 0 0 -
    -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 0) = -(y * z / x) := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp [hx.ne', hy.ne', hz.ne']
  grind

include hx hy hz in
private theorem pp_facts :
    (-y / (x * z) < 0) ∧ (0 < x / (y * z)) ∧ 2 * (-y / (2 * x * z)) = -y / (x * z) ∧
      2 * (x / (2 * y * z)) = x / (y * z) ∧
      -1 / (2 * (x * z / y)) = -y / (2 * x * z) ∧
      (1 / (2 * (x * z / y))) ^ 2 = (-y / (2 * x * z)) ^ 2 ∧
      -1 / (2 * -(y * z / x)) = x / (2 * y * z) ∧
      (1 / (2 * -(y * z / x))) ^ 2 = (x / (2 * y * z)) ^ 2 := by
  refine ⟨?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [neg_div]
    exact neg_lt_zero.mpr (div_pos hy (mul_pos hx hz))
  all_goals field_simp

include hx hy in
/-- **Ping-pong step.** -/
lemma pp_step (s t : Fin 2 × Bool) (hst : s.1 = t.1 → s.2 = t.2) :
    ppGen hz hrel s • ppX x y z t ⊆ ppX x y z s := by
  obtain ⟨hv1, hv3, e1, e3, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  -- domains
  have domA : ∀ w : ℍ, w.re < -y / (x * z) ∨ 0 < w.re →
      (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := -y / (2 * x * z)) hc
    rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  have domB : ∀ w : ℍ, w.re < 0 ∨ x / (y * z) < w.re →
      (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := x / (2 * y * z)) hc
    rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  -- facts about the regions
  have hX : ∀ w : ℍ, w ∈ ppX x y z t →
      (t = (0, true) ∧ x / (y * z) < w.re) ∨ (t = (1, true) ∧ w.re < -y / (x * z)) ∨
      (t = (0, false) ∧ -y / (x * z) < w.re ∧ w.re < 0) ∨
      (t = (1, false) ∧ 0 < w.re ∧ w.re < x / (y * z)) := by
    intro w hw
    obtain ⟨j, c⟩ := t
    fin_cases j <;> cases c
    · right; right; left
      have := re_mem_of_normSq_lt (m := -y / (2 * x * z)) hw
      rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
      exact ⟨rfl, this⟩
    · left; exact ⟨rfl, hw⟩
    · right; right; right
      have := re_mem_of_normSq_lt (m := x / (2 * y * z)) hw
      rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
      exact ⟨rfl, this⟩
    · right; left; exact ⟨rfl, hw⟩
  -- actions
  have actA : ∀ w : ℍ, (-y / (2 * x * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) →
        nA hz hrel • w ∈ ppX x y z (0, true) := by
    intro w hw
    exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  have actAi : ∀ w : ℍ, w.re < x / (y * z) → (nA hz hrel)⁻¹ • w ∈ ppX x y z (0, false) := by
    intro w hw
    have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hw
    rwa [emA, erA] at this
  have actB : ∀ w : ℍ, (x / (2 * y * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) →
        nB hz hrel • w ∈ ppX x y z (1, true) := by
    intro w hw
    exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])
  have actBi : ∀ w : ℍ, -y / (x * z) < w.re → (nB hz hrel)⁻¹ • w ∈ ppX x y z (1, false) := by
    intro w hw
    have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hw
    rwa [emB, erB] at this
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨i, b⟩ := s
  rcases hX w hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
  fin_cases i <;> cases b <;> simp at hst <;> simp only [ppGen] <;>
  first
    | exact actA w (domA w (by first | (left; linarith) | (right; linarith)))
    | exact actAi w (by linarith)
    | exact actB w (domB w (by first | (left; linarith) | (right; linarith)))
    | exact actBi w (by linarith)

include hx hy in
lemma pp_stepQ (s : Fin 2 × Bool) : ppGen hz hrel s • ppQ x y z ⊆ ppX x y z s := by
  obtain ⟨-, -, -, -, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  rintro _ ⟨w, ⟨hq1, hq2, hq3, hq4⟩, rfl⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppGen]
  · have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hq4
    rwa [emA, erA] at this
  · exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  · have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hq3
    rwa [emB, erB] at this
  · exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])

lemma ppX_disjoint_Q (s : Fin 2 × Bool) : Disjoint (ppX x y z s) (ppQ x y z) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨hq1, hq2, hq3, hq4⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppX, Set.mem_setOf_eq] at hw <;> linarith

include hx hy hz in
lemma ppQ_nonempty : (ppQ x y z).Nonempty := by
  obtain ⟨hv1, hv3, -⟩ := pp_facts hx hy hz
  have key : ∀ m : ℝ, m ^ 2 < Complex.normSq (Complex.I - (m : ℂ)) := by
    intro m; rw [Complex.normSq_apply]; simp; nlinarith
  have hre : (⟨Complex.I, by simp⟩ : ℍ).re = 0 := by simp [UpperHalfPlane.re]
  exact ⟨⟨Complex.I, by simp⟩, key _, key _, by rw [hre]; exact hv1, by rw [hre]; exact hv3⟩

lemma ppQ_isOpen : IsOpen (ppQ x y z) := by
  have h1 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    fun_prop
  have h2 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    fun_prop
  simp only [ppQ, Set.setOf_and]
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)))

end NormalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
