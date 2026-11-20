/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as stated in the upstream source header.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/PadicUnbounded.lean
-/
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

/-- If `‖d‖ < ‖t‖ ^ 2`, the quadratic `X² - t * X + d` over `ℚ_[p]` has two roots
with distinct norms. -/
theorem Padic.exists_roots_of_norm_lt {p : ℕ} [Fact p.Prime] {t d : ℚ_[p]}
    (h : ‖d‖ < ‖t‖ ^ 2) :
    ∃ μ₁ μ₂ : ℚ_[p], μ₁ + μ₂ = t ∧ μ₁ * μ₂ = d ∧ ‖μ₂‖ < ‖μ₁‖ := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact (not_lt_of_ge (norm_nonneg d)) (by simpa using h)
  have htNorm : 0 < ‖t‖ := norm_pos_iff.mpr ht
  let ε : ℚ_[p] := d / t ^ 2
  have hε : ‖ε‖ < 1 := by
    change ‖d / t ^ 2‖ < 1
    rw [norm_div, norm_pow, div_lt_one₀ (pow_pos htNorm 2)]
    exact h
  let e : ℤ_[p] := ⟨ε, hε.le⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e
  have hF : F.aeval (1 : ℤ_[p]) = e := by
    simp [F]
  have hF' : F.derivative.aeval (1 : ℤ_[p]) = 1 := by
    norm_num [F, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C]
  have hHensel : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF, hF', norm_one, one_pow]
    exact hε
  obtain ⟨z, hz, hzNear, -⟩ := hensels_lemma hHensel
  let l : ℚ_[p] := z
  have hzPoly : z ^ 2 - z + e = 0 := by
    simpa [F] using hz
  have hlPoly : l ^ 2 - l + ε = 0 := by
    have hcast := congrArg (PadicInt.Coe.ringHom (p := p)) hzPoly
    simp only [map_add, map_sub, map_pow, map_zero] at hcast
    exact hcast
  have hlNear : ‖1 - l‖ < 1 := by
    rw [hF', norm_one] at hzNear
    rw [norm_sub_rev]
    simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, l] using hzNear
  have hlNorm : 1 ≤ ‖l‖ := by
    have hsum := _root_.Padic.nonarchimedean l (1 - l)
    rw [add_sub_cancel, norm_one] at hsum
    exact (le_max_iff.mp hsum).resolve_right (not_le_of_gt hlNear)
  refine ⟨t * l, t * (1 - l), by ring, ?_, ?_⟩
  · have hd : ε * t ^ 2 = d := div_mul_cancel₀ d (pow_ne_zero 2 ht)
    linear_combination (-t ^ 2) * hlPoly + hd
  · rw [norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (hlNear.trans_le hlNorm) htNorm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
