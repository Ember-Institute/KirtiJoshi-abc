/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Depth.lean
-/
import Solutions.Source_ReferenceHeightsWeierstrassPrincipalPart
import Solutions.Source_ReferenceIutCanLiftLatticeCuspHeight
import Solutions.Source_ReferenceIutCanLiftLatticeDepthGeometry

set_option autoImplicit false

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} {U : LatticeComplementCover (periodPair t)}

private theorem log_bounds_of_sq_mul {P r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hP0 : 0 ≤ P)
    (hle : P * r ^ 2 ≤ 3 / 2) (hge : 1 / 2 ≤ P * r ^ 2) :
    Real.log (1 + P) ≤ Real.log 3 + 2 * Real.log (1 / r) ∧
      Real.log (1 / r) ≤ (Real.log (2 + P) + Real.log 2) / 2 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hlogw : Real.log (1 / r ^ 2) = 2 * Real.log (1 / r) := by
    simp only [one_div, Real.log_inv, Real.log_pow]
    push_cast <;> ring
  constructor
  · have hx : 1 ≤ 1 / r ^ 2 := by
      rw [le_div_iff₀ hr2, one_mul]
      nlinarith
    have h1 : 1 + P ≤ 3 * (1 / r ^ 2) := by
      have : P ≤ (3 / 2) * (1 / r ^ 2) := by
        rw [mul_one_div, le_div_iff₀ hr2]
        exact hle
      linarith
    calc
      Real.log (1 + P) ≤ Real.log (3 * (1 / r ^ 2)) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + 2 * Real.log (1 / r) := by
        rw [Real.log_mul (by norm_num) (by positivity), hlogw]
  · have hx : 1 / r ^ 2 ≤ 2 * (2 + P) := by
      rw [div_le_iff₀ hr2]
      nlinarith only [hge, sq_nonneg r]
    have hlog := Real.log_le_log (by positivity : 0 < 1 / r ^ 2) hx
    rw [hlogw, Real.log_mul (by norm_num) (by positivity)] at hlog
    linarith only [hlog]

private theorem exists_weierstrass_log_bounds (L : PeriodPair) :
    ∃ ε > 0, ∀ w ∈ ball (0 : ℂ) ε, w ≠ 0 →
      Real.log (1 + ‖L.weierstrassP w‖) ≤ Real.log 3 + 2 * Real.log (1 / ‖w‖) ∧
        Real.log (1 / ‖w‖) ≤ (Real.log (2 + ‖L.weierstrassP w‖) + Real.log 2) / 2 := by
  obtain ⟨ε, hε, hε℘⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp ((tendsto_sq_mul_weierstrassP_zero L).eventually
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))))
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun w hw hw0 ↦ ?_⟩
  have hnorm : ‖w‖ < 1 := (mem_ball_zero_iff.mp hw).trans_le (min_le_right _ _)
  have hnear : ‖w ^ 2 * L.weierstrassP w - 1‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hε℘ w (ball_subset_ball (min_le_left _ _) hw) hw0
  have hupper := norm_sub_norm_le (w ^ 2 * L.weierstrassP w) 1
  have hlower := norm_sub_norm_le 1 (w ^ 2 * L.weierstrassP w)
  rw [norm_mul, norm_pow, norm_one] at hupper
  rw [norm_mul, norm_pow, norm_one, norm_sub_rev] at hlower
  apply log_bounds_of_sq_mul (norm_pos_iff.mpr hw0) hnorm (norm_nonneg _)
  · rw [mul_comm]
    linarith only [hupper, hnear]
  · rw [mul_comm]
    linarith only [hlower, hnear]

/-- Near the lattice puncture, logarithmic Weierstrass growth and exponential depth
bound one another. -/
theorem cusp_estimates (c : CuspData U) : ∃ ε > 0, ε ≤ c.r₁ ∧ ∃ A B : ℝ,
    ∀ w ∈ ball (0 : ℂ) ε, w ≠ 0 →
      Real.log (1 + ‖(periodPair t).weierstrassP w‖) ≤
          A * Real.exp (depth U (Sig U (Complex.log w))) + B ∧
        Real.exp (depth U (Sig U (Complex.log w))) ≤
          A * Real.log (2 + ‖(periodPair t).weierstrassP w‖) + B := by
  obtain ⟨h, hh⟩ := exists_orbit_height c
  obtain ⟨ε₁, hε₁, hweierstrass⟩ := exists_weierstrass_log_bounds (periodPair t)
  let H := max h 1
  let a := c.κ / (2 * π)
  let Φ := c.Φ
  have hH : 0 < H := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκ := c.κ_pos
  have ha : 0 < a := by dsimp [a]; positivity
  have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (c.φ_le 0 (mem_ball_self c.r₁_pos))
  let ε := min (min c.r₁ ε₁) (Real.exp (-(Φ + 1 / a)))
  have hε : 0 < ε := lt_min (lt_min c.r₁_pos hε₁) (Real.exp_pos _)
  have hεr : ε ≤ c.r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hεr₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hεexp : ε ≤ Real.exp (-(Φ + 1 / a)) := min_le_right _ _
  let z₀ : ℍ := c.M⁻¹ • e₀ U
  let R := a * (π + Φ) + |z₀.re|
  let C := (R ^ 2 + z₀.im ^ 2) / z₀.im
  let K := a / z₀.im
  let A := max (2 * (H / a)) K
  let B := |Real.log 3| + 2 * Φ + C + K * (Φ + Real.log 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := (div_pos ha z₀.im_pos).le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB₀ : 0 ≤ K * (Φ + Real.log 2) := mul_nonneg hK (add_nonneg hΦ0 hlog2)
  refine ⟨ε, hε, hεr, A, B, fun w hw hw0 ↦ ?_⟩
  have hw₀ : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hw₁ : ‖w‖ < ε := mem_ball_zero_iff.mp hw
  let s := Complex.log w
  let ℓ := -s.re
  have hℓ : ℓ = Real.log (1 / ‖w‖) := by
    simp only [ℓ, s, Complex.log_re, one_div, Real.log_inv]
  have hℓbig : Φ + 1 / a < ℓ := by
    rw [hℓ, one_div ‖w‖, Real.log_inv, lt_neg]
    calc
      Real.log ‖w‖ < Real.log ε := Real.log_lt_log hw₀ hw₁
      _ ≤ Real.log (Real.exp (-(Φ + 1 / a))) := Real.log_le_log hε hεexp
      _ = -(Φ + 1 / a) := Real.log_exp _
  have hs : s.re < Real.log c.r₁ := log_mem_ball c (ball_subset_ball hεr hw) hw0
  have hsim : |s.im| ≤ π := by
    change |(Complex.log w).im| ≤ π
    rw [Complex.log_im]
    exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
  have hexp_s : Complex.exp s = w := Complex.exp_log hw0
  have hφw := c.φ_le w (ball_subset_ball hεr hw)
  have hφre : |(c.φ w).re| ≤ Φ := (abs_re_le_norm _).trans hφw
  have hφim : |(c.φ w).im| ≤ Φ := (abs_im_le_norm _).trans hφw
  let z : ℍ := c.M⁻¹ • Sig U s
  let E := Real.exp (depth U (Sig U s))
  let P := ‖(periodPair t).weierstrassP w‖
  have hzim : z.im = a * (ℓ - (c.φ w).re) := by
    change (τ' U c.M s).im = _
    simpa only [a, ℓ, hexp_s] using τ'_im c hs
  have hzre : z.re = a * (s.im + (c.φ w).im) := by
    change (τ' U c.M s).re = _
    simpa only [a, hexp_s] using τ'_re c hs
  have hzim₁ : 1 ≤ z.im := by
    rw [hzim]
    apply (div_le_iff₀' ha).mp
    linarith only [hℓbig, (abs_le.mp hφre).2]
  have hzreR : |z.re - z₀.re| ≤ R := by
    rw [hzre]
    calc
      |a * (s.im + (c.φ w).im) - z₀.re| ≤ |a * (s.im + (c.φ w).im)| + |z₀.re| := abs_sub _ _
      _ ≤ R := by
        rw [abs_mul, abs_of_pos ha]
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hsim hφim)) ha.le) _
  have hheight : z.im ≤ H * E :=
    im_le_bound_mul_exp_depth hH (fun γ hγ ↦ (hh γ hγ).trans (le_max_left _ _)) (Sig U s)
  have hE : E ≤ C + z.im / z₀.im :=
    exp_depth_le_of_cusp_coordinates (U := U) (M := c.M) (Sig U s) hzreR hzim₁
  obtain ⟨hlog₁, hlog₂⟩ := hweierstrass w (ball_subset_ball hεr₁ hw) hw0
  rw [← hℓ] at hlog₁ hlog₂
  change Real.log (1 + P) ≤ A * E + B ∧ E ≤ A * Real.log (2 + P) + B
  constructor
  · have hzmin : a * (ℓ - Φ) ≤ z.im := by
      rw [hzim]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (abs_le.mp hφre).2 _) ha.le
    have hℓle : ℓ - Φ ≤ (H / a) * E := by
      have hdiv := (le_div_iff₀ ha).mpr (show (ℓ - Φ) * a ≤ H * E by
        rw [mul_comm (ℓ - Φ)]
        exact hzmin.trans hheight)
      simpa only [div_mul_eq_mul_div₀] using hdiv
    have hAexp : 2 * ((H / a) * E) ≤ A * E := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    dsimp only [B]
    linarith only [hlog₁, hℓle, hAexp, hC, hB₀, le_abs_self (Real.log 3)]
  · have hzmax : z.im ≤ a * (ℓ + Φ) := by
      rw [hzim]
      exact mul_le_mul_of_nonneg_left (by linarith only [(abs_le.mp hφre).1]) ha.le
    have hzdiv : z.im / z₀.im ≤ K * (ℓ + Φ) := by
      have h := div_le_div_of_nonneg_right hzmax z₀.im_pos.le
      dsimp only [K]
      simpa only [div_mul_eq_mul_div₀] using h
    have hlogP : 0 ≤ Real.log (2 + P) := Real.log_nonneg (by
      have hP : 0 ≤ P := norm_nonneg _
      linarith only [hP])
    have hKlog : K * (ℓ + Φ) ≤ K * Real.log (2 + P) + K * (Φ + Real.log 2) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith only [hlog₂, hlogP, hlog2]) hK
    have hAlog : K * Real.log (2 + P) ≤ A * Real.log (2 + P) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlogP
    dsimp only [B]
    linarith only [hE, hzdiv, hKlog, hAlog, abs_nonneg (Real.log 3), hΦ0]

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
