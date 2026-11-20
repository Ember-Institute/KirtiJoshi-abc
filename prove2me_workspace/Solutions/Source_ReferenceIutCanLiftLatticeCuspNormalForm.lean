/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Cusp.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeCuspExponential
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))

/-- **The cusp normal form.** -/
theorem exists_cusp_normalForm :
    ∃ M : SL(2, ℝ), ∃ κ : ℝ, 0 < κ ∧ (∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) ∧
      ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r₀ t ∧ ∃ φ : ℂ → ℂ, ∃ Φ : ℝ,
        (∀ w ∈ ball (0 : ℂ) r₁, ‖φ w‖ ≤ Φ) ∧
        (∀ s : ℂ, s.re < Real.log r₁ →
          τ' U M s = (κ / (2 * π * I)) * (s + φ (Complex.exp s))) ∧
        ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 r₁) ∧ G 0 = 0 ∧ deriv G 0 ≠ 0 ∧
          ∀ s : ℂ, s.re < Real.log r₁ →
            Complex.exp (2 * π * I * τ' U M s / κ) = G (Complex.exp s) := by
  obtain ⟨M, κ, hκ, hM⟩ := exists_conj_translation U
  obtain ⟨G, hGd, hG0, hG'0, hGexp⟩ := exists_cusp_exponential U hκ hM
  set a : ℝ := |κ|
  have ha : 0 < a := abs_pos.mpr hκ
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hball : ball (0 : ℂ) (r₀ t) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 r₀_pos
  -- `G w = w F(w)` with `F(0) ≠ 0`
  set F := dslope G 0
  have hFd : DifferentiableOn ℂ F (ball 0 (r₀ t)) := (differentiableOn_dslope hball).mpr hGd
  have hF0 : F 0 = deriv G 0 := dslope_same G 0
  have hF0ne : F 0 ≠ 0 := fun h ↦ hG'0 (hF0.symm.trans h)
  have hGF : ∀ w, G w = w * F w := fun w ↦ by
    have := sub_smul_dslope G 0 w
    simp only [sub_zero, smul_eq_mul, hG0] at this
    exact this.symm
  have hFc : ContinuousAt F 0 := (hFd.differentiableAt hball).continuousAt
  have hFF : Tendsto (fun w ↦ F w / F 0) (𝓝 0) (𝓝 1) := by
    have := hFc.tendsto.div_const (F 0)
    rwa [div_self hF0ne] at this
  obtain ⟨r₂', hr₂', hr₂'s⟩ := Metric.eventually_nhds_iff_ball.mp
    (hFF.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)))
  set r₂ := min r₂' (r₀ t)
  have hr₂ : 0 < r₂ := lt_min hr₂' r₀_pos
  have hslit : ∀ w ∈ ball (0 : ℂ) r₂, F w / F 0 ∈ Complex.slitPlane := by
    intro w hw
    have h1 := hr₂'s w (ball_subset_ball (min_le_left _ _) hw)
    rw [dist_eq_norm] at h1
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (abs_re_le_norm (F w / F 0 - 1)).trans_lt h1
    rw [sub_re, one_re, abs_lt] at this
    linarith [this.1]
  set φ₀ : ℂ → ℂ := fun w ↦ Complex.log (F w / F 0) + Complex.log (F 0)
  have hφ₀ : ∀ w ∈ ball (0 : ℂ) r₂, Complex.exp (φ₀ w) = F w := by
    intro w hw
    simp only [φ₀]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit w hw)),
      Complex.exp_log hF0ne, div_mul_cancel₀ _ hF0ne]
  have hφ₀c : ContinuousOn φ₀ (ball 0 r₂) := by
    refine ContinuousOn.add ?_ continuousOn_const
    refine ContinuousOn.clog ?_ hslit
    exact (hFd.continuousOn.mono (ball_subset_ball (min_le_right _ _))).div_const _
  -- the half-plane `{Re s < log r₂}`
  set S : Set ℂ := {s | s.re < Real.log r₂}
  have hSHr : S ⊆ Hr t := fun s hs ↦ by
    simp only [Hr, mem_setOf_eq]
    exact hs.trans_le (Real.log_le_log hr₂ (min_le_right _ _))
  have hexpS : ∀ s ∈ S, Complex.exp s ∈ ball (0 : ℂ) r₂ := fun s hs ↦ by
    rw [mem_ball_zero_iff, Complex.norm_exp]
    calc Real.exp s.re < Real.exp (Real.log r₂) := Real.exp_lt_exp.mpr hs
      _ = r₂ := Real.exp_log hr₂
  have hk1 : ∀ s ∈ S, Complex.exp (2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s)) = 1 := by
    intro s hs
    have hGne : G (Complex.exp s) ≠ 0 := by
      rw [← hGexp s (hSHr hs)]
      exact Complex.exp_ne_zero _
    have hFne : F (Complex.exp s) ≠ 0 := by
      intro hzero
      exact hGne (by rw [hGF, hzero, mul_zero])
    rw [Complex.exp_sub, Complex.exp_sub, hφ₀ _ (hexpS s hs), hGexp s (hSHr hs),
      hGF, mul_div_cancel_left₀ _ (Complex.exp_ne_zero s), div_self hFne]
  have hkc : ContinuousOn (fun s ↦ 2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s)) S := by
    refine ((((continuousOn_const.mul ((differentiableOn_τ' U M).continuousOn.mono hSHr)).div_const
      _).sub continuousOn_id).sub (hφ₀c.comp Complex.continuous_exp.continuousOn hexpS))
  have hSc : IsPreconnected S := (convex_halfSpace_re_lt _).isPreconnected
  set s₀ : ℂ := ((Real.log r₂ - 1 : ℝ) : ℂ)
  have hs₀ : s₀ ∈ S := by simp [S, s₀]
  set k₀ := 2 * π * I * τ' U M s₀ / a - s₀ - φ₀ (Complex.exp s₀)
  have hk : ∀ s ∈ S, 2 * π * I * τ' U M s / a - s - φ₀ (Complex.exp s) = k₀ := fun s hs ↦
    const_of_exp_eq_one hSc hkc hk1 hs hs₀
  have hform : ∀ s ∈ S, τ' U M s = (a / (2 * π * I)) * (s + (φ₀ (Complex.exp s) + k₀)) := by
    intro s hs
    rw [← hk s hs]
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp [h2πI, haC] <;> ring
  -- `κ = a`
  have hκpos : κ = a := by
    have hs₂ : s₀ + 2 * π * I ∈ S := by simp [S, s₀]
    have h1 := τ'_add_two_pi U hM (hSHr hs₀)
    rw [hform _ hs₂, hform _ hs₀, show Complex.exp (s₀ + 2 * π * I) = Complex.exp s₀ by
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]] at h1
    have h1' : (κ : ℂ) = a := by
      rw [mul_add, mul_add, mul_add] at h1
      have e : (a : ℂ) / (2 * π * I) * (2 * π * I) = a := div_mul_cancel₀ _ h2πI
      linear_combination -h1 + e
    exact_mod_cast h1'
  -- the bound on `φ`
  set r₁ := r₂ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by positivity
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def]; linarith
  obtain ⟨Φ, hΦ⟩ := (isCompact_closedBall (0 : ℂ) r₁).exists_bound_of_continuousOn
    ((hφ₀c.mono (closedBall_subset_ball hr₁₂)).add continuousOn_const
      (g := fun _ ↦ k₀))
  have hr₁₀ : r₁ ≤ r₀ t := hr₁₂.le.trans (min_le_right _ _)
  have hsS : ∀ s : ℂ, s.re < Real.log r₁ → s ∈ S := fun s hs ↦ by
    simp only [S, mem_setOf_eq]
    exact hs.trans (Real.log_lt_log hr₁ hr₁₂)
  refine ⟨M, κ, by simpa only [hκpos] using ha, hM, r₁, hr₁, hr₁₀, fun w ↦ φ₀ w + k₀, Φ,
    fun w hw ↦ hΦ w (ball_subset_closedBall hw), fun s hs ↦ ?_, G,
    hGd.mono (ball_subset_ball hr₁₀), hG0, hG'0, fun s hs ↦ ?_⟩
  · rw [hform s (hsS s hs), hκpos]
  · rw [hκpos]
    exact hGexp s (hSHr (hsS s hs))

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
