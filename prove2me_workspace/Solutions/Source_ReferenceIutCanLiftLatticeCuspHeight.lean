/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Depth.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeCuspNormalForm

set_option autoImplicit false

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))

/-- The data of the cusp normal form. -/
structure CuspData where
  M : SL(2, ℝ)
  κ : ℝ
  κ_pos : 0 < κ
  conj : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ
  r₁ : ℝ
  r₁_pos : 0 < r₁
  r₁_le : r₁ ≤ r₀ t
  φ : ℂ → ℂ
  Φ : ℝ
  φ_le : ∀ w ∈ ball (0 : ℂ) r₁, ‖φ w‖ ≤ Φ
  normal : ∀ s : ℂ, s.re < Real.log r₁ → τ' U M s = (κ / (2 * π * I)) * (s + φ (Complex.exp s))
  G : ℂ → ℂ
  G_diff : DifferentiableOn ℂ G (ball 0 r₁)
  G_zero : G 0 = 0
  G_deriv : deriv G 0 ≠ 0
  G_exp : ∀ s : ℂ, s.re < Real.log r₁ →
    Complex.exp (2 * π * I * τ' U M s / κ) = G (Complex.exp s)

/-- A choice of cusp data. -/
noncomputable def cuspData : CuspData U := by
  choose M κ hκ hM r₁ hr₁ hr₁₀ φ Φ hΦ hnf G hG using exists_cusp_normalForm U
  exact ⟨M, κ, hκ, hM, r₁, hr₁, hr₁₀, φ, Φ, hΦ, hnf, G, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2⟩

variable {U}

theorem log_mem_ball (c : CuspData U) {w : ℂ} (hw : w ∈ ball (0 : ℂ) c.r₁) (hw0 : w ≠ 0) :
    (Complex.log w).re < Real.log c.r₁ := by
  rw [Complex.log_re]
  exact Real.log_lt_log (norm_pos_iff.mpr hw0) (mem_ball_zero_iff.mp hw)

theorem mem_Dst_of_ball (c : CuspData U) {w : ℂ} (hw : w ∈ ball (0 : ℂ) c.r₁) (hw0 : w ≠ 0) :
    w ∈ Dst t := ⟨ball_subset_ball c.r₁_le hw, hw0⟩

/-- **The horoball lemma**: points high up in the cusp coordinate lie in the `Σ`-region. -/
theorem exists_height (c : CuspData U) : ∃ h : ℝ, ∀ ν : ℍ, h < (c.M⁻¹ • ν).im →
    ∃ w ∈ ball (0 : ℂ) c.r₁, w ≠ 0 ∧ ∃ k : ℤ, ν = (Cm U) ^ k • Sig U (Complex.log w) := by
  have hGs : HasStrictDerivAt c.G (deriv c.G 0) 0 :=
    (c.G_diff.analyticAt (ball_mem_nhds 0 c.r₁_pos)).hasStrictDerivAt
  have hmap := hGs.map_nhds_eq c.G_deriv
  rw [c.G_zero] at hmap
  have himg : c.G '' ball 0 c.r₁ ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]; exact image_mem_map (ball_mem_nhds 0 c.r₁_pos)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨(c.κ / (2 * π)) * Real.log (1 / ε), fun ν hν ↦ ?_⟩
  set ν' := c.M⁻¹ • ν
  set q := Complex.exp (2 * π * I * (ν' : ℂ) / c.κ)
  have hκ' : (c.κ : ℂ) ≠ 0 := by exact_mod_cast c.κ_pos.ne'
  have hq : q ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_exp]
    have hre : (2 * π * I * (ν' : ℂ) / c.κ).re = -(2 * π / c.κ) * ν'.im := by
      rw [show (2 * π * I * (ν' : ℂ) / c.κ) = (2 * π / c.κ : ℝ) * I * ν' by push_cast; ring]
      simp
    rw [hre]
    have h1 : Real.log (1 / ε) < (2 * π / c.κ) * ν'.im := by
      have hwidth : 0 < 2 * π / c.κ := by have := c.κ_pos; positivity
      apply (div_lt_iff₀' hwidth).mp
      rw [div_div_eq_mul_div, mul_comm (Real.log (1 / ε)) c.κ,
        ← div_mul_eq_mul_div₀ c.κ (Real.log (1 / ε)) (2 * π)]
      exact hν
    calc Real.exp (-(2 * π / c.κ) * ν'.im) < Real.exp (-Real.log (1 / ε)) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = ε := by rw [Real.exp_neg, Real.exp_log (by positivity)]; simp
  obtain ⟨w, hw, hGw⟩ := hεsub hq
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [c.G_zero] at hGw
    exact Complex.exp_ne_zero _ hGw.symm
  refine ⟨w, hw, hw0, ?_⟩
  set s := Complex.log w
  have hs := log_mem_ball c hw hw0
  have h1 := c.G_exp s hs
  rw [Complex.exp_log hw0, hGw] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hcancel (z : ℂ) : (c.κ / (2 * π * I)) * (2 * π * I * z / c.κ) = z := by
    field_simp [hκ', h2πI] <;> ring
  have hτ : τ' U c.M s = ν' + n * c.κ := by
    calc
      τ' U c.M s = (c.κ / (2 * π * I)) * (2 * π * I * τ' U c.M s / c.κ) :=
        (hcancel _).symm
      _ = (c.κ / (2 * π * I)) * (2 * π * I * (ν' : ℂ) / c.κ + n * (2 * π * I)) :=
        congrArg (fun z : ℂ ↦ (c.κ / (2 * π * I)) * z) hn
      _ = _ := by
        rw [mul_add, hcancel]
        congr 1
        field_simp [h2πI] <;> ring
  refine ⟨-n, ?_⟩
  have h2 : c.M⁻¹ • Sig U s = (c.M⁻¹ * Cm U * c.M) ^ n • ν' :=
    UpperHalfPlane.ext (by rw [translation_zpow U c.conj]; exact hτ)
  have h3 := congrArg (fun z ↦ c.M • z) h2
  simp only [smul_inv_smul] at h3
  rw [show ν' = c.M⁻¹ • ν from rfl, conj_zpow_smul] at h3
  rw [h3, ← mul_smul, zpow_neg, inv_mul_cancel, one_smul]

/-! ### The orbit of the base point stays below a fixed height -/

private theorem cx_c₀_add_lattice {l : ℂ} (hl : l ∈ (periodPair t).lattice) :
    ∃ n : ℤ, cx t (c₀ t + l) = 1 / 2 + n := by
  obtain ⟨m, n, -, hn⟩ := (mem_lattice_iff t l).mp hl
  exact ⟨n, by rw [cx_add, cx_c₀, hn]⟩

/-- The orbit of `e₀` stays below a fixed height in the cusp coordinate. -/
theorem exists_orbit_height (c : CuspData U) :
    ∃ h : ℝ, ∀ γ ∈ U.deckGroup, (c.M⁻¹ • (γ • e₀ U)).im ≤ h := by
  obtain ⟨h, hh⟩ := exists_height c
  refine ⟨h, fun γ hγ ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw, hw0, k, hk⟩ := hh _ hlt
  have hψ : U.ψ (γ • e₀ U) = w := by
    rw [hk, ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr (mem_Dst_of_ball c hw hw0)),
      Complex.exp_log hw0]
  obtain ⟨l, hl, hγψ⟩ := hγ
  rw [hγψ, ψ_e₀] at hψ
  obtain ⟨n, hn⟩ := cx_c₀_add_lattice hl
  have hw' : c₀ t + l ∈ ball (0 : ℂ) c.r₁ := by rwa [hψ]
  have hbox := (box (ball_subset_ball c.r₁_le hw')).1
  rw [hn, abs_lt] at hbox
  have h1 : (n : ℝ) < 0 := by linarith [hbox.2]
  have h2 : (-1 : ℝ) < n := by linarith [hbox.1]
  have : n < 0 := by exact_mod_cast h1
  have : -1 < n := by exact_mod_cast h2
  omega

private theorem τ'_mul (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    τ' U c.M s * (2 * π * I) = c.κ * (s + c.φ (Complex.exp s)) := by
  rw [c.normal s hs]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

theorem τ'_im (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    (τ' U c.M s).im = (c.κ / (2 * π)) * (-s.re - (c.φ (Complex.exp s)).re) := by
  have h := congrArg Complex.re (τ'_mul c hs)
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    re_ofNat, im_ofNat] at h
  field_simp [Real.pi_ne_zero]
  nlinarith only [h]

theorem τ'_re (c : CuspData U) {s : ℂ} (hs : s.re < Real.log c.r₁) :
    (τ' U c.M s).re = (c.κ / (2 * π)) * (s.im + (c.φ (Complex.exp s)).im) := by
  have h := congrArg Complex.im (τ'_mul c hs)
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    re_ofNat, im_ofNat] at h
  field_simp [Real.pi_ne_zero]
  nlinarith only [h]

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
