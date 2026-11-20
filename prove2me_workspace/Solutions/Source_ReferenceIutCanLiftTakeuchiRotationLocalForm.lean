/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/JOrb.lean, lines 31–194
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Complex Filter Metric Set
open scoped Topology

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- A nonconstant analytic function has a local normal form of positive order. -/
private theorem exists_localForm {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hnc : ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀) : ∃ n : ℕ, 0 < n ∧ HasLocalForm f z₀ n := by
  have han : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  have hnc' : ¬ ∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    simpa only [sub_eq_zero] using hnc
  obtain ⟨n, g, hg, hg0, hfg⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnc'
  simp only [smul_eq_mul] at hfg
  have hn : n ≠ 0 := by
    rintro rfl
    have hz := hfg.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at hz
    exact hg0 hz.symm
  have hP' : deriv (fun z : ℂ ↦ z - z₀) z₀ ≠ 0 := by
    simp
  refine ⟨n, Nat.pos_of_ne_zero hn,
    hasLocalForm_of_eq_pow_mul hn (analyticAt_id.sub analyticAt_const)
      (sub_self z₀) hP' hg hg0 ?_⟩
  filter_upwards [hfg] with z hz
  change f z = f z₀ + (z - z₀) ^ n * g z
  rw [← hz]
  ring

/-- The slope of a function with a derivative at `0` vanishing at `0`. -/
private theorem tendsto_div_of_hasDerivAt {h : ℂ → ℂ} {a : ℂ} (hd : HasDerivAt h a 0) (h0 : h 0 = 0) :
    Tendsto (fun t ↦ h t / t) (𝓝[≠] 0) (𝓝 a) := by
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  ring

/-- **Local normal form under a rotation symmetry.** Let `F` be analytic at `0`, invariant under
the rotation by `u₀` of order `e`, and suppose that near `0` equal values of `F` differ by an
`e`-th root of unity. Then `F = F 0 + g ^ e` for a local coordinate `g` at `0`. -/
theorem exists_localForm_of_rot {F : ℂ → ℂ} {e : ℕ} (hF : AnalyticAt ℂ F 0) {δ : ℝ}
    (hδ : 0 < δ)
    (hQ : ∀ s₁ ∈ ball (0 : ℂ) δ, ∀ s₂ ∈ ball (0 : ℂ) δ, F s₁ = F s₂ →
      ∃ u : ℂ, u ^ e = 1 ∧ s₂ = u * s₁)
    {u₀ : ℂ} (hu₀ : ∀ m : ℕ, u₀ ^ m = 1 → e ∣ m)
    (hR : ∀ s ∈ ball (0 : ℂ) δ, F (u₀ * s) = F s) :
    HasLocalForm F 0 e := by
  -- `F` is not locally constant
  have hnc : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), F s = F 0 := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
    set s : ℂ := ((min ε δ / 2 : ℝ) : ℂ)
    have hs : s ∈ ball (0 : ℂ) (min ε δ) := by
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [lt_min hε hδ]
    have hs0 : s ≠ 0 := by
      simp only [s, ne_eq, ofReal_eq_zero]; exact (by positivity : min ε δ / 2 ≠ 0)
    obtain ⟨u, -, hu⟩ := hQ 0 (mem_ball_self hδ) s (ball_subset_ball (min_le_right _ _) hs)
      (hball s (ball_subset_ball (min_le_left _ _) hs)).symm
    exact hs0 (by rw [hu, mul_zero])
  obtain ⟨n, hn, φ, hφ, hφ0, hφ', hFφ⟩ := exists_localForm hF hnc
  set a := deriv φ 0
  have hsφ : HasStrictDerivAt φ a 0 := hφ.hasStrictDerivAt
  set ψ := hsφ.localInverse φ a 0 hφ'
  have hψ : HasStrictDerivAt ψ a⁻¹ 0 := by
    have := hsφ.to_localInverse hφ'
    rwa [hφ0] at this
  have hleft : ∀ᶠ s in 𝓝 0, ψ (φ s) = s := hsφ.eventually_left_inverse hφ'
  have hright : ∀ᶠ t in 𝓝 0, φ (ψ t) = t := by
    have := hsφ.eventually_right_inverse hφ'
    rwa [hφ0] at this
  have hψ0 : ψ 0 = 0 := by
    have := hleft.self_of_nhds
    rwa [hφ0] at this
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have := hψ.hasDerivAt.continuousAt.tendsto
    rwa [hψ0] at this
  have hslope : Tendsto (fun t ↦ ψ t / t) (𝓝[≠] 0) (𝓝 a⁻¹) :=
    tendsto_div_of_hasDerivAt hψ.hasDerivAt hψ0
  have hball : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ ball (0 : ℂ) δ := ball_mem_nhds 0 hδ
  -- eventually along `t → 0`, `ψ t` is a good point
  have hgood : ∀ᶠ t in 𝓝 (0 : ℂ), ψ t ∈ ball (0 : ℂ) δ ∧ F (ψ t) = F 0 + t ^ n ∧
      (t ≠ 0 → ψ t ≠ 0) := by
    filter_upwards [hψt.eventually hball, hψt.eventually hFφ, hright] with t h1 h2 h3
    refine ⟨h1, by rw [h2, h3], fun ht h ↦ ht ?_⟩
    rw [← h3, h, hφ0]
  -- upper bound: `n ∣ e`
  have hne : n ∣ e := by
    set ζ := exp (2 * Real.pi * Complex.I / n)
    have hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_exp n hn.ne'
    have hζ0 : ζ ≠ 0 := exp_ne_zero _
    have hζt : Tendsto (fun t ↦ ζ * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun t ↦ ζ * t) (𝓝 0) (𝓝 (ζ * 0)) := (continuous_const_mul ζ).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_ne_zero hζ0 ht
    have hU : Tendsto (fun t ↦ ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) (𝓝[≠] 0)
        (𝓝 (ζ * (a⁻¹ / a⁻¹))) :=
      tendsto_const_nhds.mul ((hslope.comp hζt).div hslope (inv_ne_zero hφ'))
    rw [div_self (inv_ne_zero hφ'), mul_one] at hU
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) ^ e = 1 := by
      filter_upwards [hgood.filter_mono nhdsWithin_le_nhds,
        (hζt.eventually (hgood.filter_mono nhdsWithin_le_nhds)), self_mem_nhdsWithin]
        with t h1 h2 ht
      have ht : t ≠ 0 := ht
      have hψt0 := h1.2.2 ht
      have heq : F (ψ t) = F (ψ (ζ * t)) := by
        rw [h1.2.1, h2.2.1, mul_pow, hζ.pow_eq_one, one_mul]
      obtain ⟨u, hu, hu'⟩ := hQ _ h1.1 _ h2.1 heq
      have : ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t)) = u := by
        rw [hu']; field_simp
      rw [this, hu]
    have hlim : Tendsto (fun t ↦ (ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) ^ e) (𝓝[≠] 0)
        (𝓝 (ζ ^ e)) := hU.pow e
    have : ζ ^ e = 1 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono
      fun _ h ↦ h.symm))
    exact hζ.dvd_of_pow_eq_one e this
  -- lower bound: `e ∣ n`
  have hen : e ∣ n := by
    set h : ℂ → ℂ := fun t ↦ φ (u₀ * ψ t)
    have hd : HasDerivAt h (a * (u₀ * a⁻¹)) 0 := by
      have h1 : HasDerivAt (fun t ↦ u₀ * ψ t) (u₀ * a⁻¹) 0 := hψ.hasDerivAt.const_mul u₀
      have h2 : HasDerivAt φ a (u₀ * ψ 0) := by
        rw [hψ0, mul_zero]; exact hφ.differentiableAt.hasDerivAt
      exact h2.comp 0 h1
    have ha : a * (u₀ * a⁻¹) = u₀ := by field_simp
    rw [ha] at hd
    have h0 : h 0 = 0 := by simp only [h, hψ0, mul_zero, hφ0]
    have hsl := tendsto_div_of_hasDerivAt hd h0
    have hut : Tendsto (fun t ↦ u₀ * ψ t) (𝓝 0) (𝓝 0) := by
      have := hψt.const_mul u₀
      rwa [mul_zero] at this
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), h t ^ n = t ^ n := by
      filter_upwards [hgood, hut.eventually hFφ] with t h1 h2
      have := h2.symm.trans ((hR _ h1.1).trans h1.2.1)
      exact add_left_cancel this
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (h t / t) ^ n = 1 := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t h1 ht
      have ht : t ≠ 0 := ht
      rw [div_pow, h1, div_self (pow_ne_zero _ ht)]
    have : u₀ ^ n = 1 := tendsto_nhds_unique (hsl.pow n) (tendsto_const_nhds.congr' (hev'.mono
      fun _ h ↦ h.symm))
    exact hu₀ n this
  exact ⟨φ, hφ, hφ0, hφ', by rwa [Nat.dvd_antisymm hne hen] at hFφ⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
