/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Cusp.lean
-/
import Solutions.Source_ReferenceIutCanLiftHolomorphicFunctions
import Solutions.Source_ReferenceIutCanLiftLatticeCuspCoordinates
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))

/-- The exponential of the normalized cusp coordinate descends to the punctured disk
and extends across the origin with a simple zero. -/
theorem exists_cusp_exponential {M : SL(2, ℝ)} {κ : ℝ} (hκ : κ ≠ 0)
    (hM : ∀ z : ℍ, (((M⁻¹ * Cm U * M) • z : ℍ) : ℂ) = z + κ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (0 : ℂ) (r₀ t)) ∧ G 0 = 0 ∧
      deriv G 0 ≠ 0 ∧ ∀ s ∈ Hr t,
        Complex.exp (2 * π * I * τ' U M s / (|κ| : ℝ)) = G (Complex.exp s) := by
  set a : ℝ := |κ|
  have ha : 0 < a := abs_pos.mpr hκ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hcancel (z : ℂ) : (a / (2 * π * I)) * (2 * π * I * z / a) = z := by
    field_simp [ha', h2πI] <;> ring
  have hscale (z q : ℂ) (hq : Complex.exp (2 * π * I * z / a) = Complex.exp q) :
      ∃ n : ℤ, z = (a / (2 * π * I)) * q + n * a := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hq
    refine ⟨n, ?_⟩
    calc
      z = (a / (2 * π * I)) * (2 * π * I * z / a) := (hcancel _).symm
      _ = (a / (2 * π * I)) * (q + n * (2 * π * I)) :=
        congrArg (fun u : ℂ ↦ (a / (2 * π * I)) * u) hn
      _ = _ := by
        rw [mul_add]
        congr 1
        field_simp [h2πI] <;> ring
  set E : ℂ → ℂ := fun s ↦ Complex.exp (2 * π * I * τ' U M s / a)
  have hEd : DifferentiableOn ℂ E (Hr t) :=
    (((differentiableOn_const _).mul (differentiableOn_τ' U M)).div_const _).cexp
  have hκa : Complex.exp (2 * π * I * κ / a) = 1 := by
    rcases abs_choice κ with h | h
    · rw [show (a : ℂ) = κ by simp [a, h], mul_div_assoc, div_self (by exact_mod_cast hκ),
        mul_one, Complex.exp_two_pi_mul_I]
    · rw [show (a : ℂ) = -κ by simp [a, h], show (2 * π * I * κ / -κ : ℂ) = -(2 * π * I) by
        field_simp [show (κ : ℂ) ≠ 0 by exact_mod_cast hκ]]
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hEper : ∀ s ∈ Hr t, E (s + 2 * π * I) = E s := by
    intro s hs
    simp only [E]
    rw [τ'_add_two_pi U hM hs, show 2 * π * I * (τ' U M s + κ) / a =
      2 * π * I * τ' U M s / a + 2 * π * I * κ / a by ring, Complex.exp_add, hκa, mul_one]
  have hEnorm : ∀ s, ‖E s‖ < 1 := by
    intro s
    simp only [E, Complex.norm_exp]
    rw [Real.exp_lt_one_iff]
    have him := τ'_im_pos U M s
    have : (2 * π * I * τ' U M s / a).re = -(2 * π * (τ' U M s).im) / a := by
      simp [div_ofReal_re]
    rw [this]
    exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) ha
  obtain ⟨hgd, hgexp⟩ := differentiableOn_comp_log hEd hEper
  set g : ℂ → ℂ := fun w ↦ E (Complex.log w)
  -- the removable singularity
  set G := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g)
  have hball : ball (0 : ℂ) (r₀ t) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 r₀_pos
  have hGd : DifferentiableOn ℂ G (ball 0 (r₀ t)) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hgd
      ⟨1, by rintro _ ⟨p, -, rfl⟩; exact (hEnorm _).le⟩
  have hGg : ∀ p ∈ Dst t, G p = g p := fun p hp ↦ Function.update_of_ne hp.2 _ _
  have hGc : ContinuousAt G 0 := (hGd.differentiableAt hball).continuousAt
  -- values in the normalised coordinate
  have hτ'log : ∀ p ∈ Dst t, ∀ q ∈ Dst t, g p = g q →
      ∃ m : ℤ, τ' U M (Complex.log p) = τ' U M (Complex.log q) + m * κ := by
    intro p hp q hq hpq
    simp only [g, E] at hpq
    obtain ⟨n, hn⟩ := hscale _ _ hpq
    rw [hcancel] at hn
    rcases abs_choice κ with h | h
    · exact ⟨n, by rw [hn]; simp [a, h]⟩
    · exact ⟨-n, by rw [hn]; simp [a, h]⟩
  -- injectivity on the punctured disc
  have hinj : ∀ p ∈ Dst t, ∀ q ∈ Dst t, g p = g q → p = q := by
    intro p hp q hq hpq
    obtain ⟨m, hm⟩ := hτ'log p hp q hq hpq
    have h1 : M⁻¹ • Sig U (Complex.log p) = (M⁻¹ * Cm U * M) ^ m • (M⁻¹ • Sig U (Complex.log q)) :=
      UpperHalfPlane.ext (by rw [translation_zpow U hM]; exact hm)
    have h2 := congrArg (fun z : ℍ ↦ M • z) h1
    rw [smul_inv_smul, conj_zpow_smul] at h2
    have h3 := congrArg U.ψ h2
    rw [ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr hp), ψ_Sig U (log_mem_Hr hq), Complex.exp_log hp.2,
      Complex.exp_log hq.2] at h3
    exact h3
  have hgne : ∀ p, g p ≠ 0 := fun p ↦ Complex.exp_ne_zero _
  have hGle : ∀ z ∈ ball (0 : ℂ) (r₀ t), ‖G z‖ ≤ 1 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have hlim : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) := hGc.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim.norm ?_
      filter_upwards [inter_mem_nhdsWithin _ hball] with p hp
      rw [hGg p ⟨hp.2, hp.1⟩]; exact (hEnorm _).le
    · rw [hGg z ⟨hz, hz0⟩]; exact (hEnorm _).le
  have hp₁ : ((r₀ t / 2 : ℝ) : ℂ) ∈ Dst t := ⟨by
    rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
    by simp [r₀_pos.ne']⟩
  have hp₂ : ((r₀ t / 3 : ℝ) : ℂ) ∈ Dst t := ⟨by
    rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
    by simp [r₀_pos.ne']⟩
  have hp₁₂ : ((r₀ t / 2 : ℝ) : ℂ) ≠ ((r₀ t / 3 : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith [r₀_pos (t := t)]
  -- `G 0 = 0`
  have hG0 : G 0 = 0 := by
    by_contra hL
    set L := G 0
    have hLlt : ‖L‖ < 1 := by
      refine lt_of_le_of_ne (hGle 0 (mem_ball_self r₀_pos)) fun h1 ↦ ?_
      have hmax : IsMaxOn (norm ∘ G) (ball 0 (r₀ t)) 0 := fun z hz ↦ by
        simp only [mem_setOf_eq, Function.comp_apply]; rw [h1]; exact hGle z hz
      have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball (0 : ℂ) (r₀ t)).isPreconnected isOpen_ball hGd (mem_ball_self r₀_pos) hmax
      apply hp₁₂
      apply hinj _ hp₁ _ hp₂
      rw [← hGg _ hp₁, ← hGg _ hp₂, hc hp₁.1, hc hp₂.1] <;> rfl
    set ℓ₀ := Complex.log L
    have hℓ₀ : Complex.exp ℓ₀ = L := Complex.exp_log hL
    set τL : ℂ := (a / (2 * π * I)) * ℓ₀
    have hτL : 0 < τL.im := by
      have hre : ℓ₀.re = Real.log ‖L‖ := Complex.log_re L
      have hlog : Real.log ‖L‖ < 0 := Real.log_neg (norm_pos_iff.mpr hL) hLlt
      have : τL.im = -(a / (2 * π)) * ℓ₀.re := by
        simp only [τL]
        rw [show (a : ℂ) / (2 * π * I) = ((-(a / (2 * π)) : ℝ) : ℂ) * I by
          rw [div_eq_iff h2πI]; push_cast; field_simp; rw [show I ^ 2 = -1 from I_sq]; ring]
        simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
          mul_one, zero_add, add_zero, re_ofReal_mul]
      rw [this, hre]
      have : 0 < a / (2 * π) := by positivity
      nlinarith
    -- the approximating points
    have hGL : Tendsto (fun w ↦ G w / L) (𝓝[≠] 0) (𝓝 1) := by
      have := (hGc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).div_const L
      rwa [show G 0 / L = 1 from div_self hL] at this
    have hΛ : Tendsto (fun w ↦ Complex.log (G w / L)) (𝓝[≠] 0) (𝓝 0) := by
      have := (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp hGL
      rw [Complex.log_one] at this
      exact this
    have hrel : ∀ p ∈ Dst t, ∃ m : ℤ, τ' U M (Complex.log p) - m * κ =
        (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
      intro p hp
      have hGp : G p / L ≠ 0 := div_ne_zero (by rw [hGg p hp]; exact hgne p) hL
      have h1 : Complex.exp (2 * π * I * τ' U M (Complex.log p) / a) =
          Complex.exp (ℓ₀ + Complex.log (G p / L)) := by
        rw [Complex.exp_add, hℓ₀, Complex.exp_log hGp, mul_div_cancel₀ _ hL, hGg p hp]
      obtain ⟨n, hn⟩ := hscale _ _ h1
      have hτ : τ' U M (Complex.log p) - n * a =
          (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
        rw [hn, add_sub_cancel_right]
      rcases abs_choice κ with h | h
      · exact ⟨n, by rw [← hτ]; simp [a, h]⟩
      · exact ⟨-n, by rw [← hτ]; simp [a, h]⟩
    choose! mp hmp using hrel
    set ν : ℂ → ℍ := fun p ↦ (M⁻¹ * Cm U * M) ^ (-mp p) • (M⁻¹ • Sig U (Complex.log p))
    have hν : ∀ p ∈ Dst t, (ν p : ℂ) = (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L)) := by
      intro p hp
      simp only [ν]
      rw [translation_zpow U hM, ← hmp p hp]
      change τ' U M (Complex.log p) + _ = _
      push_cast; ring
    have hev : ∀ᶠ p in 𝓝[≠] (0 : ℂ), p ∈ Dst t := by
      filter_upwards [inter_mem_nhdsWithin _ hball] with p hp using ⟨hp.2, hp.1⟩
    have hlimν : Tendsto (fun p ↦ (ν p : ℂ)) (𝓝[≠] 0) (𝓝 τL) := by
      have : Tendsto (fun p ↦ (a / (2 * π * I)) * (ℓ₀ + Complex.log (G p / L))) (𝓝[≠] 0)
          (𝓝 ((a / (2 * π * I)) * (ℓ₀ + 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.add hΛ)
      rw [add_zero] at this
      exact this.congr' (hev.mono fun p hp ↦ (hν p hp).symm)
    set νL : ℍ := ⟨τL, hτL⟩
    have hlimν' : Tendsto ν (𝓝[≠] 0) (𝓝 νL) :=
      UpperHalfPlane.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.mpr hlimν
    have hψν : ∀ p ∈ Dst t, U.ψ (M • ν p) = p := by
      intro p hp
      simp only [ν]
      rw [conj_zpow_smul, ψ_Cm_zpow_smul, ψ_Sig U (log_mem_Hr hp), Complex.exp_log hp.2]
    have h1 : Tendsto (fun p ↦ U.ψ (M • ν p)) (𝓝[≠] 0) (𝓝 (U.ψ (M • νL))) :=
      ((U.continuous_ψ.comp (continuous_const_smul M)).tendsto νL).comp hlimν'
    have h2 : Tendsto (fun p ↦ U.ψ (M • ν p)) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun p hp ↦ (hψν p hp).symm)
    exact U.ψ_notMem (M • νL) (by rw [tendsto_nhds_unique h1 h2]; exact zero_mem _)
  -- `G` is injective on the disc, so `G′(0) ≠ 0`
  have hGinj : InjOn G (ball 0 (r₀ t)) := by
    intro p hp q hq hpq
    by_cases hp0 : p = 0
    · by_cases hq0 : q = 0
      · rw [hp0, hq0]
      · rw [hp0, hG0, hGg q ⟨hq, hq0⟩] at hpq; exact absurd hpq.symm (hgne q)
    · by_cases hq0 : q = 0
      · rw [hq0, hG0, hGg p ⟨hp, hp0⟩] at hpq; exact absurd hpq (hgne p)
      · rw [hGg p ⟨hp, hp0⟩, hGg q ⟨hq, hq0⟩] at hpq
        exact hinj p ⟨hp, hp0⟩ q ⟨hq, hq0⟩ hpq
  have hG'0 : deriv G 0 ≠ 0 := HolomorphicFunctions.deriv_ne_zero_of_injOn hGd hball hGinj
  refine ⟨G, hGd, hG0, hG'0, fun s hs ↦ ?_⟩
  change E s = G (Complex.exp s)
  rw [hGg _ (exp_mem_Dst hs)]
  exact (hgexp s hs).symm

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
