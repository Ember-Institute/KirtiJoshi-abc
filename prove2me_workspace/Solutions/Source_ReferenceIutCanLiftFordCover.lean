/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/FordCover.lean
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Topology Filter
open scoped BigOperators MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

private theorem im_smul_SL (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (g 1 0 * (z : ℂ) + g 1 1) := by
  change (mapGL ℝ g • z).im = _
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom]

/-- A finite open disc cover of a period has a uniform margin below height η. -/
private theorem exists_shrunken_disc_cover {a w : ℝ} (hw : 0 < w)
    {ι : Type*} [Finite ι] (g : ι → SL(2, ℝ))
    (hcov : ∀ t ∈ Icc a (a + w), ∃ i, |g i 1 0 * t + g i 1 1| < 1) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ z : ℍ,
      z.re ∈ Icc a (a + w) → z.im < η →
        ∃ i, Complex.normSq (g i 1 0 * (z : ℂ) + g i 1 1) < ρ ^ 2 := by
  classical
  obtain ⟨i₀, -⟩ := hcov a ⟨le_rfl, by linarith⟩
  haveI := Fintype.ofFinite ι
  haveI : Nonempty ι := ⟨i₀⟩
  set φ : ℝ → ℝ := fun t ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ |g i 1 0 * t + g i 1 1|
  have hφc : Continuous φ := by
    refine Continuous.finset_inf'_apply _ fun i _ ↦ ?_
    fun_prop
  have hφlt : ∀ t ∈ Icc a (a + w), φ t < 1 := by
    intro t ht
    obtain ⟨i, hi⟩ := hcov t ht
    exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ i)) hi
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := a) (b := a + w)).exists_isMaxOn
    (nonempty_Icc.mpr (by linarith))
    hφc.continuousOn
  set ρ₀ := φ t₀
  have hρ₀ : ρ₀ < 1 := hφlt t₀ ht₀
  have hρ₀0 : 0 ≤ ρ₀ := Finset.le_inf' Finset.univ_nonempty _ fun i _ ↦ abs_nonneg _
  set ρ := (1 + ρ₀) / 2
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hρ0 : 0 < ρ := by simp only [ρ]; linarith
  set C := 1 + ∑ i, |g i 1 0|
  have hC : 0 < C := by positivity
  have hCi : ∀ i, |g i 1 0| ≤ C := fun i ↦ by
    have := Finset.single_le_sum (f := fun i ↦ |g i 1 0|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    simp only [C]
    linarith
  set η := (ρ - ρ₀) / C with hη_def
  have hη : 0 < η := div_pos (by simp only [ρ]; linarith) hC
  refine ⟨η, ρ, hη, hρ0, hρ1, ?_⟩
  intro z hz hzi
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    fun i ↦ |g i 1 0 * z.re + g i 1 1|
  refine ⟨i, ?_⟩
  have hle : |g i 1 0 * z.re + g i 1 1| ≤ ρ₀ := by
    have := hmax hz
    simp only [Set.mem_setOf_eq] at this
    rw [← hi]
    exact this
  have habs : ‖(g i 1 0 * (z : ℂ) + g i 1 1)‖ ≤ |g i 1 0 * z.re + g i 1 1| +
      |g i 1 0| * z.im := by
    have e : (g i 1 0 * (z : ℂ) + g i 1 1) = ((g i 1 0 * z.re + g i 1 1 : ℝ) : ℂ) +
        ((g i 1 0 * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos z.im_pos]
  have hlt : ‖(g i 1 0 * (z : ℂ) + g i 1 1)‖ < ρ := by
    have h1 : |g i 1 0| * z.im ≤ C * z.im := mul_le_mul_of_nonneg_right (hCi i) z.im_pos.le
    have h2 : C * z.im < C * η := mul_lt_mul_of_pos_left hzi hC
    have h3 : C * η = ρ - ρ₀ := by
      rw [hη_def, mul_comm, div_mul_cancel₀ _ hC.ne']
    linarith only [hle, habs, h1, h2, h3]
  rw [Complex.normSq_eq_norm_sq]
  exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)

/-- A positive translation moves every point into the period and preserves its height. -/
private theorem exists_zpow_translate {a w : ℝ} (hw : 0 < w) {τ : SL(2, ℝ)}
    (hτz : ∀ z : ℍ, ((τ • z : ℍ) : ℂ) = z + w) (z : ℍ) :
    ∃ k : ℤ, ((τ ^ k) • z).re ∈ Icc a (a + w) ∧ ((τ ^ k) • z).im = z.im := by
  have hτk : ∀ (k : ℤ) (u : ℍ), (((τ ^ k) • u : ℍ) : ℂ) = u + k * w := by
    intro k
    induction k using Int.induction_on with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [_root_.zpow_add_one, mul_smul, ih, hτz]
      push_cast
      ring
    | pred n ih =>
      intro u
      have h := hτz ((τ ^ (-(n : ℤ) - 1)) • u)
      rw [← mul_smul, ← _root_.zpow_one_add,
        show (1 : ℤ) + (-(n : ℤ) - 1) = -(n : ℤ) by ring, ih] at h
      push_cast at h ⊢
      linear_combination -h
  refine ⟨⌈(a - z.re) / w⌉, ?_, ?_⟩
  · have hre : ((τ ^ ⌈(a - z.re) / w⌉) • z).re = z.re + ⌈(a - z.re) / w⌉ * w := by
      have := congrArg Complex.re (hτk ⌈(a - z.re) / w⌉ z)
      simpa using this
    rw [hre]
    have h1 := Int.le_ceil ((a - z.re) / w)
    have h2 := Int.ceil_lt_add_one ((a - z.re) / w)
    rw [div_le_iff₀ hw] at h1
    have h2' : (⌈(a - z.re) / w⌉ : ℝ) * w < ((a - z.re) / w + 1) * w :=
      mul_lt_mul_of_pos_right h2 hw
    rw [add_mul, div_mul_cancel₀ _ hw.ne'] at h2'
    constructor <;> linarith
  · have := congrArg Complex.im (hτk ⌈(a - z.re) / w⌉ z)
    simpa using this

/-- If the open isometric discs cover a period, every orbit meets a strip above positive height. -/
theorem exists_strip_cover_of_cover {Γ : Subgroup SL(2, ℝ)} {w a : ℝ} (hw : 0 < w)
    {τ : SL(2, ℝ)} (hτ : τ ∈ Γ) (hτz : ∀ z : ℍ, ((τ • z : ℍ) : ℂ) = z + w)
    {ι : Type*} [Finite ι] (g : ι → SL(2, ℝ)) (hg : ∀ i, g i ∈ Γ)
    (hcov : ∀ t ∈ Icc a (a + w), ∃ i, |g i 1 0 * t + g i 1 1| < 1) :
    ∃ η > 0, ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ {z : ℍ | z.re ∈ Icc a (a + w) ∧ η ≤ z.im} := by
  obtain ⟨η, ρ, hη, hρ0, hρ1, hlow⟩ := exists_shrunken_disc_cover hw g hcov
  refine ⟨η, hη, ?_⟩
  have hP : ∀ n : ℕ, ∀ z : ℍ, η * ρ ^ (2 * n) ≤ z.im →
      ∃ γ ∈ Γ, γ • z ∈ {z : ℍ | z.re ∈ Icc a (a + w) ∧ η ≤ z.im} := by
    intro n
    induction n with
    | zero =>
      intro z hz
      obtain ⟨k, hk1, hk2⟩ := exists_zpow_translate (a := a) hw hτz z
      exact ⟨τ ^ k, zpow_mem hτ k, hk1, by rw [hk2]; simpa using hz⟩
    | succ n ih =>
      intro z hz
      obtain ⟨k, hk1, hk2⟩ := exists_zpow_translate (a := a) hw hτz z
      set z' := (τ ^ k) • z
      by_cases hhigh : η ≤ z'.im
      · exact ⟨τ ^ k, zpow_mem hτ k, hk1, hhigh⟩
      obtain ⟨i, hi⟩ := hlow z' hk1 (lt_of_not_ge hhigh)
      have hpos : 0 < Complex.normSq (g i 1 0 * (z' : ℂ) + g i 1 1) := by
        simpa [UpperHalfPlane.denom] using UpperHalfPlane.normSq_denom_pos (mapGL ℝ (g i))
          z'.im_ne_zero
      have him : η * ρ ^ (2 * n) ≤ (g i • z').im := by
        rw [im_smul_SL, le_div_iff₀ hpos]
        have h1 : η * ρ ^ (2 * (n + 1)) ≤ z'.im := by
          simpa only [z', hk2] using hz
        have h2 : η * ρ ^ (2 * n) * Complex.normSq (g i 1 0 * (z' : ℂ) + g i 1 1) ≤
            η * ρ ^ (2 * n) * ρ ^ 2 :=
          mul_le_mul_of_nonneg_left hi.le (by positivity)
        calc
          _ ≤ η * ρ ^ (2 * n) * ρ ^ 2 := h2
          _ = η * ρ ^ (2 * (n + 1)) := by ring
          _ ≤ z'.im := h1
      obtain ⟨γ, hγ, hγz⟩ := ih _ him
      refine ⟨γ * g i * τ ^ k, mul_mem (mul_mem hγ (hg i)) (zpow_mem hτ k), ?_⟩
      rw [mul_smul, mul_smul]
      exact hγz
  intro z
  have hlim : Tendsto (fun n : ℕ ↦ η * ρ ^ (2 * n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ (ρ ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (by nlinarith only [hρ0, hρ1, mul_pos hρ0 (sub_pos.mpr hρ1)])
    simpa [pow_mul] using this.const_mul η
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds z.im_pos)).exists
  exact hP n z hn.le

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
