/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

The finite-area strip computation is adapted from OrbicurveCores/Fuchsian/FordCover.lean
at 61616dcd77fbe45c083a8ebfa7cc80728f86e841 of https://github.com/lana-agents/orbicurve-cores.
The orbit representatives come from Oka/Uniformization/{Cusp,Depth}.lean at
75dcdc3faadd10b986afb9283e89902bcdddecd4 of https://github.com/lana-agents/oka.
-/
import Solutions.Source_ReferenceIutCanLiftLatticeCuspHeight
import Solutions.Source_ReferenceIutCanLiftLatticeDepthDomain
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false

open Complex MeasureTheory Metric Set UpperHalfPlane
open scoped MatrixGroups ENNReal NNReal Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- A finite-covolume subgroup has a measurable set of finite hyperbolic area meeting every orbit. -/
def HasFiniteCovolume (Γ : Subgroup SL(2, ℝ)) : Prop :=
  ∃ F : Set ℍ, MeasurableSet F ∧ volume F < ∞ ∧ ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F

theorem volume_smul_SL (g : SL(2, ℝ)) (s : Set ℍ) : volume (g • s) = volume s := by
  have h : g • s = (Matrix.SpecialLinearGroup.mapGL ℝ g) • s := by
    ext z
    simp [Set.mem_smul_set, MulAction.compHom_smul_def]
  rw [h, measure_smul]

/-- A vertical strip bounded away from the real axis has finite hyperbolic area. -/
private theorem volume_strip_lt_top (a b η : ℝ) (hη : 0 < η) :
    volume {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} < ∞ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  let T : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Ici η)
  have hsub : ((↑) '' {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} : Set ℂ) ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [T, Complex.measurableEquivRealProd] using hz
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' T = Icc a b ×ˢ Ici η := by
    ext p
    simp [T]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hg : Measurable fun y : ℝ ↦ (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    fun_prop
  have hfeq : ∀ p : ℝ × ℝ, (Complex.measurableEquivRealProd.symm p).im = p.2 := by
    intro p
    simp [Complex.measurableEquivRealProd]
  simp_rw [hfeq]
  rw [lintegral_prod (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
    (hg.comp measurable_snd).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  have hint := (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hη).2
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  refine lt_of_le_of_lt (le_of_eq ?_) hint
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := lt_trans hη hy
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _), ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.rpow_neg hy0.le, Real.rpow_two, Real.norm_of_nonneg hy0.le]
  ring

namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} {U : LatticeComplementCover (periodPair t)}

private theorem exists_cusp_strip (c : CuspData U) :
    ∃ ε > 0, ε ≤ c.r₁ ∧ ∃ a > 0, ∃ R : ℝ,
      ∀ w ∈ ball (0 : ℂ) ε, w ≠ 0 →
        |(c.M⁻¹ • Sig U (Complex.log w)).re| ≤ R ∧ a ≤ (c.M⁻¹ • Sig U (Complex.log w)).im := by
  let ε := min c.r₁ (Real.exp (-(c.Φ + 1)))
  have hε : 0 < ε := lt_min c.r₁_pos (Real.exp_pos _)
  have hεr : ε ≤ c.r₁ := min_le_left _ _
  let a := c.κ / (2 * Real.pi)
  have ha : 0 < a := div_pos c.κ_pos (by positivity)
  refine ⟨ε, hε, hεr, a, ha, a * (Real.pi + c.Φ), fun w hw hw0 ↦ ?_⟩
  have hw' : w ∈ ball (0 : ℂ) c.r₁ := ball_subset_ball hεr hw
  let s := Complex.log w
  have hs := log_mem_ball c hw' hw0
  have hs_exp : Complex.exp s = w := Complex.exp_log hw0
  have hs_re : s.re < -(c.Φ + 1) := by
    rw [show s.re = Real.log ‖w‖ from Complex.log_re w]
    calc
      Real.log ‖w‖ < Real.log ε := Real.log_lt_log (norm_pos_iff.mpr hw0) (mem_ball_zero_iff.mp hw)
      _ ≤ Real.log (Real.exp (-(c.Φ + 1))) := Real.log_le_log hε (min_le_right _ _)
      _ = -(c.Φ + 1) := Real.log_exp _
  have hs_im : |s.im| ≤ Real.pi := by
    change |(Complex.log w).im| ≤ Real.pi
    rw [Complex.log_im]
    exact abs_le.mpr ⟨(neg_pi_lt_arg w).le, arg_le_pi w⟩
  have hφre : |(c.φ w).re| ≤ c.Φ := (abs_re_le_norm _).trans (c.φ_le w hw')
  have hφim : |(c.φ w).im| ≤ c.Φ := (abs_im_le_norm _).trans (c.φ_le w hw')
  constructor
  · change |(τ' U c.M s).re| ≤ a * (Real.pi + c.Φ)
    rw [τ'_re c hs, hs_exp, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hs_im hφim)) ha.le
  · change a ≤ (τ' U c.M s).im
    rw [τ'_im c hs, hs_exp]
    have h : 1 ≤ -s.re - (c.φ w).re := by
      linarith only [hs_re, (abs_le.mp hφre).2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha.le

/-- The deck group of a lattice-complement covering has finite hyperbolic covolume. -/
theorem deckGroup_hasFiniteCovolume (U : LatticeComplementCover (periodPair t)) :
    HasFiniteCovolume U.deckGroup := by
  let c := cuspData U
  obtain ⟨ε, hε, hεr, a, ha, R, hcusp⟩ := exists_cusp_strip c
  let K₀ : Set ℍ := sK U '' Kε t ε
  let S : Set ℍ := {z | z.re ∈ Icc (-R) R ∧ a ≤ z.im}
  have hK₀ : IsCompact K₀ :=
    (isCompact_Kε ε).image_of_continuousOn ((continuousOn_sK U).mono (Kε_subset hε))
  have hS : MeasurableSet S :=
    (measurableSet_Icc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ici.preimage UpperHalfPlane.continuous_im.measurable)
  have hMS : MeasurableSet (c.M • S) := hS.const_smul c.M
  have hvol : volume (c.M • S) < ∞ := by
    rw [volume_smul_SL]
    exact volume_strip_lt_top (-R) R a ha
  refine ⟨K₀ ∪ c.M • S, hK₀.isClosed.measurableSet.union hMS,
    (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hK₀.measure_lt_top, hvol⟩), ?_⟩
  intro z
  rcases compact_or_cusp (U := U) (hεr.trans c.r₁_le) z with
    ⟨γ, hγ, w, hw, heq⟩ | ⟨γ, hγ, w, hw, hw0, heq⟩
  · exact ⟨γ, hγ, Or.inl ⟨w, hw, heq.symm⟩⟩
  · refine ⟨γ, hγ, Or.inr (Set.mem_smul_set_iff_inv_smul_mem.mpr ?_)⟩
    rw [heq]
    obtain ⟨hre, him⟩ := hcusp w hw hw0
    exact ⟨abs_le.mp hre, him⟩

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
