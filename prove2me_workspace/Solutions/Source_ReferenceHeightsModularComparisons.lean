import Solutions.Source_ReferenceHeightsModularCusp
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Logarithmic comparisons on the modular fundamental domain

Source `Heights/ModularJ.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open Asymptotics Filter Topology UpperHalfPlane
open scoped UpperHalfPlane Manifold

private theorem abs_bound_on_fd_of_tendsto {f : ℍ → ℝ} {a : ℝ}
    (hcont : Continuous f) (hlim : Tendsto f atImInfty (𝓝 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ ModularGroup.fd, |f τ| ≤ C := by
  have hO : f =O[atImInfty] (fun τ : ℍ => τ.im ^ (0 : ℝ)) := by
    simpa using hlim.isBigO_one ℝ
  obtain ⟨B, hB⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont hO
  refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
  have hbound : |f τ| ≤ B := by
    simpa only [Real.norm_eq_abs, Real.rpow_zero, mul_one] using hB τ hτ
  exact hbound.trans (le_max_left _ _)

private lemma norm_discriminant_pos (τ : ℍ) : 0 < ‖ModularForm.discriminant τ‖ :=
  norm_pos_iff.mpr (ModularForm.discriminant_ne_zero τ)

theorem modularDeltaJ_fd_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ ModularGroup.fd,
      |-Real.log ‖silvermanDiscriminant τ‖ - Real.log (max ‖modularJ τ‖ 1)| ≤ C := by
  let K := ‖(2 * (Real.pi : ℂ)) ^ 12‖
  let M (τ : ℍ) := max ‖ModularForm.E₄ τ ^ 3‖ ‖ModularForm.discriminant τ‖
  have hK : K ≠ 0 :=
    norm_ne_zero_iff.mpr (pow_ne_zero _ (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hM (τ : ℍ) : M τ ≠ 0 := ((norm_discriminant_pos τ).trans_le (le_max_right _ _)).ne'
  have hDcont : Continuous fun τ : ℍ => ‖ModularForm.discriminant τ‖ := by
    simpa only [CuspForm.coe_discriminant] using (ModularFormClass.continuous CuspForm.discriminant).norm
  have hMcont : Continuous M :=
    ((ModularFormClass.continuous ModularForm.E₄).pow 3).norm.max hDcont
  have hMlim : Tendsto M atImInfty (𝓝 1) := by
    simpa [M] using
      (E₄_tendsto_atImInfty.pow 3).norm.max ModularForm.discriminant_isZeroAtImInfty.norm
  have hlim : Tendsto (fun τ => -Real.log K - Real.log (M τ)) atImInfty (𝓝 (-Real.log K)) := by
    simpa using tendsto_const_nhds.sub (hMlim.log one_ne_zero)
  obtain ⟨C, hC, hbound⟩ := abs_bound_on_fd_of_tendsto
    (f := fun τ => -Real.log K - Real.log (M τ))
    (continuous_const.sub (hMcont.log hM)) hlim
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hden := (norm_discriminant_pos τ).ne'
  have hmax : max ‖modularJ τ‖ 1 = M τ / ‖ModularForm.discriminant τ‖ := by
    rw [modularJ, norm_div, ← max_div_div_right (norm_nonneg (ModularForm.discriminant τ)),
      div_self hden]
  rw [hmax, silvermanDiscriminant, norm_mul, Real.log_mul hK hden, Real.log_div (hM τ) hden]
  have hcancel : -(Real.log K + Real.log ‖ModularForm.discriminant τ‖) -
      (Real.log (M τ) - Real.log ‖ModularForm.discriminant τ‖) =
      -Real.log K - Real.log (M τ) := by ring
  rw [hcancel]
  exact hbound τ hτ

private theorem log_max_modularJ_div_im_tendsto :
    Tendsto (fun τ : ℍ => Real.log (max ‖modularJ τ‖ (Real.exp 1)) / τ.im) atImInfty
      (𝓝 (2 * Real.pi)) := by
  have hlog : Tendsto (fun τ : ℍ => Real.log (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)))
      atImInfty (𝓝 0) := by
    simpa using scaled_modularJ_tendsto.log one_ne_zero
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hlim : Tendsto
      (fun τ => (2 * Real.pi) + Real.log (‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)) / τ.im)
      atImInfty (𝓝 (2 * Real.pi)) := by
    simpa using tendsto_const_nhds.add (hlog.div_atTop him)
  refine hlim.congr' ?_
  filter_upwards [modularJ_norm_tendsto_atImInfty.eventually (eventually_gt_atTop (Real.exp 1))]
    with τ hτ
  have hJ : ‖modularJ τ‖ ≠ 0 := ((Real.exp_pos 1).trans hτ).ne'
  rw [max_eq_left hτ.le, Real.log_mul hJ (Real.exp_pos _).ne', Real.log_exp]
  field_simp [τ.im_ne_zero]
  ring

theorem modularIm_logLogJ_fd_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ ModularGroup.fd,
      |Real.log τ.im - Real.log (Real.log (max ‖modularJ τ‖ (Real.exp 1)))| ≤ C := by
  let g (τ : ℍ) := max ‖modularJ τ‖ (Real.exp 1)
  have hg (τ : ℍ) : 0 < g τ := (Real.exp_pos 1).trans_le (le_max_right _ _)
  have hlog (τ : ℍ) : 0 < Real.log (g τ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le (le_max_right _ _))
  have hgcont : Continuous g := modularJ_mdifferentiable.continuous.norm.max continuous_const
  have hcont : Continuous (fun τ : ℍ => Real.log τ.im - Real.log (Real.log (g τ))) :=
    (continuous_im.log fun τ => τ.im_ne_zero).sub
      ((hgcont.log fun τ => (hg τ).ne').log fun τ => (hlog τ).ne')
  have hlim : Tendsto (fun τ : ℍ => -Real.log (Real.log (g τ) / τ.im)) atImInfty
      (𝓝 (-Real.log (2 * Real.pi))) :=
    (log_max_modularJ_div_im_tendsto.log (mul_pos two_pos Real.pi_pos).ne').neg
  refine abs_bound_on_fd_of_tendsto hcont (hlim.congr' ?_)
  filter_upwards with τ
  rw [Real.log_div (hlog τ).ne' τ.im_ne_zero, neg_sub]

end AbcAdaptation.Reference.Heights
