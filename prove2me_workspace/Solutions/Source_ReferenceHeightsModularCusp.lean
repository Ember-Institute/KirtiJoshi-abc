import Solutions.Source_ReferenceHeightsLatticeModular
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Behavior of modular `j` at the cusp

The source is `Heights/ModularJ.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open Filter Topology UpperHalfPlane
open scoped UpperHalfPlane Manifold Modular

theorem E₄_tendsto_atImInfty : Tendsto (fun τ : ℍ => ModularForm.E₄ τ) atImInfty (𝓝 1) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL
  have han := analyticAt_cuspFunction_zero one_pos hper
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
  have hconst : valueAtInfty (ModularForm.E₄ : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos han hper]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by decide) ⟨2, rfl⟩
  have hlim : Tendsto (cuspFunction 1 (ModularForm.E₄ : ℍ → ℂ)) (𝓝 0) (𝓝 1) := by
    convert han.continuousAt.tendsto using 1
    rw [cuspFunction_apply_zero one_pos han hper, hconst]
  refine (hlim.comp (qParam_tendsto_atImInfty one_pos)).congr' ?_
  exact Eventually.of_forall fun τ => SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ
    one_mem_strictPeriods_SL one_ne_zero

private theorem scaled_discriminant_tendsto : Tendsto
    (fun τ : ℍ => ‖ModularForm.discriminant τ‖ / Real.exp (-2 * Real.pi * τ.im))
    atImInfty (𝓝 1) := by
  have h := ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.norm
  rw [norm_one] at h
  apply h.congr'
  filter_upwards with τ
  symm
  have hq : ‖Function.Periodic.qParam 1 τ‖ = Real.exp (-2 * Real.pi * τ.im) := by
    simp [Function.Periodic.qParam, Complex.norm_exp]
  rw [ModularForm.discriminant_eq_q_prod, norm_mul, hq]
  field_simp

theorem scaled_modularJ_tendsto : Tendsto
    (fun τ : ℍ => ‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 1) := by
  have h := (E₄_tendsto_atImInfty.pow 3).norm.div scaled_discriminant_tendsto (by norm_num)
  rw [one_pow, norm_one, div_one] at h
  apply h.congr'
  filter_upwards with τ
  change ‖ModularForm.E₄ τ ^ 3‖ /
      (‖ModularForm.discriminant τ‖ / Real.exp (-2 * Real.pi * τ.im)) = _
  rw [modularJ, norm_div, div_div_eq_mul_div, div_mul_eq_mul_div₀]

theorem modularJ_mdifferentiable : MDiff modularJ :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (by simpa only [CuspForm.coe_discriminant] using ModularFormClass.holo CuspForm.discriminant)
    ModularForm.discriminant_ne_zero

theorem modularJ_norm_tendsto_atImInfty :
    Tendsto (fun τ : ℍ => ‖modularJ τ‖) atImInfty atTop := by
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hexp : Tendsto (fun τ : ℍ => Real.exp (2 * Real.pi * τ.im)) atImInfty atTop :=
    Real.tendsto_exp_atTop.comp (him.const_mul_atTop (mul_pos two_pos Real.pi_pos))
  rw [tendsto_atTop]
  intro r
  have hscale : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖modularJ τ‖ * Real.exp (-2 * Real.pi * τ.im) :=
    scaled_modularJ_tendsto.eventually (Ici_mem_nhds (by norm_num))
  have hlarge := hexp.eventually (eventually_ge_atTop (2 * r))
  filter_upwards [hscale, hlarge] with τ hτ hlarge
  have hf := mul_le_mul_of_nonneg_right hτ (Real.exp_pos (2 * Real.pi * τ.im)).le
  have he : Real.exp (-2 * Real.pi * τ.im) * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [mul_assoc ‖modularJ τ‖ _ _, he, mul_one] at hf
  linarith only [hf, hlarge]

end AbcAdaptation.Reference.Heights
