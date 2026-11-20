/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/JOrb.lean, lines 195–396
-/
import Solutions.Source_ReferenceIutCanLiftCayley
import Solutions.Source_ReferenceIutCanLiftModularCovering
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open AbcAdaptation.Reference
open Complex Filter Metric Set
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Topology UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-! ### The Cayley map centred at a point of `ℍ` -/

/-- The Cayley map `ℍ → 𝔻` centred at `τ`. -/
noncomputable def cay (τ z : ℂ) : ℂ := (z - τ) / (z - conj τ)

/-- The inverse of the Cayley map centred at `τ`. -/
noncomputable def cayInv (τ s : ℂ) : ℂ := (τ - conj τ * s) / (1 - s)

theorem sub_conj_ne_zero {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : z - conj τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, conj_im, zero_im] at this
  linarith

theorem one_sub_ne_zero_of_norm_lt {s : ℂ} (hs : ‖s‖ < 1) : 1 - s ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hs
  exact lt_irrefl _ hs

theorem cay_self (τ : ℂ) : cay τ τ = 0 := by simp [cay]

theorem cayInv_zero (τ : ℂ) : cayInv τ 0 = τ := by simp [cayInv]

theorem cayInv_cay {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : cayInv τ (cay τ z) = z := by
  have h1 := sub_conj_ne_zero hτ hz
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  unfold cayInv cay
  rw [div_eq_iff]
  · field_simp
    ring
  · rw [one_sub_div h1]
    exact div_ne_zero (by rwa [sub_sub_sub_cancel_left]) h1

theorem cay_cayInv {τ s : ℂ} (hτ : 0 < τ.im) (hs : ‖s‖ < 1) : cay τ (cayInv τ s) = s := by
  have h1 := one_sub_ne_zero_of_norm_lt hs
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  unfold cayInv cay
  have h3 : (τ - conj τ * s) / (1 - s) - conj τ = (τ - conj τ) / (1 - s) := by
    field_simp; ring
  rw [h3, div_eq_iff (div_ne_zero h2 h1)]
  field_simp
  ring

theorem cayInv_eq (τ s : ℂ) (hs : ‖s‖ < 1) :
    cayInv τ s = τ.re + τ.im * CanLiftAnalytic.cayleyInv s := by
  have h1 := one_sub_ne_zero_of_norm_lt hs
  unfold cayInv CanLiftAnalytic.cayleyInv
  field_simp
  apply Complex.ext <;> simp <;> ring

theorem im_cayInv_pos {τ s : ℂ} (hτ : 0 < τ.im) (hs : ‖s‖ < 1) : 0 < (cayInv τ s).im := by
  rw [cayInv_eq τ s hs]
  have := CanLiftAnalytic.im_cayleyInv_pos (w := s) (by rwa [mem_ball_zero_iff])
  simpa using mul_pos hτ this

theorem analyticAt_cayInv (τ : ℂ) {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (cayInv τ) s :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hs.symm)

theorem analyticAt_cay {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : AnalyticAt ℂ (cay τ) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
    (sub_conj_ne_zero hτ hz)

theorem deriv_cay_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : deriv (cay τ) τ ≠ 0 := by
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  have hd : HasDerivAt (cay τ) ((1 * (τ - conj τ) - (τ - τ) * 1) / (τ - conj τ) ^ 2) τ :=
    ((hasDerivAt_id τ).sub_const τ).div ((hasDerivAt_id τ).sub_const _) h2
  rw [hd.deriv, sub_self, zero_mul, sub_zero, one_mul]
  exact div_ne_zero h2 (pow_ne_zero _ h2)

theorem continuousOn_cay {τ : ℂ} (hτ : 0 < τ.im) : ContinuousOn (cay τ) {z : ℂ | 0 < z.im} :=
  fun _ hz ↦ (analyticAt_cay hτ hz).continuousAt.continuousWithinAt

/-! ### The action of `SL(2, ℤ)` on `ℂ` -/

/-- The Möbius transformation of `γ` as a function on `ℂ`. -/
noncomputable def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

theorem det_coe (γ : SL(2, ℤ)) : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

theorem denom_coe_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
  have hc : γ 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' hz.ne'
  have hre := congrArg Complex.re h
  simp only [hc, Int.cast_zero, zero_mul, zero_add, intCast_re, zero_re] at hre
  have hd : γ 1 1 = 0 := by exact_mod_cast hre
  have := det_coe γ
  rw [hc, hd] at this
  simp at this

theorem smulC_eq_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ z = mob γ z := by
  rw [smulC_of_im_pos γ hz, coe_specialLinearGroup_apply]
  simp [mob]

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul (γ 0 0 : ℂ) |>.add_const (γ 0 1 : ℂ)).div
    ((hasDerivAt_id z).const_mul (γ 1 0 : ℂ) |>.add_const (γ 1 1 : ℂ)) (denom_coe_ne_zero γ hz)
  refine h.congr_deriv ?_
  congr 1
  simp only [id]
  linear_combination det_coe γ

theorem smulC_eventuallyEq_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    smulC γ =ᶠ[𝓝 z] mob γ := by
  filter_upwards [isOpen_upper.mem_nhds hz] with y hy
  exact smulC_eq_mob γ hy

theorem hasDerivAt_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (smulC γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z :=
  (hasDerivAt_mob γ hz).congr_of_eventuallyEq (smulC_eventuallyEq_mob γ hz)

theorem differentiableOn_smulC (γ : SL(2, ℤ)) : DifferentiableOn ℂ (smulC γ) {z : ℂ | 0 < z.im} :=
  fun _ hz ↦ (hasDerivAt_smulC γ hz).differentiableAt.differentiableWithinAt

theorem analyticAt_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (smulC γ) z :=
  (differentiableOn_smulC γ).analyticAt (isOpen_upper.mem_nhds hz)

theorem deriv_smulC_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : deriv (smulC γ) z ≠ 0 := by
  rw [(hasDerivAt_smulC γ hz).deriv]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ (denom_coe_ne_zero γ hz))

theorem smulC_smulC (γ γ' : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    smulC γ (smulC γ' z) = smulC (γ * γ') z := by
  rw [smulC_of_im_pos γ' hz, smulC_of_im_pos γ (γ' • (⟨z, hz⟩ : ℍ)).im_pos,
    smulC_of_im_pos _ hz, mul_smul]

theorem smulC_one {z : ℂ} (hz : 0 < z.im) : smulC 1 z = z := by
  rw [smulC_of_im_pos 1 hz, one_smul]

theorem smulC_inv_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ⁻¹ (smulC γ z) = z := by
  rw [smulC_smulC _ _ hz, inv_mul_cancel, smulC_one hz]

theorem smulC_smulC_inv (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ (smulC γ⁻¹ z) = z := by
  rw [smulC_smulC _ _ hz, mul_inv_cancel, smulC_one hz]

theorem smulC_coe (γ : SL(2, ℤ)) (τ : ℍ) : smulC γ τ = ((γ • τ : ℍ) : ℂ) :=
  smulC_of_im_pos γ τ.im_pos

/-! ### The stabiliser acts by rotations in the Cayley coordinate -/

/-- The rotation factor of `γ` at a fixed point `τ`, in the Cayley coordinate at `τ`. -/
noncomputable def cmul (γ : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  ((γ 1 0 : ℂ) * conj τ + γ 1 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)

theorem fix_eq {γ : SL(2, ℤ)} {τ : ℍ} (h : γ • τ = τ) :
    (γ 0 0 : ℂ) * τ + γ 0 1 = τ * ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  have h' := congrArg ((↑) : ℍ → ℂ) h
  rw [← smulC_coe, smulC_eq_mob γ τ.im_pos, mob, div_eq_iff (denom_coe_ne_zero γ τ.im_pos)] at h'
  exact h'

theorem smul_eq_self_of {γ : SL(2, ℤ)} {τ : ℍ}
    (h : (γ 0 0 : ℂ) * τ + γ 0 1 = τ * ((γ 1 0 : ℂ) * τ + γ 1 1)) : γ • τ = τ := by
  apply UpperHalfPlane.ext
  rw [← smulC_coe, smulC_eq_mob γ τ.im_pos, mob, div_eq_iff (denom_coe_ne_zero γ τ.im_pos)]
  exact h

private theorem conj_denom (γ : SL(2, ℤ)) (τ : ℂ) :
    (γ 1 0 : ℂ) * conj τ + γ 1 1 = conj ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  simp only [map_add, map_mul, map_intCast]

private theorem mob_sub_aux (a b c d t z : ℂ) (hdet : a * d - b * c = 1)
    (ht : a * t + b = t * (c * t + d)) (hD : c * z + d ≠ 0) (hDt : c * t + d ≠ 0) :
    (a * z + b) / (c * z + d) - t = (z - t) / ((c * z + d) * (c * t + d)) := by
  rw [eq_div_iff (mul_ne_zero hD hDt)]
  have e : (a * z + b) / (c * z + d) * (c * z + d) = a * z + b := div_mul_cancel₀ _ hD
  linear_combination (c * t + d) * e + (z - t) * hdet + (c * z + d) * ht

theorem cay_smulC {γ : SL(2, ℤ)} {τ : ℍ} (hγ : γ • τ = τ) {z : ℂ} (hz : 0 < z.im) :
    cay τ (smulC γ z) = cmul γ τ * cay τ z := by
  have hdet := det_coe γ
  have ht := fix_eq hγ
  have ht' : (γ 0 0 : ℂ) * conj (τ : ℂ) + γ 0 1 =
      conj (τ : ℂ) * ((γ 1 0 : ℂ) * conj (τ : ℂ) + γ 1 1) := by
    have := congrArg conj ht
    simpa only [map_add, map_mul, map_intCast] using this
  have hD := denom_coe_ne_zero γ hz
  have hDt := denom_coe_ne_zero γ τ.im_pos
  have hDt' : (γ 1 0 : ℂ) * conj (τ : ℂ) + γ 1 1 ≠ 0 := by
    rw [conj_denom]; exact (map_ne_zero _).mpr hDt
  have hz' := sub_conj_ne_zero τ.im_pos hz
  rw [smulC_eq_mob γ hz, cay, mob, mob_sub_aux _ _ _ _ _ _ hdet ht hD hDt,
    mob_sub_aux _ _ _ _ _ _ hdet ht' hD hDt', cmul, cay]
  have hD2 : z * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  have hDt2 : (τ : ℂ) * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  field_simp

theorem norm_cmul (γ : SL(2, ℤ)) (τ : ℍ) : ‖cmul γ τ‖ = 1 := by
  have hDt := denom_coe_ne_zero γ τ.im_pos
  rw [cmul, conj_denom, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hDt)]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
