/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/JOrb.lean, lines 397–576
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiCayleyAction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open AbcAdaptation.Reference
open Complex Filter Metric Set
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Topology UpperHalfPlane Modular

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-! ### The stabilisers of `i` and `ρ` -/

theorem cmul_sq_of_fix_I {γ : SL(2, ℤ)} (h : γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    cmul γ UpperHalfPlane.I ^ 2 = 1 := by
  have hfix := fix_eq h
  have hre : ((γ 0 1 : ℤ) : ℝ) = -(γ 1 0 : ℝ) := by simpa using congrArg Complex.re hfix
  have him : ((γ 0 0 : ℤ) : ℝ) = (γ 1 1 : ℝ) := by simpa using congrArg Complex.im hfix
  have hb : γ 0 1 = -γ 1 0 := by exact_mod_cast hre
  have ha : γ 0 0 = γ 1 1 := by exact_mod_cast him
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast det_coe γ
  rw [ha, hb] at hdet
  have hcd : γ 1 0 * γ 1 1 = 0 := by
    have h1 : γ 1 0 ^ 2 ≤ 1 := by nlinarith
    have h2 : -1 ≤ γ 1 0 ∧ γ 1 0 ≤ 1 := by constructor <;> nlinarith
    rcases h2 with ⟨h2, h3⟩
    interval_cases hc : γ 1 0
    · have : γ 1 1 = 0 := by nlinarith
      simp [this]
    · simp
    · have : γ 1 1 = 0 := by nlinarith
      simp [this]
  have hcd' : (γ 1 0 : ℂ) * γ 1 1 = 0 := by exact_mod_cast hcd
  have hD := denom_coe_ne_zero γ (z := Complex.I) (by simp)
  rw [cmul, coe_I, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hD), conj_I]
  linear_combination (-4 * Complex.I) * hcd'

private theorem coe_ρ : (ρ : ℂ) = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := rfl

private theorem conj_ρ : conj (ρ : ℂ) = -1 - ρ := by
  apply Complex.ext <;> norm_num [coe_ρ]

private theorem ρ_sq' : (ρ : ℂ) ^ 2 + ρ + 1 = 0 := by
  linear_combination ρ_sq

private theorem ρ_im_ne : (ρ : ℂ).im ≠ 0 := ρ.im_pos.ne'

theorem cmul_cube_of_fix_ρ {γ : SL(2, ℤ)} (h : γ • ρ = ρ) : cmul γ ρ ^ 3 = 1 := by
  have hfix := fix_eq h
  have key : (((γ 0 0 + γ 1 0 - γ 1 1 : ℤ) : ℂ)) * ρ + ((γ 0 1 + γ 1 0 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination hfix + (γ 1 0 : ℂ) * ρ_sq'
  have him := congrArg Complex.im key
  have hre := congrArg Complex.re key
  simp only [mul_im, intCast_re, intCast_im, zero_mul, add_zero, add_im, zero_im,
    mul_re, add_re, sub_zero, zero_re] at him hre
  have ha : γ 0 0 + γ 1 0 - γ 1 1 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' ρ_im_ne
  rw [ha] at hre
  simp only [Int.cast_zero, zero_mul, zero_add] at hre
  have hb : γ 0 1 + γ 1 0 = 0 := by exact_mod_cast hre
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast det_coe γ
  have hq : γ 1 1 ^ 2 - γ 1 0 * γ 1 1 + γ 1 0 ^ 2 = 1 := by
    have h1 : γ 0 0 = γ 1 1 - γ 1 0 := by linarith
    have h2 : γ 0 1 = - γ 1 0 := by linarith
    rw [h1, h2] at hdet
    linear_combination hdet
  have hc3 : γ 1 0 ^ 3 = γ 1 0 := by
    have h1 : -1 ≤ γ 1 0 ∧ γ 1 0 ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (2 * γ 1 1 - γ 1 0)]
    rcases h1 with ⟨h1, h2⟩
    interval_cases γ 1 0 <;> norm_num
  have hq' : (γ 1 1 : ℂ) ^ 2 - γ 1 0 * γ 1 1 + (γ 1 0 : ℂ) ^ 2 = 1 := by exact_mod_cast hq
  have hc3' : (γ 1 0 : ℂ) ^ 3 = γ 1 0 := by exact_mod_cast hc3
  have hD := denom_coe_ne_zero γ ρ.im_pos
  rw [cmul, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hD), conj_ρ]
  linear_combination (-2 * (γ 1 0 : ℂ) ^ 3 * ρ - (γ 1 0 : ℂ) ^ 3) * ρ_sq' +
    (-6 * (γ 1 0 : ℂ) * ρ - 3 * (γ 1 0 : ℂ)) * hq' + (6 * (ρ : ℂ) + 3) * hc3'

/-- The element `[[-1, -1], [1, 0]]` of order `3` in `PSL(2, ℤ)`, fixing `ρ`. -/
def gρ : SL(2, ℤ) := ⟨!![-1, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem gρ_smul : gρ • ρ = ρ := by
  apply smul_eq_self_of
  simp only [gρ, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Int.cast_neg, Int.cast_one, Int.cast_zero]
  linear_combination -ρ_sq

theorem cmul_gρ : cmul gρ ρ = ρ := by
  have hρ : (ρ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; exact ρ_im_ne (by simpa using this)
  simp only [cmul, gρ, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Int.cast_one, Int.cast_zero, one_mul, add_zero, conj_ρ]
  rw [div_eq_iff hρ]
  linear_combination -ρ_sq

private theorem ρ_ne_one : (ρ : ℂ) ≠ 1 := by
  intro h; have := congrArg Complex.re h; norm_num [coe_ρ] at this

private theorem ρ_cube : (ρ : ℂ) ^ 3 = 1 := by
  linear_combination ((ρ : ℂ) - 1) * ρ_sq'

theorem dvd_of_ρ_pow {m : ℕ} (h : (ρ : ℂ) ^ m = 1) : 3 ∣ m := by
  have : orderOf (ρ : ℂ) = 3 := orderOf_eq_prime ρ_cube ρ_ne_one
  rw [← this]
  exact orderOf_dvd_of_pow_eq_one h

theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply smul_eq_self_of
  simp only [ModularGroup.S, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, Int.cast_zero, coe_I]
  ring_nf
  rw [I_sq]

theorem cmul_S_I : cmul ModularGroup.S UpperHalfPlane.I = -1 := by
  simp only [cmul, ModularGroup.S, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero, one_mul, add_zero, coe_I, conj_I]
  rw [div_eq_iff I_ne_zero]
  ring

theorem dvd_of_neg_one_pow {m : ℕ} (h : (-1 : ℂ) ^ m = 1) : 2 ∣ m := by
  have : orderOf (-1 : ℂ) = 2 := orderOf_eq_prime (by norm_num) (by norm_num)
  rw [← this]
  exact orderOf_dvd_of_pow_eq_one h

section values

open Matrix.SpecialLinearGroup CongruenceSubgroup

private theorem E₄_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * ModularForm.E₄ τ := by
  let : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₄ (mem_Gamma_one γ) τ

private theorem E₆_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₆ (γ • τ) = denom γ τ ^ (6 : ℤ) * ModularForm.E₆ τ := by
  let : SlashInvariantFormClass (ModularForm 𝒮ℒ 6) Γ(1) 6 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₆ (mem_Gamma_one γ) τ

private theorem E₄_ρ : ModularForm.E₄ ρ = 0 := by
  have h := E₄_smul gρ ρ
  rw [gρ_smul] at h
  have hd : denom gρ ρ = ρ := by
    have hc : gρ 1 0 = 1 := rfl
    have hd : gρ 1 1 = 0 := rfl
    simp [ModularGroup.denom_apply, hc, hd]
  rw [hd] at h
  have h4 : (ρ : ℂ) ^ (4 : ℤ) = ρ := by
    rw [show (4 : ℤ) = ((3 + 1 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, ρ_cube, one_mul]
  rw [h4] at h
  have : (1 - (ρ : ℂ)) * ModularForm.E₄ ρ = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ρ_ne_one.symm)

private theorem E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have h := E₆_smul ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I] at h
  have hd : denom ModularGroup.S UpperHalfPlane.I = Complex.I :=
    ModularGroup.denom_S UpperHalfPlane.I
  rw [hd] at h
  have h6 : Complex.I ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast,
      show 6 = 2 * 3 by norm_num, pow_mul, I_sq]
    norm_num
  rw [h6] at h
  linear_combination h / 2

theorem modularJ_ρ : Heights.modularJ ρ = 0 := by
  simp [Heights.modularJ, E₄_ρ]

theorem modularJ_I : Heights.modularJ UpperHalfPlane.I = 1728 := by
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [E₆_I, zero_pow two_ne_zero, sub_zero] at hΔ
  have hE : ModularForm.E₄ UpperHalfPlane.I ^ 3 ≠ 0 := by
    intro h
    rw [h, zero_div] at hΔ
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I hΔ
  rw [Heights.modularJ, hΔ, div_div_eq_mul_div, mul_div_cancel_left₀ _ hE]

end values

theorem jC_ρ : jC ρ = 0 := by rw [jC_coe, modularJ_ρ]

theorem jC_I : jC UpperHalfPlane.I = 1728 := by rw [jC_coe, modularJ_I]

theorem jBranch_eq : jBranch = {1728, 0} := by
  rw [jBranch, modularJ_I, modularJ_ρ]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
