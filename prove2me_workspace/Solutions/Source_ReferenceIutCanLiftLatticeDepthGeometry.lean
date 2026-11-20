/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Depth.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeDepthDomain

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} {U : LatticeComplementCover (periodPair t)}

/-- An upper bound on the height of the base-point orbit gives a lower bound on depth. -/
theorem im_le_bound_mul_exp_depth {M : SL(2, ℝ)} {H : ℝ}
    (hH : 0 < H) (hh : ∀ γ ∈ U.deckGroup, (M⁻¹ • (γ • e₀ U)).im ≤ H) (τ : ℍ) :
    (M⁻¹ • τ).im ≤ H * Real.exp (depth U τ) := by
  have hlog : Real.log (M⁻¹ • τ).im - Real.log H ≤ depth U τ := by
    refine le_depth fun γ hγ ↦ ?_
    let y : ℍ := M⁻¹ • (γ⁻¹ • e₀ U)
    have hy : y.im ≤ H := hh _ (inv_mem hγ)
    calc
      Real.log (M⁻¹ • τ).im - Real.log H ≤ Real.log (M⁻¹ • τ).im - Real.log y.im :=
        sub_le_sub_left (Real.log_le_log y.im_pos hy) _
      _ ≤ dist (Real.log (M⁻¹ • τ).im) (Real.log y.im) := by
        rw [Real.dist_eq]
        exact le_abs_self _
      _ ≤ dist (M⁻¹ • τ) y := UpperHalfPlane.dist_log_im_le _ _
      _ = dist (γ • τ) (e₀ U) := by
        dsimp only [y]
        rw [dist_smul, ← dist_smul γ τ (γ⁻¹ • e₀ U), smul_inv_smul]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log (M⁻¹ • τ).im_pos, Real.exp_log hH] at hexp
  exact (div_le_iff₀' hH).mp hexp

private theorem exp_dist_le_of_abs_re_sub_le {z w : ℍ} {R : ℝ}
    (hre : |z.re - w.re| ≤ R) (him : 1 ≤ z.im) :
    Real.exp (dist z w) ≤ (R ^ 2 + w.im ^ 2) / w.im + z.im / w.im := by
  have hsq : (z.re - w.re) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have hprod : 0 < z.im * w.im := mul_pos z.im_pos w.im_pos
  have hwprod : w.im ≤ z.im * w.im := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right him w.im_pos.le
  calc
    Real.exp (dist z w) ≤ 2 * Real.cosh (dist z w) := by
      rw [Real.cosh_eq]
      linarith only [Real.exp_pos (-dist z w)]
    _ = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (z.im * w.im) := by
      rw [UpperHalfPlane.cosh_dist']
      field_simp [z.im_pos.ne', w.im_pos.ne'] <;> ring
    _ ≤ (R ^ 2 + z.im ^ 2 + w.im ^ 2) / (z.im * w.im) :=
      div_le_div_of_nonneg_right (by linarith only [hsq]) hprod.le
    _ = (R ^ 2 + w.im ^ 2) / (z.im * w.im) + z.im / w.im := by
      field_simp [z.im_pos.ne', w.im_pos.ne'] <;> ring
    _ ≤ (R ^ 2 + w.im ^ 2) / w.im + z.im / w.im :=
      add_le_add_left (div_le_div_of_nonneg_left (by positivity) w.im_pos hwprod) _

/-- With bounded horizontal displacement, exponential depth grows at most linearly in height. -/
theorem exp_depth_le_of_cusp_coordinates {M : SL(2, ℝ)} {R : ℝ} (τ : ℍ)
    (hre : |(M⁻¹ • τ).re - (M⁻¹ • e₀ U).re| ≤ R) (him : 1 ≤ (M⁻¹ • τ).im) :
    Real.exp (depth U τ) ≤ (R ^ 2 + (M⁻¹ • e₀ U).im ^ 2) / (M⁻¹ • e₀ U).im
      + (M⁻¹ • τ).im / (M⁻¹ • e₀ U).im := by
  have hdist : depth U τ ≤ dist (M⁻¹ • τ) (M⁻¹ • e₀ U) := by
    rw [dist_smul]
    simpa only [one_smul] using depth_le (U := U) (τ := τ) U.deckGroup.one_mem
  exact (Real.exp_le_exp.mpr hdist).trans (exp_dist_le_of_abs_re_sub_le hre him)

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
