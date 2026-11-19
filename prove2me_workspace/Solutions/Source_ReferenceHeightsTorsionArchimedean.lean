import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Complex.Polynomial.Basic
import Solutions.Source_ReferenceHeightsLatticeModular
import Solutions.Source_TripodCyclicArch

/-!
# Archimedean bound for affine elliptic torsion coordinates

This assembles the estimate in `Heights/TorsionArchimedean.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1` from the lattice uniformization,
the range of the lattice j-invariant and the two modular comparisons.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open WeierstrassCurve
open scoped UpperHalfPlane Classical

/-- The `j`-invariant of the lattice's short Weierstrass model. -/
private noncomputable def latticeJ (hell : ∀ τ : ℍ, (latticeCurve τ).IsElliptic) (τ : ℍ) : ℂ :=
  letI := hell τ
  (latticeCurve τ).j

private lemma one_le_exp_mul_norm_discriminant {W : WeierstrassCurve ℂ} [W.IsElliptic]
    {j : ℂ} {D : ℝ} (h : |-Real.log ‖W.Δ‖ - Real.log (max ‖j‖ 1)| ≤ D) :
    1 ≤ Real.exp D * ‖W.Δ‖ * max ‖j‖ 1 := by
  have hΔ : 0 < ‖W.Δ‖ := norm_pos_iff.mpr W.isUnit_Δ.ne_zero
  have hJ : 0 < max ‖j‖ 1 := one_pos.trans_le (le_max_right _ _)
  have hlog : 0 ≤ D + Real.log (‖W.Δ‖ * max ‖j‖ 1) := by
    rw [Real.log_mul hΔ.ne' hJ.ne']
    linarith only [(abs_le.mp h).2]
  have he := Real.one_le_exp hlog
  rw [Real.exp_add, Real.exp_log (mul_pos hΔ hJ), ← mul_assoc] at he
  exact he

private lemma norm_tau_le {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) {j : ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (h : |Real.log τ.im - Real.log (Real.log (max ‖j‖ (Real.exp 1)))| ≤ C) :
    ‖(τ : ℂ)‖ ≤ Real.exp C * (Real.log (max ‖j‖ (Real.exp 1)) + 1) := by
  have hj : 1 ≤ Real.log (max ‖j‖ (Real.exp 1)) :=
    (Real.le_log_iff_exp_le (lt_max_of_lt_right (Real.exp_pos 1))).mpr (le_max_right _ _)
  have hlog : Real.log τ.im ≤ C + Real.log (Real.log (max ‖j‖ (Real.exp 1))) := by
    linarith only [(abs_le.mp h).2]
  have him := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log τ.im_pos, Real.exp_add, Real.exp_log (zero_lt_one.trans_le hj)] at him
  have hre : |(τ : ℂ).re| ≤ 1 / 2 := hτ.2
  have hhalf : (1 : ℝ) / 2 ≤ Real.exp C := by linarith only [Real.one_le_exp hC]
  calc
    ‖(τ : ℂ)‖ ≤ |(τ : ℂ).re| + |(τ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Real.exp C + Real.exp C * Real.log (max ‖j‖ (Real.exp 1)) := by
      change |(τ : ℂ).re| + |τ.im| ≤ _
      rw [abs_of_pos τ.im_pos]
      exact add_le_add (hre.trans hhalf) him
    _ = _ := by ring

/-- The lattice calculations give the general bound as soon as the actual lattice models
have the stated uniformization, range and modular comparisons. -/
private theorem complexTorsionXBound_of_lattice
    (hell : ∀ τ : ℍ, (latticeCurve τ).IsElliptic)
    (hsurj : ∀ j : ℂ, ∃ τ ∈ ModularGroup.fd, latticeJ hell τ = j)
    (huniform : ∀ τ : ℍ, LatticePointUniformization τ)
    (hdisc : ∃ D : ℝ, 0 ≤ D ∧ ∀ τ ∈ ModularGroup.fd,
      |-Real.log ‖(latticeCurve τ).Δ‖ - Real.log (max ‖latticeJ hell τ‖ 1)| ≤ D)
    (him : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ ModularGroup.fd,
      |Real.log τ.im - Real.log (Real.log (max ‖latticeJ hell τ‖ (Real.exp 1)))| ≤ C) :
    Tripod.ComplexTorsionXBound := by
  obtain ⟨D, _, hD⟩ := hdisc
  obtain ⟨C, hC0, hC⟩ := him
  have hS := latticeSumThree_nonneg
  refine ⟨Real.exp D, 80 * latticeSumThree * Real.exp C ^ 2,
    (Real.exp_pos D).le, by positivity, ?_⟩
  intro W hW N hN x y h hP
  obtain ⟨τ, hτ, hj⟩ := hsurj W.j
  letI := hell τ
  obtain ⟨V, hV⟩ := W.exists_variableChange_of_j_eq (latticeCurve τ) hj.symm
  have hDτ := hD τ hτ
  have hCτ := hC τ hτ
  rw [hj] at hDτ hCτ
  have hlow := one_le_exp_mul_norm_discriminant hDτ
  have hΔ := norm_u_pow_twelve_mul_discriminant hV
  have hu : ‖(V.u : ℂ)‖ ^ 12 ≤ Real.exp D * ‖W.Δ‖ * max ‖W.j‖ 1 := by
    calc
      ‖(V.u : ℂ)‖ ^ 12 ≤ ‖(V.u : ℂ)‖ ^ 12 *
          (Real.exp D * ‖(latticeCurve τ).Δ‖ * max ‖W.j‖ 1) :=
        le_mul_of_one_le_right (by positivity) hlow
      _ = _ := by rw [← hΔ]; ring
  let L := Real.log (max ‖W.j‖ (Real.exp 1))
  let Q := 2 * (N : ℝ) ^ 2 + 80 * latticeSumThree * Real.exp C ^ 2 * (L + 1) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hτnorm := norm_tau_le hτ hC0 hCτ
  have hτsq : ‖(τ : ℂ)‖ ^ 2 ≤ Real.exp C ^ 2 * (L + 1) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hτnorm 2
  have hQle : 2 * (N : ℝ) ^ 2 + 80 * ‖(τ : ℂ)‖ ^ 2 * latticeSumThree ≤ Q := by
    calc
      _ ≤ 2 * (N : ℝ) ^ 2 + 80 * (Real.exp C ^ 2 * (L + 1) ^ 2) * latticeSumThree := by
        gcongr
      _ = Q := by dsimp [Q]; ring
  have hbound := norm_x_sub_r_le hτ (huniform τ) hV hN h hP
  rw [r_eq_neg_b₂_div_twelve hV, sub_neg_eq_add] at hbound
  calc
    ‖x + W.b₂ / 12‖ ^ 6 ≤ (‖(V.u : ℂ)‖ ^ 2 * Q) ^ 6 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound.trans (mul_le_mul_of_nonneg_left hQle (sq_nonneg _))) 6
    _ = ‖(V.u : ℂ)‖ ^ 12 * Q ^ 6 := by rw [mul_pow, ← pow_mul]
    _ ≤ Real.exp D * ‖W.Δ‖ * max ‖W.j‖ 1 * Q ^ 6 :=
      mul_le_mul_of_nonneg_right hu (pow_nonneg hQ _)

/-- The general complex torsion bound from the modular range, two comparisons
on the fundamental domain, and the additive uniformization of the lattice models. -/
theorem complexTorsionXBound_of_modular
    (hsurj : Function.Surjective modularJ)
    (huniform : ∀ τ : ℍ, LatticePointUniformization τ)
    (hdisc : ∃ D : ℝ, 0 ≤ D ∧ ∀ τ ∈ ModularGroup.fd,
      |-Real.log ‖silvermanDiscriminant τ‖ - Real.log (max ‖modularJ τ‖ 1)| ≤ D)
    (him : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ ModularGroup.fd,
      |Real.log τ.im - Real.log (Real.log (max ‖modularJ τ‖ (Real.exp 1)))| ≤ C) :
    Tripod.ComplexTorsionXBound := by
  have hj (τ : ℍ) : latticeJ latticeCurve_isElliptic τ = modularJ τ := by
    letI := latticeCurve_isElliptic τ
    exact latticeCurve_j_eq_modularJ τ
  refine complexTorsionXBound_of_lattice latticeCurve_isElliptic ?_ huniform ?_ ?_
  · intro j
    obtain ⟨τ, hτ, h⟩ := exists_mem_fd_modularJ_eq hsurj j
    exact ⟨τ, hτ, (hj τ).trans h⟩
  · simpa only [hj, latticeCurve_discriminant_eq_silvermanDiscriminant] using hdisc
  · simpa only [hj] using him

end AbcAdaptation.Reference.Heights
