/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Solutions.Source_ReferenceIutCanLiftFrickeRationalRep
import Solutions.Source_ReferenceIutCanLiftProjectiveLine

set_option autoImplicit false

open Matrix OnePoint.Proj
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

variable (p : ℕ) [Fact p.Prime]

private theorem det_map_rep_ne_zero {g : SL(2, ℝ)} (h : IsRatMul g) :
    (h.rep.map (Rat.castHom ℚ_[p])).det ≠ 0 := by
  change ((Rat.castHom ℚ_[p]).mapMatrix h.rep).det ≠ 0
  rw [← (Rat.castHom ℚ_[p]).map_det]
  exact Rat.cast_ne_zero.2 (IsRatMul.det_ne_zero_of h.spec)

/-- Use the chosen rational representative in `GL(2, ℚ_[p])` when it exists. -/
noncomputable def aP (g : SL(2, ℝ)) : GL (Fin 2) ℚ_[p] := by
  classical
  exact if h : IsRatMul g then
    Matrix.GeneralLinearGroup.mkOfDetNeZero (h.rep.map (Rat.castHom ℚ_[p]))
      (det_map_rep_ne_zero p h)
    else 1

theorem coe_aP {g : SL(2, ℝ)} (h : IsRatMul g) :
    (aP p g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = h.rep.map (Rat.castHom ℚ_[p]) := by
  simp only [aP, dif_pos h]
  rfl

variable [DecidableEq ℚ_[p]]

/-- The action on the p-adic projective line is independent of the rational representative. -/
theorem aP_smul {g : SL(2, ℝ)} (h : IsRatMul g) {c : ℝ} (hc : c ≠ 0)
    {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ))
    (y : OnePoint ℚ_[p]) : aP p g • y = mob (R.map (Rat.castHom ℚ_[p])) y := by
  obtain ⟨μ, hμ, rfl⟩ := h.rep_unique hc hR
  have hmap : (μ • h.rep).map (Rat.castHom ℚ_[p]) = (μ : ℚ_[p]) • h.rep.map (Rat.castHom ℚ_[p]) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Rat.coe_castHom, Rat.cast_mul]
  rw [gl_smul_eq_mob, coe_aP p h, hmap, mob_smul_matrix (Rat.cast_ne_zero.2 hμ)]

/-- Rationally represented elements act multiplicatively on the p-adic projective line. -/
theorem actsOn_aP {Δ : Subgroup SL(2, ℝ)} (hΔ : ∀ δ ∈ Δ, IsRatMul δ) :
    ∀ g ∈ Δ, ∀ h ∈ Δ, ∀ y : OnePoint ℚ_[p], aP p (g * h) • y = aP p g • aP p h • y := by
  intro g hg h hh y
  have hg' := hΔ g hg
  have hh' := hΔ h hh
  have hproduct : ((g * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (hg'.scal * hh'.scal) • (hg'.rep * hh'.rep).map (Rat.castHom ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hg'.spec, hh'.spec, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.map_mul (f := Rat.castHom ℝ)]
  rw [aP_smul p (hΔ _ (mul_mem hg hh)) (mul_ne_zero hg'.scal_ne_zero hh'.scal_ne_zero) hproduct,
    aP_smul p hg' hg'.scal_ne_zero hg'.spec, aP_smul p hh' hh'.scal_ne_zero hh'.spec,
    Matrix.map_mul (f := Rat.castHom ℚ_[p]), mob_mul (det_map_rep_ne_zero p hh')]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
