/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as stated in the upstream source header.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.Data.Rat.Cast.Order
import Solutions.Source_ReferenceIutCanLiftDenseUnipotents
import Solutions.Source_ReferenceIutCanLiftFrickeComplexAction
import Solutions.Source_ReferenceIutCanLiftPadicAction

set_option autoImplicit false

/-!
# The p-adic projective action of the Fricke normal form

The commutator acts by translation by two and the first generator moves infinity.
A nonintegral squared trace gives the norm inequality for the p-adic unboundedness proof.
-/

open OnePoint OnePoint.Proj
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (nA coe_nA)

variable (p : ℕ) [Fact p.Prime]

/-- A nonintegral squared trace gives dominance of the trace over the determinant in norm. -/
theorem aP_det_norm_lt_trace_norm_sq {g : SL(2, ℝ)} (h : IsRatMul g)
    (hlarge : 1 < padicNorm p (h.rep.trace ^ 2 / h.rep.det)) :
    ‖(aP p g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ <
      ‖(aP p g : Matrix (Fin 2) (Fin 2) ℚ_[p]).trace‖ ^ 2 := by
  rw [coe_aP p h]
  change ‖((Rat.castHom ℚ_[p]).mapMatrix h.rep).det‖ <
    ‖(h.rep.map (Rat.castHom ℚ_[p])).trace‖ ^ 2
  rw [← (Rat.castHom ℚ_[p]).map_det, ← AddMonoidHom.map_trace (Rat.castHom ℚ_[p]) h.rep]
  simp only [Rat.coe_castHom, Padic.eq_padicNorm]
  have hdet := IsRatMul.det_ne_zero_of h.spec
  have hpos : 0 < padicNorm p h.rep.det :=
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hdet).symm
  rw [padicNorm.div, sq, padicNorm.mul, one_lt_div hpos] at hlarge
  rw [← Rat.cast_pow, Rat.cast_lt]
  simpa only [sq] using hlarge

variable [DecidableEq ℚ_[p]]

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

theorem aP_commK (hK : IsRatMul (commK hz hrel)) (w : OnePoint ℚ_[p]) :
    aP p (commK hz hrel) • w = transl (2 : ℚ_[p]) • w := by
  have hrep : (commK hz hrel : Matrix (Fin 2) (Fin 2) ℝ) =
      (1 : ℝ) • (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) := by
    rw [coe_commK, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [aP_smul p hK one_ne_zero hrep, gl_smul_eq_mob]
  have hmatrix : (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℚ_[p]) =
      (-1 : ℚ_[p]) • (transl (2 : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transl]
  rw [hmatrix, mob_smul_matrix (neg_ne_zero.mpr one_ne_zero)]

theorem aP_nA_infty (hA : IsRatMul (nA hz hrel)) (hx : x ≠ 0) :
    aP p (nA hz hrel) • (∞ : OnePoint ℚ_[p]) ≠ ∞ := by
  rw [Ne, smul_infty_eq_self_iff, coe_aP p hA]
  change (hA.rep 1 0 : ℚ_[p]) ≠ 0
  apply Rat.cast_ne_zero.mpr
  intro hzero
  apply hx
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 0) hA.spec
  rw [coe_nA] at hentry
  simpa only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Rat.coe_castHom, hzero, Rat.cast_zero, mul_zero] using hentry

theorem aP_uU_two (hU : IsRatMul (SL2R.uU 2)) (w : OnePoint ℚ_[p]) :
    aP p (SL2R.uU 2) • w = transl (2 : ℚ_[p]) • w := by
  have hrep : (SL2R.uU 2 : Matrix (Fin 2) (Fin 2) ℝ) =
      (1 : ℝ) • (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) := by
    rw [SL2R.coe_uU, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [aP_smul p hU one_ne_zero hrep, gl_smul_eq_mob]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transl]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
