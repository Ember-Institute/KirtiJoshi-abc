/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Solutions.Source_ReferenceIutCanLiftFrickeRational

set_option autoImplicit false

open Matrix
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2.IsRatMul

variable {g : SL(2, ℝ)}

/-- The chosen real scale of a rational matrix representative. -/
noncomputable def scal (h : IsRatMul g) : ℝ := h.choose

/-- The chosen rational matrix representative. -/
noncomputable def rep (h : IsRatMul g) : Matrix (Fin 2) (Fin 2) ℚ := h.choose_spec.2.choose

theorem scal_ne_zero (h : IsRatMul g) : h.scal ≠ 0 := h.choose_spec.1

theorem spec (h : IsRatMul g) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) = h.scal • h.rep.map (Rat.castHom ℝ) :=
  h.choose_spec.2.choose_spec

/-- Every rational matrix representative of a determinant-one matrix is invertible. -/
theorem det_ne_zero_of {c : ℝ} {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ)) : R.det ≠ 0 := by
  intro hzero
  have hdet := g.det_coe
  rw [hR, Matrix.det_smul, Fintype.card_fin] at hdet
  change c ^ 2 * ((Rat.castHom ℝ).mapMatrix R).det = 1 at hdet
  rw [← (Rat.castHom ℝ).map_det, hzero, map_zero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Two rational representatives of the same real matrix differ by a nonzero rational scale. -/
theorem rep_unique (h : IsRatMul g) {c : ℝ} (hc : c ≠ 0) {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ)) :
    ∃ μ : ℚ, μ ≠ 0 ∧ R = μ • h.rep := by
  have hrep0 : h.rep ≠ 0 := by
    intro hzero
    exact det_ne_zero_of h.spec (by rw [hzero, Matrix.det_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, h.rep i j ≠ 0 := by
    by_contra hno
    apply hrep0
    ext i j
    change h.rep i j = 0
    by_contra hij
    exact hno ⟨i, j, hij⟩
  have hentry (a b : Fin 2) : c * (R a b : ℝ) = h.scal * (h.rep a b : ℝ) := by
    simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Rat.coe_castHom] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M a b) (hR.symm.trans h.spec)
  let μ : ℚ := R i j / h.rep i j
  have hijReal : (h.rep i j : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hij
  have hμ : (μ : ℝ) = h.scal / c := by
    rw [show (μ : ℝ) = (R i j : ℝ) / (h.rep i j : ℝ) from Rat.cast_div _ _,
      div_eq_div_iff hijReal hc, mul_comm (R i j : ℝ) c]
    exact hentry i j
  refine ⟨μ, Rat.cast_ne_zero.1 (by rw [hμ]; exact div_ne_zero h.scal_ne_zero hc), ?_⟩
  ext a b
  change R a b = μ * h.rep a b
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_mul, hμ]
  calc
    (R a b : ℝ) = c * (R a b : ℝ) / c := (mul_div_cancel_left₀ _ hc).symm
    _ = (h.scal * (h.rep a b : ℝ)) / c := by rw [hentry]
    _ = (h.scal / c) * (h.rep a b : ℝ) := (div_mul_eq_mul_div _ _ _).symm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2.IsRatMul
