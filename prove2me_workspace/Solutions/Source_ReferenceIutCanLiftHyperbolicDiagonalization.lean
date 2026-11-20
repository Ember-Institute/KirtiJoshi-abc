/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/FrickeRigidity.lean
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Matrix

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.SL2R

/-- The larger eigenvalue `(x + √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigBig (x : ℝ) : ℝ := (x + Real.sqrt (x ^ 2 - 4)) / 2

/-- The smaller eigenvalue `(x - √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigSmall (x : ℝ) : ℝ := (x - Real.sqrt (x ^ 2 - 4)) / 2

section eig

variable {x : ℝ} (hx : 4 < x ^ 2)
include hx

omit hx in
lemma eig_sum : eigBig x + eigSmall x = x := by unfold eigBig eigSmall; ring

lemma eig_prod : eigBig x * eigSmall x = 1 := by
  unfold eigBig eigSmall
  have := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 by linarith)
  linear_combination (-1 / 4 : ℝ) * this

lemma eig_sub_pos : 0 < eigBig x - eigSmall x := by
  unfold eigBig eigSmall
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < x ^ 2 - 4 by linarith)
  linarith

end eig

/-- Diagonalisation, in coordinates: for `A = [[p, q], [r, s]]` with `ps - qr = 1` and roots
`l ≠ m` of `t² - (p + s) t + 1`, an explicit invertible `P` with `P A = diag(l, m) P`. -/
private lemma exists_diagonalize_aux (p q r s l m : ℝ) (hd : p * s - q * r = 1)
    (hsum : l + m = p + s) (hprod : l * m = 1) (hne : l - m ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * !![p, q; r, s] = !![l, 0; 0, m] * P := by
  have hl : l ^ 2 - (p + s) * l + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  have hm : m ^ 2 - (p + s) * m + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  by_cases hr : r = 0
  · subst hr
    have hp : (p - l) * (p - m) = 0 := by linear_combination -p * hsum - hd + hprod
    rcases mul_eq_zero.mp hp with hpl | hpm
    · have hpl' : p = l := by linarith
      have hsm : s = m := by linarith
      subst hpl' hsm
      refine ⟨!![p - s, q; 0, s - p], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
    · have hpm' : p = m := by linarith
      have hsl : s = l := by linarith
      subst hpm' hsl
      refine ⟨!![0, s - p; p - s, q], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
  · refine ⟨!![r, l - p; r, m - p], ?_, ?_⟩
    · rw [det_fin_two_of]
      have : r * (m - p) - (l - p) * r = -(r * (l - m)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero hr hne
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      · ring
      · linear_combination -hl - hd
      · ring
      · linear_combination -hm - hd

/-- **Diagonalisation of a hyperbolic element.** If `det A = 1` and `(tr A)² > 4`, there is an
invertible `P` with `P A = diag(λ, μ) P`, where `λ, μ` are the two eigenvalues. -/
lemma exists_diagonalize {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    (hx : 4 < A.trace ^ 2) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * A = !![eigBig A.trace, 0; 0, eigSmall A.trace] * P := by
  have hA := eta_fin_two A
  rw [det_fin_two] at hdet
  have hsum : eigBig A.trace + eigSmall A.trace = A 0 0 + A 1 1 := by
    rw [eig_sum, trace_fin_two]
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize_aux (A 0 0) (A 0 1) (A 1 0) (A 1 1) _ _ hdet hsum
    (eig_prod hx) (eig_sub_pos hx).ne'
  exact ⟨P, hP, by rw [hA]; exact hPA⟩

/-- The Fricke polynomial in normal form: for `D = diag(l, m)` with `lm = 1` and
`C = [[a, b], [c, d]]` with `det C = 1`, `x² + y² + z² - xyz - 4 = -bc (l - m)²` where
`x = l + m`, `y = a + d`, `z = la + md`. -/
lemma fricke_normal {l m a b c d : ℝ} (hprod : l * m = 1) (hdet : a * d - b * c = 1) :
    (l + m) ^ 2 + (a + d) ^ 2 + (l * a + m * d) ^ 2 - (l + m) * (a + d) * (l * a + m * d) - 4 =
      -(b * c) * (l - m) ^ 2 := by
  linear_combination (4 - (a + d) ^ 2) * hprod - (l - m) ^ 2 * hdet

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.SL2R
