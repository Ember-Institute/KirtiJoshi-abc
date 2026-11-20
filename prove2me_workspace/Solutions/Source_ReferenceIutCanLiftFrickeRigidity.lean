/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/FrickeRigidity.lean
-/
import Solutions.Source_ReferenceIutCanLiftFricke
import Solutions.Source_ReferenceIutCanLiftHyperbolicDiagonalization
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.SL2R

open Fricke (tr tr_commutator)

/-- The normal form of the second matrix: `[[a, 1], [ad - 1, d]]` with
`a = (z - μy)/(λ - μ)`, `d = (λy - z)/(λ - μ)`. -/
noncomputable def normalB (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (z - eigSmall x * y) / (eigBig x - eigSmall x)
  let d := (eigBig x * y - z) / (eigBig x - eigSmall x)
  !![a, 1; a * d - 1, d]

/-- **Normal form of an irreducible pair with hyperbolic first element.** -/
theorem exists_conj_normal {A B : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) :
    ∃ g : GL (Fin 2) ℝ,
      ((g * toGL A * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![eigBig (tr A), 0; 0, eigSmall (tr A)] ∧
      ((g * toGL B * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        normalB (tr A) (tr B) (tr (A * B)) := by
  set x := tr A with hxdef
  set l := eigBig x
  set m := eigSmall x
  have hprod : l * m = 1 := eig_prod hx
  have hlm : l - m ≠ 0 := (eig_sub_pos hx).ne'
  set D : Matrix (Fin 2) (Fin 2) ℝ := !![l, 0; 0, m] with hD
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize (A := (A : Matrix (Fin 2) (Fin 2) ℝ)) A.det_coe hx
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPPi : P * P⁻¹ = 1 := mul_nonsing_inv P hPu
  have hPiP : P⁻¹ * P = 1 := nonsing_inv_mul P hPu
  set C : Matrix (Fin 2) (Fin 2) ℝ := P * (B : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ with hC
  have hDA : P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ = D := by
    rw [hPA, mul_assoc, hPPi, mul_one]
  -- invariants of `C`
  have htrC : C.trace = tr B := by
    rw [hC, trace_mul_cycle, hPiP, one_mul]
  have htrDC : (D * C).trace = tr (A * B) := by
    rw [← hDA, hC, show P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ * (P * B * P⁻¹) =
      P * ((A : Matrix (Fin 2) (Fin 2) ℝ) * B) * P⁻¹ by
        simp only [mul_assoc]; rw [← mul_assoc P⁻¹ P, hPiP, one_mul],
      trace_mul_cycle, hPiP, one_mul]
    simp [tr]
  have hdetC : C.det = 1 := by
    rw [hC, det_mul, det_mul, B.det_coe, mul_one, ← det_mul, hPPi, det_one]
  set a := C 0 0
  set b := C 0 1
  set c := C 1 0
  set d := C 1 1
  have hCeta : C = !![a, b; c, d] := eta_fin_two C
  have hdet' : a * d - b * c = 1 := by rw [hCeta, det_fin_two_of] at hdetC; exact hdetC
  have hy : a + d = tr B := by rw [← htrC, hCeta, trace_fin_two_of]
  have hz : l * a + m * d = tr (A * B) := by
    rw [← htrDC, hCeta, hD]; simp [trace_fin_two]
  have hxlm : l + m = x := eig_sum
  -- `bc ≠ 0` by irreducibility
  have hbc : b * c ≠ 0 := by
    intro h0
    apply hc
    have hf := fricke_normal (b := b) (c := c) hprod hdet'
    rw [h0, hxlm, hy, hz] at hf
    rw [tr_commutator]
    linarith
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  -- rescale by `diag(b⁻¹, 1)`
  set Q : Matrix (Fin 2) (Fin 2) ℝ := !![b⁻¹, 0; 0, 1] with hQ
  have hQdet : Q.det ≠ 0 := by rw [hQ, det_fin_two_of]; simpa using hb
  set Qi : Matrix (Fin 2) (Fin 2) ℝ := !![b, 0; 0, 1] with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
  have hQinv : Q⁻¹ = Qi := inv_eq_right_inv hQQi
  let g : GL (Fin 2) ℝ := GeneralLinearGroup.mkOfDetNeZero (Q * P)
    (by rw [det_mul]; exact mul_ne_zero hQdet hP)
  have hgc : (g : Matrix (Fin 2) (Fin 2) ℝ) = Q * P := rfl
  have hginv : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = P⁻¹ * Qi := by
    rw [Matrix.coe_units_inv, hgc, Matrix.mul_inv_rev, hQinv]
  -- solve for `a`, `d`
  have ha : a = (tr (A * B) - m * tr B) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  have hd' : d = (l * tr B - tr (A * B)) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  refine ⟨g, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (A : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * (P * A * P⁻¹) * Qi by simp only [mul_assoc], hDA, hQ, hQi, hD]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply]
    field_simp
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (B : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * C * Qi by simp only [hC, mul_assoc], hCeta, hQ, hQi, normalB]
    rw [← ha, ← hd']
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
    · field_simp
    · linear_combination -hdet'

/-- **Fricke rigidity.** Two pairs in `SL(2, ℝ)` with the same trace triple, whose first element
is hyperbolic and which are irreducible (`tr [A, B] ≠ 2`), are simultaneously conjugate by an
element of `GL(2, ℝ)`. -/
theorem exists_conj_of_tr_eq {A B A' B' : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) (h1 : tr A = tr A') (h2 : tr B = tr B')
    (h3 : tr (A * B) = tr (A' * B')) :
    ∃ g : GL (Fin 2) ℝ, g * toGL A * g⁻¹ = toGL A' ∧ g * toGL B * g⁻¹ = toGL B' := by
  have hx' : 4 < tr A' ^ 2 := h1 ▸ hx
  have hc' : tr (A' * B' * A'⁻¹ * B'⁻¹) ≠ 2 := by
    rwa [tr_commutator, ← h1, ← h2, ← h3, ← tr_commutator]
  obtain ⟨g, hgA, hgB⟩ := exists_conj_normal hx hc
  obtain ⟨g', hgA', hgB'⟩ := exists_conj_normal hx' hc'
  refine ⟨g'⁻¹ * g, ?_, ?_⟩
  · have e : g * toGL A * g⁻¹ = g' * toGL A' * g'⁻¹ := by
      ext1; rw [hgA, hgA', h1]
    calc g'⁻¹ * g * toGL A * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL A * g⁻¹) * g' := by group
      _ = toGL A' := by rw [e]; group
  · have e : g * toGL B * g⁻¹ = g' * toGL B' * g'⁻¹ := by
      ext1; rw [hgB, hgB', h1, h2, h3]
    calc g'⁻¹ * g * toGL B * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL B * g⁻¹) * g' := by group
      _ = toGL B' := by rw [e]; group

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.SL2R
