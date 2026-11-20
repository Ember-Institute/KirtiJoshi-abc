/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/OneInftyLattice.lean
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Solutions.Source_ReferenceIutCanLiftNielsenDescent
import Solutions.Source_ReferenceIutCanLiftTakeuchiFourGroups

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

open Takeuchi (Realizes exists_sign_normalize)

section Matrices

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The first matrix of the punctured-torus Fricke normal form. -/
noncomputable def nA : SL(2, ℝ) :=
  ⟨!![x - y / z, x / z ^ 2; x, y / z], by
    rw [det_fin_two_of]
    field_simp [hz.ne']
    linear_combination -hrel⟩

/-- The second matrix of the punctured-torus Fricke normal form. -/
noncomputable def nB : SL(2, ℝ) :=
  ⟨!![y - x / z, -y / z ^ 2; -y, x / z], by
    rw [det_fin_two_of]
    field_simp [hz.ne']
    linear_combination -hrel⟩

theorem coe_nA : (nA hz hrel : Matrix (Fin 2) (Fin 2) ℝ) =
    !![x - y / z, x / z ^ 2; x, y / z] := rfl

theorem coe_nB : (nB hz hrel : Matrix (Fin 2) (Fin 2) ℝ) =
    !![y - x / z, -y / z ^ 2; -y, x / z] := rfl

theorem coe_nAnB : ((nA hz hrel * nB hz hrel : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) = !![z, -1 / z; z, 0] := by
  rw [coe_mul, coe_nA, coe_nB, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hz.ne']
  · linear_combination (-z) * hrel
  · linear_combination hrel
  · linear_combination -hrel
  · ring

private theorem coe_nBnA : ((nB hz hrel * nA hz hrel : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) = !![z, 1 / z; -z, 0] := by
  rw [coe_mul, coe_nB, coe_nA, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hz.ne']
  · linear_combination (-z) * hrel
  · linear_combination -hrel
  · linear_combination hrel
  · ring

theorem tr_nA : tr (nA hz hrel) = x := by
  simp [tr, coe_nA, trace_fin_two_of]

theorem tr_nB : tr (nB hz hrel) = y := by
  simp [tr, coe_nB, trace_fin_two_of]

theorem tr_nAnB : tr (nA hz hrel * nB hz hrel) = z := by
  rw [tr, coe_nAnB, trace_fin_two_of, add_zero]

/-- The commutator of the normal-form matrices acts by translation by two. -/
theorem coe_commutator_n : ((nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ *
    (nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -2; 0, -1] := by
  rw [show nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹ =
    (nA hz hrel * nB hz hrel) * (nB hz hrel * nA hz hrel)⁻¹ by group,
    coe_mul, coe_nAnB, coe_inv, coe_nBnA, adjugate_fin_two]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hz.ne']
  all_goals ring

end Matrices

private theorem trace_product_pos {x y z : ℝ}
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : x ≠ 0) :
    0 < x * y * z := by
  rw [← hrel]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)) (sq_nonneg z)

private theorem two_lt_abs_of_relation {x y z : ℝ}
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : x ≠ 0) :
    2 < |x| := by
  by_contra! h
  have hproduct : x * y * z ≤ |x| * (|y| * |z|) := by
    simpa only [abs_mul, mul_assoc] using le_abs_self (x * y * z)
  have hmul := mul_le_mul_of_nonneg_right h (mul_nonneg (abs_nonneg y) (abs_nonneg z))
  have hsum : 2 * (|y| * |z|) ≤ y ^ 2 + z ^ 2 := by
    nlinarith only [sq_nonneg (|y| - |z|), sq_abs y, sq_abs z]
  linarith only [hrel, hproduct.trans (hmul.trans hsum), sq_pos_of_ne_zero hx]

private theorem descent_step_bound {x y z : ℝ} (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hx : 2 < |x|) (hy : 2 < |y|) (htri : |x| + |y| ≤ |z|) :
    |x * y - z| + 2 ≤ |z| := by
  have hz : 0 < |z| := by linarith
  have hVieta : |x * y - z| * |z| = |x| ^ 2 + |y| ^ 2 := by
    rw [← abs_mul, sq_abs, sq_abs]
    rw [show (x * y - z) * z = x ^ 2 + y ^ 2 by linear_combination -hrel,
      abs_of_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y))]
  have hab : |x| ^ 2 + |y| ^ 2 ≤ (|x| + |y| - 2) * (|x| + |y|) := by
    nlinarith only [hx, hy, mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hy.le)]
  have h₁ := mul_le_mul_of_nonneg_left htri (show 0 ≤ |x| + |y| - 2 by linarith)
  have h₂ := mul_le_mul_of_nonneg_right (sub_le_sub_right htri 2) hz.le
  have hbound : |x * y - z| ≤ |z| - 2 := by
    apply (mul_le_mul_iff_of_pos_right hz).mp
    rw [hVieta]
    exact hab.trans (h₁.trans h₂)
  linarith

/-- Nielsen moves reach the strict triangle inequalities for the absolute traces. -/
theorem exists_triangle {Γ : Subgroup SL(2, ℝ)} (N : ℕ) :
    ∀ x y z : ℝ, Realizes Γ x y z → x ^ 2 + y ^ 2 + z ^ 2 = x * y * z → x ≠ 0 →
      |x| + |y| + |z| ≤ 2 * N →
      ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧ x' ≠ 0 ∧
        |x'| < |y'| + |z'| ∧ |y'| < |x'| + |z'| ∧ |z'| < |x'| + |y'| := by
  induction N with
  | zero =>
    intro x y z _ _ hx hsum
    simp only [Nat.cast_zero, mul_zero] at hsum
    linarith only [hsum, abs_pos.mpr hx, abs_nonneg y, abs_nonneg z]
  | succ N ih =>
    intro x y z hreal hrel hx hsum
    obtain ⟨hxy, hz⟩ := mul_ne_zero_iff.mp (ne_of_gt (trace_product_pos hrel hx))
    have hy := (mul_ne_zero_iff.mp hxy).2
    have hrely : y ^ 2 + z ^ 2 + x ^ 2 = y * z * x := by linear_combination hrel
    have hrelz : z ^ 2 + x ^ 2 + y ^ 2 = z * x * y := by linear_combination hrel
    have hx₂ := two_lt_abs_of_relation hrel hx
    have hy₂ := two_lt_abs_of_relation hrely hy
    have hz₂ := two_lt_abs_of_relation hrelz hz
    push_cast at hsum
    by_cases tx : |x| < |y| + |z|
    · by_cases ty : |y| < |x| + |z|
      · by_cases tz : |z| < |x| + |y|
        · exact ⟨x, y, z, hreal, hrel, hx, tx, ty, tz⟩
        · have hstep := descent_step_bound hrel hx₂ hy₂ (le_of_not_gt tz)
          exact ih x y (x * y - z) hreal.flip (by linear_combination hrel) hx (by linarith)
      · have ty' : |z| + |x| ≤ |y| := by simpa only [add_comm] using le_of_not_gt ty
        have hstep := descent_step_bound hrelz hz₂ hx₂ ty'
        exact ih z x (z * x - y) hreal.cycle.cycle.flip
          (by linear_combination hrelz) hz (by linarith)
    · have hstep := descent_step_bound hrely hy₂ hz₂ (le_of_not_gt tx)
      exact ih y z (y * z - x) hreal.cycle.flip (by linear_combination hrely) hy (by linarith)

/-- A punctured-torus pair reaches the Fricke normal form by Nielsen moves, generator
sign changes, and simultaneous real conjugation. -/
theorem exists_normal_form {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) :
    ∃ (x y z : ℝ) (_ : 0 < x) (_ : 0 < y) (hz : 0 < z)
      (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z),
      (x < y + z ∧ y < x + z ∧ z < x + y) ∧
      ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
        ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
          ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (nA hz hrel) ∧
            g * toGL B'' * g⁻¹ = toGL (nB hz hrel) := by
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hreal : Realizes (Subgroup.closure {A, B}) (tr A) (tr B) (tr (A * B)) :=
    ⟨A, B, rfl, rfl, rfl, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ((|tr A| + |tr B| + |tr (A * B)|) / 2)
  obtain ⟨_, _, _, ⟨A', B', hcl, rfl, rfl, rfl⟩, hrel', hx, tx, ty, tz⟩ :=
    exists_triangle N _ _ _ hreal hrel hA (by linarith)
  have hpos := trace_product_pos hrel' hx
  obtain ⟨hxy, hz⟩ := mul_ne_zero_iff.mp (ne_of_gt hpos)
  have hy := (mul_ne_zero_iff.mp hxy).2
  obtain ⟨A'', hA'', B'', hB'', e1, e2, e3, e4⟩ := exists_sign_normalize hpos
  have hz₀ := abs_pos.mpr hz
  have hrelAbs : |tr A'| ^ 2 + |tr B'| ^ 2 + |tr (A' * B')| ^ 2 =
      |tr A'| * |tr B'| * |tr (A' * B')| := by
    simp only [sq_abs]
    rw [← abs_mul, ← abs_mul, abs_of_pos hpos]
    exact hrel'
  have hx₄ : 4 < tr A'' ^ 2 := by
    have h := sq_lt_sq.mpr (show |(2 : ℝ)| < |tr A'| by
      rw [abs_of_nonneg (by norm_num)]
      exact two_lt_abs_of_relation hrel' hx)
    rw [e1, sq_abs]
    norm_num at h
    exact h
  have hc : tr (A'' * B'' * A''⁻¹ * B''⁻¹) ≠ 2 := by
    rw [e4, (tr_commutator_eq_neg_two_iff A' B').mpr hrel']
    norm_num
  obtain ⟨g, hgA, hgB⟩ := SL2R.exists_conj_of_tr_eq
    (A' := nA hz₀ hrelAbs) (B' := nB hz₀ hrelAbs)
    hx₄ hc (by rw [e1, tr_nA]) (by rw [e2, tr_nB]) (by rw [e3, tr_nAnB])
  exact ⟨_, _, _, abs_pos.mpr hx, abs_pos.mpr hy, hz₀, hrelAbs, ⟨tx, ty, tz⟩,
    A', B', hcl, A'', hA'', B'', hB'', g, hgA, hgB⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
