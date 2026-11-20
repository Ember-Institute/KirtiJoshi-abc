/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Rational.lean
-/
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Solutions.Source_ReferenceIutCanLiftFrickeNormalForm

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (nA nB coe_nA coe_nB)

/-- A determinant-one real matrix proportional to a rational matrix. -/
def IsRatMul (g : SL(2, ℝ)) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∃ R : Matrix (Fin 2) (Fin 2) ℚ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ)

theorem isRatMul_one : IsRatMul 1 := ⟨1, one_ne_zero, 1, by ext i j; simp [one_apply]⟩

theorem IsRatMul.mul {g h : SL(2, ℝ)} (hg : IsRatMul g) (hh : IsRatMul h) :
    IsRatMul (g * h) := by
  obtain ⟨c, hc, R, hR⟩ := hg
  obtain ⟨d, hd, S, hS⟩ := hh
  refine ⟨c * d, mul_ne_zero hc hd, R * S, ?_⟩
  rw [coe_mul, hR, hS, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.map_mul (f := Rat.castHom ℝ)]

theorem IsRatMul.inv {g : SL(2, ℝ)} (hg : IsRatMul g) : IsRatMul g⁻¹ := by
  obtain ⟨c, hc, R, hR⟩ := hg
  refine ⟨c, hc, R.adjugate, ?_⟩
  rw [coe_inv, hR, adjugate_fin_two, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isRatMul_of_mem_closure {A B : SL(2, ℝ)} (hA : IsRatMul A) (hB : IsRatMul B)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B}) : IsRatMul γ := by
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hA
    · exact hB
  | one => exact isRatMul_one
  | mul g h _ _ hg hh => exact hg.mul hh
  | inv g _ hg => exact hg.inv

section NormalForm

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
  {X Y Z : ℚ} (hX : x ^ 2 = (X : ℝ)) (hY : y ^ 2 = (Y : ℝ)) (hZ : z ^ 2 = (Z : ℝ))

private theorem x_ne_zero_of_relation (hz : 0 < z)
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) : x ≠ 0 := by
  intro hx
  have hz₂ := sq_pos_of_ne_zero hz.ne'
  rw [hx] at hrel
  nlinarith only [hrel, sq_nonneg y, hz₂]

private theorem cast_sum_eq_product (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hX : x ^ 2 = (X : ℝ)) (hY : y ^ 2 = (Y : ℝ)) (hZ : z ^ 2 = (Z : ℝ)) :
    ((X + Y + Z : ℚ) : ℝ) = x * y * z := by
  push_cast
  rw [← hX, ← hY, ← hZ, hrel]

include hX hY hZ

/-- The first normal-form generator is a scalar multiple of a rational matrix. -/
theorem isRatMul_nA : IsRatMul (nA hz hrel) := by
  have hx := x_ne_zero_of_relation hz hrel
  let W : ℚ := X + Y + Z
  have hW : (W : ℝ) = x * y * z := cast_sum_eq_product hrel hX hY hZ
  refine ⟨x, hx, !![1 - W / (X * Z), 1 / Z; 1, W / (X * Z)], ?_⟩
  rw [coe_nA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← hX, ← hZ, hW] <;> field_simp [hx, hz.ne']

/-- The second normal-form generator is a scalar multiple of a rational matrix. -/
theorem isRatMul_nB : IsRatMul (nB hz hrel) := by
  have hx := x_ne_zero_of_relation hz hrel
  let W : ℚ := X + Y + Z
  have hW : (W : ℝ) = x * y * z := cast_sum_eq_product hrel hX hY hZ
  refine ⟨x * z, mul_ne_zero hx hz.ne',
    !![W / (X * Z) - 1 / Z, -(W / (X * Z ^ 2)); -(W / (X * Z)), 1 / Z], ?_⟩
  rw [coe_nB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← hX, ← hZ, hW] <;> field_simp [hx, hz.ne']

/-- Three rational squared traces give rational matrices up to scale throughout the
normal-form group. -/
theorem isRatMul_of_mem_normalForm {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) : IsRatMul γ :=
  isRatMul_of_mem_closure (isRatMul_nA hz hrel hX hY hZ) (isRatMul_nB hz hrel hX hY hZ) hγ

end NormalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
