/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Adapted from OrbicurveCores/Markov.lean, lines 36–95, and
OrbicurveCores/Takeuchi.lean, lines 49–52 and 108–130.
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- The four sorted triples of integral squared traces in Takeuchi's classification. -/
def IsTakeuchiTriple (X Y Z : ℤ) : Prop :=
  (X = 9 ∧ Y = 9 ∧ Z = 9) ∨ (X = 8 ∧ Y = 8 ∧ Z = 16) ∨ (X = 5 ∧ Y = 20 ∧ Z = 25) ∨
    (X = 6 ∧ Y = 12 ∧ Z = 18)

private theorem search : ∀ i : Fin 5, ∀ j : Fin 17, ∀ k : Fin 26,
    let X := (i : ℕ) + 5
    let Y := (j : ℕ) + 5
    let Z := (k : ℕ) + 5
    X ≤ Y → Y ≤ Z → 2 * (X + Y + Z) ≤ X * Y → (X + Y + Z) ^ 2 = X * Y * Z →
    (X = 9 ∧ Y = 9 ∧ Z = 9) ∨ (X = 8 ∧ Y = 8 ∧ Z = 16) ∨ (X = 5 ∧ Y = 20 ∧ Z = 25) ∨
      (X = 6 ∧ Y = 12 ∧ Z = 18) := by
  decide +kernel

/-- A positive sorted squared-trace triple is one of Takeuchi's four triples if the Vieta
move in the largest coordinate cannot decrease that coordinate. -/
theorem reduced_classification {X Y Z : ℤ} (hX : 0 < X) (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    (hrel : (X + Y + Z) ^ 2 = X * Y * Z) (hred : 2 * (X + Y + Z) ≤ X * Y) :
    IsTakeuchiTriple X Y Z := by
  have hY : 0 < Y := hX.trans_le hXY
  have hZ : 0 < Z := hY.trans_le hYZ
  -- The other root of the quadratic in Z is at least Z.
  have hroot : Z * (X * Y - 2 * (X + Y) - Z) = (X + Y) ^ 2 := by linear_combination -hrel
  have hZZ' : Z ≤ X * Y - 2 * (X + Y) - Z := by omega
  have hZle : Z ≤ X + Y := by
    have hsq := mul_le_mul_of_nonneg_left hZZ' hZ.le
    rw [hroot] at hsq
    by_contra! h
    have hlt := mul_self_lt_mul_self (show 0 ≤ X + Y by omega) h
    rw [pow_two] at hsq
    exact hlt.not_ge hsq
  have hX5 : 5 ≤ X := by
    by_contra! h
    have hXYZ := mul_nonneg (show 0 ≤ 4 - X by omega) (mul_nonneg hY.le hZ.le)
    have hpos := mul_pos hX (show 0 < X + 2 * Y + 2 * Z by omega)
    nlinarith only [hrel, hXYZ, hpos, sq_nonneg (Y - Z)]
  -- Evaluating the quadratic at Y gives a nonnegative value.
  have hpY : 0 ≤ (Y - Z) * (Y - (X * Y - 2 * (X + Y) - Z)) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hYZ) (sub_nonpos.mpr (hYZ.trans hZZ'))
  have hpY' : Y ^ 2 * (X - 4) ≤ 4 * X * Y + X ^ 2 := by
    nlinarith only [hroot, hpY]
  have hX9 : X ≤ 9 := by
    by_contra! h
    have h1 := mul_pos (sub_pos.mpr h) (mul_pos hY hY)
    have h2 := mul_nonneg (sub_nonneg.mpr hXY) (show 0 ≤ 5 * Y + X by omega)
    nlinarith only [hpY', h1, h2]
  have hY21 : Y ≤ 21 := by
    by_contra! h
    have hY22 : 22 ≤ Y := by omega
    have hquad : 0 ≤ Y ^ 2 - 4 * Y - X - 5 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hY22) (show 0 ≤ Y + 18 by omega)
      nlinarith only [hX9, hprod]
    have hdifference := mul_nonneg (sub_nonneg.mpr hX5) hquad
    have hbase := mul_nonneg (sub_nonneg.mpr hY22) (show 0 ≤ Y + 2 by omega)
    nlinarith only [hpY', hdifference, hbase]
  have hZ30 : Z ≤ 30 := by omega
  lift X to ℕ using hX.le
  lift Y to ℕ using hY.le
  lift Z to ℕ using hZ.le
  let i : Fin 5 := ⟨X - 5, by omega⟩
  let j : Fin 17 := ⟨Y - 5, by omega⟩
  let k : Fin 26 := ⟨Z - 5, by omega⟩
  have hi : (i : ℕ) + 5 = X := by dsimp [i]; omega
  have hj : (j : ℕ) + 5 = Y := by dsimp [j]; omega
  have hk : (k : ℕ) + 5 = Z := by dsimp [k]; omega
  have hcases := search i j k
  dsimp only at hcases
  rw [hi, hj, hk] at hcases
  obtain h | h | h | h := hcases (by exact_mod_cast hXY) (by exact_mod_cast hYZ)
    (by exact_mod_cast hred) (by exact_mod_cast hrel) <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;> norm_num [IsTakeuchiTriple]

/-- The four Takeuchi triples expressed in terms of real traces. -/
def TakeuchiSq (x y z : ℝ) : Prop :=
  (x ^ 2 = 9 ∧ y ^ 2 = 9 ∧ z ^ 2 = 9) ∨ (x ^ 2 = 8 ∧ y ^ 2 = 8 ∧ z ^ 2 = 16) ∨
    (x ^ 2 = 5 ∧ y ^ 2 = 20 ∧ z ^ 2 = 25) ∨ (x ^ 2 = 6 ∧ y ^ 2 = 12 ∧ z ^ 2 = 18)

/-- The reduced case of Nielsen descent for a real trace triple with integral squares. -/
theorem takeuchiSq_of_sorted {a b c : ℝ} {X Y Z : ℤ} (ha : a ^ 2 = X) (hb : b ^ 2 = Y)
    (hc : c ^ 2 = Z) (hrel : a ^ 2 + b ^ 2 + c ^ 2 = a * b * c) (hpos : 0 < a ^ 2)
    (hab : a ^ 2 ≤ b ^ 2) (hbc : b ^ 2 ≤ c ^ 2) (hred : 2 * (a * b * c) ≤ a ^ 2 * b ^ 2) :
    TakeuchiSq a b c := by
  have hX : (0 : ℝ) < X := ha ▸ hpos
  have hXY : (X : ℝ) ≤ Y := ha ▸ hb ▸ hab
  have hYZ : (Y : ℝ) ≤ Z := hb ▸ hc ▸ hbc
  have hrel' : ((X + Y + Z : ℤ) : ℝ) ^ 2 = ((X * Y * Z : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hb, ← hc, hrel]
    simp only [mul_pow]
  have hred' : ((2 * (X + Y + Z) : ℤ) : ℝ) ≤ ((X * Y : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hb, ← hc, hrel]
    exact hred
  have hcases := reduced_classification (by exact_mod_cast hX) (by exact_mod_cast hXY)
    (by exact_mod_cast hYZ) (by exact_mod_cast hrel') (by exact_mod_cast hred')
  unfold IsTakeuchiTriple at hcases
  unfold TakeuchiSq
  rw [ha, hb, hc]
  obtain h | h | h | h := hcases <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> norm_num

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
