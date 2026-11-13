/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

The normal-form lemma and the arithmetic proof below are adapted from
refer/iut/Iut/Tripod/ClassicalAbc.lean, especially `exists_normal_form` and
`classicalABCInt_of_statementI`. No Iut import is used.
-/
import Definitions.Def_AbcClassicalInt
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A rational height adapter for classical ABC

`RationalABCHeight` uses Mathlib's actual logarithmic height on `ℚ` and the
integer radical of the reduced numerator, numerator minus denominator, and
denominator. Its constant is uniform in the rational point.

This is the local rational consequence required from the concrete tripod
`StatementI`. The geometric projection remains to be supplied: it must prove
this exact rational inequality, including the conductor bound by the logarithm
of this integer radical. This file asserts no equivalence with an arbitrary
height theory and makes no replacement height or volume assignments.
-/

set_option autoImplicit false

open UniqueFactorizationMonoid

namespace AbcAdaptation

/-- The uniform rational height inequality with the concrete integer radical. -/
def RationalABCHeight : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℚ, q ≠ 0 → q ≠ 1 →
    Height.logHeight₁ q ≤
      (1 + ε) * Real.log
        ((radical (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ) + C

/-- Normalize a coprime integer ABC triple to a reduced fraction with positive
denominator. The product has the same absolute value as the original product. -/
private lemma exists_normal_form {a b c : ℤ} (hc : c ≠ 0) (hab : IsCoprime a b)
    (habc : a + b + c = 0) :
    ∃ n d : ℤ, 0 < d ∧ |n| = |a| ∧ d = |c| ∧ |n - d| = |b| ∧
      (n * (n - d) * d).natAbs = (a * b * c).natAbs ∧ IsCoprime n d := by
  have hac : IsCoprime a c := by
    have := hab.neg_right.add_mul_left_right (-1)
    rwa [show -b + a * -1 = c by omega] at this
  rcases hc.lt_or_gt with hc | hc
  · refine ⟨a, -c, by omega, rfl, (abs_of_neg hc).symm, ?_, ?_, hac.neg_right⟩
    · rw [show a - -c = -b by omega, abs_neg]
    · rw [show a * (a - -c) * -c = a * b * c by
        rw [show a - -c = -b by omega]; ring]
  · refine ⟨-a, c, hc, abs_neg a, (abs_of_pos hc).symm, ?_, ?_, hac.neg_left⟩
    · rw [show -a - c = b by omega]
    · rw [show -a - c = b by omega,
        show -a * b * c = -(a * b * c) by ring, Int.natAbs_neg]

/-- The concrete rational height inequality implies the symmetric integer ABC
inequality. The multiplicative constant is `2 * exp C`. -/
theorem classicalABCInt_of_rationalABCHeight (h : RationalABCHeight) : ClassicalABCInt := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨2 * Real.exp C, fun a b c ha hb hc hab habc => ?_⟩
  obtain ⟨n, d, hd, hna, hdc, hndb, hprod, hcop⟩ := exists_normal_form hc hab habc
  have hn : n ≠ 0 := by
    intro h
    rw [h, abs_zero] at hna
    exact ha (abs_eq_zero.mp hna.symm)
  have hnd : n - d ≠ 0 := by
    intro h
    rw [h, abs_zero] at hndb
    exact hb (abs_eq_zero.mp hndb.symm)
  set q : ℚ := n / d with hqdef
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h0 : q ≠ 0 := div_ne_zero (by exact_mod_cast hn) hdQ
  have h1 : q ≠ 1 := by
    intro h
    rw [hqdef, div_eq_one_iff_eq hdQ] at h
    exact hnd (by exact_mod_cast sub_eq_zero.mpr h)
  have hcop' : Nat.Coprime n.natAbs d.natAbs :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hnum : q.num = n := Rat.num_div_eq_of_coprime hd hcop'
  have hden : (q.den : ℤ) = d := Rat.den_div_eq_of_coprime hd hcop'

  -- Pass through the natural radical only to use the product's `natAbs` identity.
  set R : ℕ := radical (a * b * c).natAbs with hR
  have hqrad :
      ((radical (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ) = R := by
    rw [hnum, hden, ← Int.radical_natAbs_eq_radical, hprod, Int.cast_natCast]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.radical_pos _
  have hlog := hC q h0 h1
  rw [hqrad, Rat.logHeight₁_eq_log_max, hnum] at hlog

  have hM : ((max n.natAbs q.den : ℕ) : ℝ) = max |(a : ℝ)| |(c : ℝ)| := by
    have hden' : (q.den : ℝ) = |(c : ℝ)| := by
      rw [← Int.cast_abs, ← hdc, ← hden, Int.cast_natCast]
    rw [Nat.cast_max, hden', Nat.cast_natAbs, Int.cast_abs,
      ← Int.cast_abs, hna, Int.cast_abs]
  rw [hM] at hlog
  have hMpos : 0 < max |(a : ℝ)| |(c : ℝ)| :=
    lt_max_of_lt_left (abs_pos.mpr (by exact_mod_cast ha))
  have hMle : max |(a : ℝ)| |(c : ℝ)| ≤ Real.exp C * (R : ℝ) ^ (1 + ε) := by
    rw [← Real.exp_log hMpos, Real.rpow_def_of_pos hRpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

  have hb' : |(b : ℝ)| ≤ |(a : ℝ)| + |(c : ℝ)| := by
    rw [show (b : ℝ) = -(a + c) by
      have : (a : ℝ) + b + c = 0 := by exact_mod_cast habc
      linarith, abs_neg]
    exact abs_add_le _ _
  have hrad : ((radical (a * b * c) : ℤ) : ℝ) = R := by
    rw [hR, ← Int.radical_natAbs_eq_radical, Int.cast_natCast]
  rw [hrad]
  push_cast
  have hE : 0 ≤ Real.exp C * (R : ℝ) ^ (1 + ε) := by positivity
  have ha' := le_max_left |(a : ℝ)| |(c : ℝ)|
  have hc' := le_max_right |(a : ℝ)| |(c : ℝ)|
  refine max_le (by nlinarith) (max_le (by nlinarith) (by nlinarith))

end AbcAdaptation
