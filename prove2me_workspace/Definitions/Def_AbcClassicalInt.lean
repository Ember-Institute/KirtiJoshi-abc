/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcClassical
import Mathlib.Tactic.Ring

set_option autoImplicit false
open UniqueFactorizationMonoid
namespace AbcAdaptation

def ClassicalABCInt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → IsCoprime a b →
    a + b + c = 0 →
      ((max |a| (max |b| |c|) : ℤ) : ℝ) ≤ C * ((radical (a * b * c) : ℤ) : ℝ) ^ (1 + ε)

/-- The form over `ℤ` implies the form over `ℕ` (apply it to `(a, b, −c)`). -/
theorem classicalABC_of_int (h : ClassicalABCInt) : ClassicalABC := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun a b c ha hb hab habc => ?_⟩
  have key := hC a b (-c) (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by rw [neg_ne_zero]; exact_mod_cast (show 0 < c by omega).ne')
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hab))
    (by rw [← habc]; push_cast; ring)
  have hmax : (max |(a : ℤ)| (max |(b : ℤ)| |-(c : ℤ)|)) = c := by
    rw [abs_neg]
    simp only [Nat.abs_cast]
    omega
  have hrad : (radical ((a : ℤ) * b * -(c : ℤ)) : ℤ) = (radical (a * b * c) : ℕ) := by
    rw [← Int.radical_natAbs_eq_radical]
    congr 2
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_neg]
    simp
  rw [hmax, hrad] at key
  exact_mod_cast key


end AbcAdaptation
