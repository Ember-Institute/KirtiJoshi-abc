/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

The ClassicalABC definition is adapted from refer/iut/Iut/Abc/Classical.lean.
The adaptation lemmas below are local to this project. No Iut import is used.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false

open UniqueFactorizationMonoid

namespace AbcAdaptation

def ClassicalABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ,
    0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

def PlatformABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ,
    0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
        (c : ℝ) < K * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

theorem coprime_of_pairwise_sum {a b c : ℕ} (hb : 0 < b)
    (hp : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime) (hadd : a + b = c) :
    Nat.Coprime a b := by
  have hac : a ≠ c := by
    intro h
    have hzero : a + b = a + 0 := by simpa only [Nat.add_zero] using hadd.trans h.symm
    exact (Nat.ne_of_gt hb) (Nat.add_left_cancel hzero)
  have h : Nat.Coprime a c := hp (by simp) (by simp) hac
  simpa only [← hadd, Nat.coprime_self_add_right] using h

theorem pairwise_of_coprime_sum {a b c : ℕ} (hab : Nat.Coprime a b)
    (hadd : a + b = c) : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime := by
  have hac : Nat.Coprime a c := by
    rw [← hadd]
    exact Nat.coprime_self_add_right.mpr hab
  have hbc : Nat.Coprime b c := by
    rw [← hadd]
    exact Nat.coprime_add_self_right.mpr hab.symm
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact False.elim (hxy rfl)
    | exact hab
    | exact hab.symm
    | exact hac
    | exact hac.symm
    | exact hbc
    | exact hbc.symm

theorem platformABC_of_classicalABC (h : ClassicalABC) : PlatformABC := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C + 1, ?_⟩
  intro a b c ha hb _hc hp hadd
  have hrad : (0 : ℝ) < ((radical (a * b * c) : ℕ) : ℝ) := by
    exact_mod_cast Nat.radical_pos (a * b * c)
  have hr := Real.rpow_pos_of_pos hrad (1 + ε)
  exact lt_of_le_of_lt (hC a b c ha hb (coprime_of_pairwise_sum hb hp hadd) hadd)
    (mul_lt_mul_of_pos_right (lt_add_one C) hr)

theorem classicalABC_of_platformABC (h : PlatformABC) : ClassicalABC := by
  intro ε hε
  obtain ⟨K, hK⟩ := h ε hε
  refine ⟨K, ?_⟩
  intro a b c ha hb hab hadd
  have hc : 0 < c := by
    rw [← hadd]
    exact lt_of_lt_of_le ha (Nat.le_add_right a b)
  exact (hK a b c ha hb hc (pairwise_of_coprime_sum hab hadd) hadd).le

theorem platformABC_iff_classicalABC : PlatformABC ↔ ClassicalABC :=
  ⟨classicalABC_of_platformABC, platformABC_of_classicalABC⟩

theorem platform_constant_pos {ε K : ℝ}
    (hK : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
        (c : ℝ) < K * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)) : 0 < K := by
  have hp := pairwise_of_coprime_sum (a := 1) (b := 1) (c := 2) (by decide) rfl
  have hbound := hK 1 1 2 (by decide) (by decide) (by decide) hp rfl
  have hrad : (0 : ℝ) < ((radical ((1 : ℕ) * 1 * 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.radical_pos ((1 : ℕ) * 1 * 2)
  have hr := Real.rpow_pos_of_pos hrad (1 + ε)
  have hzero : (0 : ℝ) < (2 : ℕ) := by exact_mod_cast (show 0 < (2 : ℕ) by decide)
  by_contra hnot
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hr.le))
    (hzero.trans hbound)

end AbcAdaptation
