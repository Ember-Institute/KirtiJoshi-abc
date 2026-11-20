/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Unipotent.lean
-/
import Mathlib.Algebra.Ring.GeomSum
import Solutions.Source_ReferenceIutCanLiftDenseUnipotents
import Solutions.Source_ReferenceIutCanLiftFrickeComplexAction

set_option autoImplicit false

/-!
# Rational unipotent rigidity

The only projective `m`-th root of the translation by two is the translation by `2 / m`.
An action on the projective line therefore agrees with the rational translations if its upper
unipotent with parameter two acts by translation by two.
-/

open OnePoint OnePoint.Proj
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

variable {k : Type*} [Field k] [DecidableEq k]

variable [CharZero k]

/-- **Möbius roots of a translation.** -/
theorem root_of_translation (g : GL (Fin 2) k) {m : ℕ} (hm : 0 < m)
    (h : ∀ y : OnePoint k, (fun z ↦ g • z)^[m] y = transl (2 : k) • y) (y : OnePoint k) :
    g • y = transl (2 / (m : k)) • y := by
  set f : OnePoint k → OnePoint k := fun z ↦ g • z
  -- `f` commutes with the translation, hence fixes `∞`
  have hT : ∀ z, transl (2 : k) • f z = f (transl (2 : k) • z) := by
    intro z
    rw [← h, ← h, ← Function.iterate_succ_apply' f m z, Function.iterate_succ_apply]
  have hfix : ∀ z : k, transl (2 : k) • (z : OnePoint k) ≠ z := by
    intro z hz
    rw [transl_smul_coe, OnePoint.coe_eq_coe] at hz
    have : (2 : k) = 0 := by linear_combination hz
    exact two_ne_zero this
  have hinf : f ∞ = ∞ := by
    have := hT ∞
    rw [transl_smul_infty] at this
    induction h' : f ∞ using OnePoint.rec with
    | infty => rfl
    | coe z => rw [h'] at this; exact absurd this (hfix z)
  have hg10 : g 1 0 = 0 := smul_infty_eq_self_iff.1 hinf
  have hg11 : g 1 1 ≠ 0 := by
    intro h0
    have := g.det_ne_zero
    rw [Matrix.det_fin_two, hg10, h0] at this
    simp at this
  set a := g 0 0 / g 1 1
  set b := g 0 1 / g 1 1
  have hf : ∀ z : k, f z = ((a * z + b : k) : OnePoint k) := by
    intro z
    simp only [f]
    rw [smul_some_eq_ite]
    simp only [hg10, zero_mul, zero_add, hg11, ↓reduceIte, a, b]
    congr 1
    field_simp
  -- iterates
  have hiter : ∀ n : ℕ, ∀ z : k, f^[n] z =
      ((a ^ n * z + b * ∑ i ∈ Finset.range n, a ^ i : k) : OnePoint k) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, hf, geom_sum_succ]
      congr 1
      ring
  have e0 := h ((0 : k) : OnePoint k)
  rw [hiter, transl_smul_coe, OnePoint.coe_eq_coe] at e0
  set S := ∑ i ∈ Finset.range m, a ^ i
  have ha : a = 1 := by
    by_contra ha
    set y₀ := b / (1 - a)
    have h1a : (1 : k) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    have hfix0 : f y₀ = y₀ := by
      rw [hf, OnePoint.coe_eq_coe]
      simp only [y₀]; field_simp; ring
    have hit : f^[m] y₀ = y₀ := Function.iterate_fixed hfix0 m
    rw [h] at hit
    exact hfix y₀ hit
  have hS : S = m := by simp [S, ha]
  have hb : b = 2 / m := by
    rw [hS] at e0
    have hm' : (m : k) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    field_simp
    linear_combination e0
  induction y using OnePoint.rec with
  | infty => rw [transl_smul_infty]; exact hinf
  | coe z => rw [show g • (z : OnePoint k) = f z from rfl, hf, transl_smul_coe, ha, hb, one_mul]

namespace UnipotentRigidity

open SL2R

private lemma uU_add (s t : ℝ) : uU (s + t) = uU s * uU t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma uU_zero : uU 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {Φ : SL(2, ℝ) → GL (Fin 2) k}
  (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint k, Φ (g * h) • y = Φ g • Φ h • y)
include hΦ

omit [CharZero k] in
lemma smul_one' (y : OnePoint k) : Φ 1 • y = y := by
  have := hΦ 1 1 y
  rw [mul_one] at this
  exact ((smul_left_cancel_iff (Φ 1)).1 this).symm

omit [CharZero k] in
lemma smul_pow (g : SL(2, ℝ)) (n : ℕ) (y : OnePoint k) :
    Φ (g ^ n) • y = (fun z ↦ Φ g • z)^[n] y := by
  induction n generalizing y with
  | zero => simp [smul_one' hΦ]
  | succ n ih => rw [pow_succ', hΦ, ih, Function.iterate_succ_apply']

omit [CharZero k] hΦ in
lemma transl_add (s t : k) (y : OnePoint k) : transl (s + t) • y = transl s • transl t • y := by
  induction y using OnePoint.rec with
  | infty => simp [transl_smul_infty]
  | coe z => simp only [transl_smul_coe]; congr 1; ring

omit [CharZero k] hΦ in
lemma uU_pow (t : ℝ) (n : ℕ) : uU t ^ n = uU (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uU_zero]
  | succ n ih => rw [pow_succ, ih, ← uU_add]; congr 1; push_cast; ring

/-- The property "`Φ(u_t)` is translation by `t`". -/
def IsTransl (Φ : SL(2, ℝ) → GL (Fin 2) k) (t : ℝ) (b : k) : Prop :=
  ∀ y : OnePoint k, Φ (uU t) • y = transl b • y

/-- **Unipotent rigidity.** If `Φ(u₂)` is translation by `2`, then `Φ(u_q)` is translation by `q`
for every rational `q`. -/
theorem smul_uU_rat (h2 : IsTransl Φ 2 2) (q : ℚ) : IsTransl Φ q q := by
  -- `1/d`
  have hd : ∀ d : ℕ, 0 < d → IsTransl Φ (1 / d) (1 / d) := by
    intro d hd0 y
    have hm : 0 < 2 * d := Nat.mul_pos (by decide) hd0
    have := root_of_translation (k := k) (Φ (uU (1 / d))) hm (fun z ↦ by
      rw [← smul_pow hΦ, uU_pow, ← h2 z]
      congr 3
      push_cast
      field_simp) y
    rw [this]
    congr 2
    push_cast
    field_simp
  -- additivity and negation
  have hadd : ∀ s t (b c : k), IsTransl Φ s b → IsTransl Φ t c → IsTransl Φ (s + t) (b + c) := by
    intro s t b c hs ht y
    rw [uU_add, hΦ, ht, hs, transl_add]
  have hneg : ∀ t (b : k), IsTransl Φ t b → IsTransl Φ (-t) (-b) := by
    intro t b ht y
    have e : ∀ z : OnePoint k, Φ (uU (-t)) • Φ (uU t) • z = z := by
      intro z
      rw [← hΦ, ← uU_add, neg_add_cancel, uU_zero, smul_one' hΦ]
    have := e (transl (-b) • y)
    rw [ht, ← transl_add, add_neg_cancel] at this
    rw [← this]
    congr 1
    induction y using OnePoint.rec with
    | infty => simp [transl_smul_infty]
    | coe z => simp [transl_smul_coe]
  have hnat : ∀ d : ℕ, 0 < d → ∀ n : ℕ, IsTransl Φ (n * (1 / d)) (n * (1 / d)) := by
    intro d hd0 n
    induction n with
    | zero =>
      intro y
      simp only [Nat.cast_zero, zero_mul]
      rw [uU_zero, smul_one' hΦ]
      induction y using OnePoint.rec with
      | infty => simp [transl_smul_infty]
      | coe z => simp [transl_smul_coe]
    | succ n ih =>
      have := hadd _ _ _ _ ih (hd d hd0)
      convert this using 2 <;> push_cast <;> ring
  have hint : ∀ n : ℤ, IsTransl Φ (n * (1 / q.den)) (n * (1 / q.den)) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · exact_mod_cast hnat q.den q.den_pos m
    · have := hneg _ _ (hnat q.den q.den_pos m)
      convert this using 2 <;> push_cast <;> ring
  have := hint q.num
  convert this using 2
  · rw [Rat.cast_def]; ring
  · rw [Rat.cast_def]; ring

end UnipotentRigidity


end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
