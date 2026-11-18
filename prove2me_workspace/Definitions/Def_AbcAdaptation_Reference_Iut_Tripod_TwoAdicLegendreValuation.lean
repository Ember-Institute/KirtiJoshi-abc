/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.Linarith

namespace AbcAdaptation.Tripod

open WithZero WeierstrassCurve
open scoped WithZero

section
variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendre l).IsElliptic]

lemma valuation_legendre_ne_zero (hj : v (legendre l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  rw [legendre_j, map_div₀, map_mul, map_pow] at hj
  have hnum := (div_ne_zero_iff.mp hj).1
  exact ⟨(mul_ne_zero_iff.mp hnum).1,
    (pow_ne_zero_iff (by norm_num)).mp (mul_ne_zero_iff.mp hnum).2,
    (Valuation.ne_zero_iff v).mpr hl0, (Valuation.ne_zero_iff v).mpr hl1⟩

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendre_j (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  rw [legendre_j, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (2 : K)] [(legendre l).IsElliptic] in
/-- `log v(λ² − λ + 1) ≤ log v(λ) + log v(λ − 1)` or `≤ 0` (ultrametric inequality for
`λ² − λ + 1 = λ(λ − 1) + 1`). -/
lemma log_valuation_sq_sub_add_one_le (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0)
    (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨ log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have h : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [h] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with h1 | h1
  · left
    rw [map_mul] at h1
    rw [← log_mul hl hl1]
    exact (log_le_log hc (mul_ne_zero hl hl1)).mpr h1
  · right
    rw [map_one] at h1
    have := (log_le_log hc one_ne_zero).mpr h1
    simpa using this

/-- **The bound on `log v(j(E_λ))`**: if `v(256) ≤ 1` then
`log v(j) ≤ 2|log v(λ)| + 2|log v(λ − 1)|`. -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1) (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendre_j v hj]
  have ha := le_abs_self (log (v l))
  have ha' := neg_abs_le (log (v l))
  have hb := le_abs_self (log (v (l - 1)))
  have hb' := neg_abs_le (log (v (l - 1)))
  have ha0 := abs_nonneg (log (v l))
  have hb0 := abs_nonneg (log (v (l - 1)))
  rcases log_valuation_sq_sub_add_one_le v hc hvl hvl1 with h | h
  · linarith
  · linarith

end

end AbcAdaptation.Tripod
