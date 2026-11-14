/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:258-436.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

variable {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) {l : R}

/-- The right-hand side of the ultrametric comparison at a finite place:
`2(max(0, log v(λ)) + max(0, −log v(λ)) + max(0, −log v(λ − 1)))`. -/
def legendreBound (l : R) : ℤ :=
  2 * (max 0 (log (v l)) + max 0 (-log (v l)) + max 0 (-log (v (l - 1))))

lemma legendreBound_nonneg (l : R) : 0 ≤ legendreBound v l := by
  unfold legendreBound
  have h1 := le_max_left 0 (log (v l))
  have h2 := le_max_left 0 (-log (v l))
  have h3 := le_max_left 0 (-log (v (l - 1)))
  omega

variable (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- `v(legendreJ λ) ≠ 0 ↔ v(λ² − λ + 1) ≠ 0`. -/
lemma valuation_legendreJ_ne_zero_iff [NeZero (2 : R)] :
    v (legendreJ l) ≠ 0 ↔ v (l ^ 2 - l + 1) ≠ 0 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow]
  rw [div_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by norm_num),
    pow_ne_zero_iff (by norm_num), pow_ne_zero_iff (by norm_num)]
  simp only [(Valuation.ne_zero_iff v).mpr h256, (Valuation.ne_zero_iff v).mpr hl0,
    (Valuation.ne_zero_iff v).mpr hl1', ne_eq, not_false_eq_true, true_and, and_true]

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendreJ [NeZero (2 : R)] (hc : v (l ^ 2 - l + 1) ≠ 0) :
    log (v (legendreJ l)) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  have h256 : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit hl0 hl1 in
/-- **The ultrametric case analysis** for `λ`, `λ − 1`, `λ² − λ + 1` at a finite place. -/
lemma legendre_valuation_cases :
    (v l < 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) < 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) ≤ 1) ∨
    (1 < v l ∧ v (l - 1) = v l ∧ v (l ^ 2 - l + 1) = v l ^ 2) := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
  · left
    have hb : v (l - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
    refine ⟨hlt, hb, ?_⟩
    have hlt' : v (l * (l - 1)) < v 1 := by
      rw [map_mul, hb, mul_one, map_one]
      exact hlt
    rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
  · have hb' : v (l - 1) ≤ 1 := by
      have := Valuation.map_sub v l 1
      rwa [heq, map_one, max_self] at this
    rcases hb'.lt_or_eq with hb | hb
    · right; left
      refine ⟨heq, hb, ?_⟩
      have hlt' : v (l * (l - 1)) < v 1 := by
        rw [map_mul, heq, one_mul, map_one]
        exact hb
      rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
    · right; right; left
      refine ⟨heq, hb, ?_⟩
      rw [e]
      refine (Valuation.map_add v _ _).trans (max_le ?_ (map_one v).le)
      rw [map_mul, heq, hb, mul_one]
  · right; right; right
    have hb : v (l - 1) = v l :=
      Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
    refine ⟨hgt, hb, ?_⟩
    have e' : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
    have hlt' : v (1 - l) < v (l ^ 2) := by
      rw [Valuation.map_sub_swap, hb, map_pow]
      exact lt_self_pow₀ hgt (by norm_num)
    rw [e', Valuation.map_add_eq_of_lt_left v hlt', map_pow]

/-- **The upper bound** `max(0, log v(j)) ≤ legendreBound` for `v(256) ≤ 1`. -/
lemma max_log_valuation_legendreJ_le [NeZero (2 : R)] (h256 : v 256 ≤ 1) :
    max 0 (log (v (legendreJ l))) ≤ legendreBound v l := by
  refine max_le (legendreBound_nonneg v l) ?_
  by_cases hj : v (legendreJ l) = 0
  · rw [hj, log_zero]
    exact legendreBound_nonneg v l
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  have h256' : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendreJ v hl0 hl1 hc]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    have := le_max_left 0 (log (v l))
    have := le_max_right 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    have := le_max_right 0 (-log (v (l - 1)))
    omega
  · have hS : log (v (l ^ 2 - l + 1)) ≤ 0 := by
      have := (log_le_log hc one_ne_zero).mpr hc'
      simpa using this
    rw [ha, hb, log_one]
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    have := le_max_right 0 (log (v l))
    have := le_max_left 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    push_cast
    omega

/-- **The lower bound** `legendreBound ≤ max(0, log v(j))` for `v(256) = 1` and `j ≠ 0`. -/
lemma legendreBound_le_max_log_valuation_legendreJ [NeZero (2 : R)] (h256 : v 256 = 1)
    (hj : v (legendreJ l) ≠ 0) :
    legendreBound v l ≤ max 0 (log (v (legendreJ l))) := by
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [log_valuation_legendreJ v hl0 hl1 hc, h256, log_one]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    omega
  · rw [ha, hb, log_one]
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    omega

end AbcAdaptation.Tripod
