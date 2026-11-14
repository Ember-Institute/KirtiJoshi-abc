import Lean
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-!
The two private helpers and the numeric proof below are copied from
`refer/iut/Iut/Implication/Corollary22.lean`, source declarations
`Iut.log_le_four_mul_sqrt_sqrt`, `Iut.log_le_self_of_pos`, and `Iut.epsilonE_le`.
Source SHA256: ffec17b8d1552155acca3886ee0b73ab9c410916e5128370186978b6d34d2d15.
The historical upstream Git revision is unverified in the local source archive.
-/

/-- `log h ≤ 4·√√h` for `h ≥ 1`. -/
private lemma log_le_four_mul_sqrt_sqrt {h : ℝ} (hh : 1 ≤ h) :
    Real.log h ≤ 4 * Real.sqrt (Real.sqrt h) := by
  set s := Real.sqrt (Real.sqrt h) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = Real.sqrt h := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs4 : s * s * (s * s) = h := by rw [hs2]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  have hlog : Real.log h = 4 * Real.log s := by
    rw [← hs4, show s * s * (s * s) = s ^ 4 by ring, Real.log_pow]; push_cast; ring
  rw [hlog]
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < s)
  linarith

/-- `log y ≤ y` for `y > 0`. -/
private lemma log_le_self_of_pos {y : ℝ} (hy : 0 < y) : Real.log y ≤ y := by
  linarith [Real.log_le_sub_one_of_pos hy]

end AbcAdaptation.Tripod

open AbcAdaptation.Tripod

theorem solution :
    AbcAdaptation.Tripod.EpsilonELargeHeight := by
  intro δ h ε hδ hε hh hh1
  set s := Real.sqrt (Real.sqrt h) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = Real.sqrt h := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs4 : s * s * (s * s) = h := by rw [hs2]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  set M := (60 * δ) ^ 2 * (2 * δ + 4) / ε with hM
  have hM0 : 0 ≤ M := by positivity
  have hsM : M ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < M ^ 4 := by
      apply pow_lt_pow_left₀ hlt hs0 (by norm_num)
    have : s ^ 4 = h := by rw [← hs4]; ring
    linarith
  -- `log(2δh) ≤ 2δ + 4s`
  have hlog : Real.log (2 * δ * h) ≤ 2 * δ + 4 * s := by
    rw [Real.log_mul (by positivity) (by linarith)]
    have h1 := log_le_self_of_pos (by positivity : (0 : ℝ) < 2 * δ)
    have h2 := log_le_four_mul_sqrt_sqrt hh1
    linarith
  have hlog0 : 0 ≤ Real.log (2 * δ * h) := Real.log_nonneg (by nlinarith)
  unfold AbcAdaptation.Tripod.epsilonE
  rw [← hs2, div_le_iff₀ (by positivity)]
  -- `(60δ)²·log ≤ (60δ)²(2δ + 4s) ≤ (60δ)²(2δ+4)·s = ε·M·s ≤ ε·s·s`
  have h1 : (60 * δ) ^ 2 * Real.log (2 * δ * h) ≤ (60 * δ) ^ 2 * (2 * δ + 4 * s) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : (60 * δ) ^ 2 * (2 * δ + 4 * s) ≤ (60 * δ) ^ 2 * (2 * δ + 4) * s := by
    have : 2 * δ + 4 * s ≤ (2 * δ + 4) * s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ (60 * δ) ^ 2)]
  have h3 : (60 * δ) ^ 2 * (2 * δ + 4) = ε * M := by rw [hM]; field_simp
  have h4 : ε * M * s ≤ ε * (s * s) := by
    have := mul_le_mul_of_nonneg_left hsM (mul_nonneg hε.le hs0)
    calc ε * M * s = ε * s * M := by ring
      _ ≤ ε * s * s := this
      _ = ε * (s * s) := by ring
  calc (60 * δ) ^ 2 * Real.log (2 * δ * h) ≤ (60 * δ) ^ 2 * (2 * δ + 4) * s := h1.trans h2
    _ = ε * M * s := by rw [h3]
    _ ≤ ε * (s * s) := h4

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.epsilonELargeHeight
  let c ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"
