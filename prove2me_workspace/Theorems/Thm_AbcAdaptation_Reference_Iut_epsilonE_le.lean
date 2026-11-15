/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Namespace adaptation of the complete original source command. The proof body
and signature bytes are retained. Validation is recorded in the delivery evidence. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22_NumericInputs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_self_of_pos
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_four_mul_sqrt_sqrt

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference
namespace Iut
universe u v w
open Finset Real

/-- `ε_E` is small for large `h`: `ε_E ≤ ε` as soon as `h ≥ ((60δ)²(2δ+4)/ε)⁴`. -/
lemma epsilonE_le {δ h ε : ℝ} (hδ : 1 ≤ δ) (hε : 0 < ε)
    (hh : ((60 * δ) ^ 2 * (2 * δ + 4) / ε) ^ 4 ≤ h) (hh1 : 1 ≤ h) :
    epsilonE δ h ≤ ε := by
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
  unfold epsilonE
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

end Iut
end AbcAdaptation.Reference
