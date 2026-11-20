/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Integrality.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticBounds
import Solutions.Source_ReferenceIutCanLiftOrbitDepth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open UpperHalfPlane
open scoped MatrixGroups

/-- A two-sided comparison between log norm and exponential orbit depth gives a polynomial
growth bound after precomposition by a commensurator element. -/
theorem polyBdd_smul_of_depth_comparison {Γ : Subgroup SL(2, ℝ)} {o : ℍ} {F : ℍ → ℂ}
    {a b : ℝ} (ha : 0 ≤ a)
    (hcomparison : ∀ τ : ℍ,
      Real.log (1 + ‖F τ‖) ≤ a * Real.exp (orbitDepth Γ o τ) + b ∧
        Real.exp (orbitDepth Γ o τ) ≤ a * Real.log (2 + ‖F τ‖) + b)
    {δ : SL(2, ℝ)} (hδ : δ ∈ Subgroup.Commensurable.commensurator Γ) :
    PolyBdd F fun τ ↦ ‖F (δ • τ)‖ := by
  obtain ⟨c, hc⟩ := exists_orbitDepth_smul_le o hδ
  let n := ⌈a * Real.exp c * a⌉₊
  let d := a * Real.exp c * b + b
  refine ⟨Real.exp d, n, fun τ ↦ ?_⟩
  have hcExp : Real.exp (orbitDepth Γ o (δ • τ)) ≤
      Real.exp c * Real.exp (orbitDepth Γ o τ) := by
    rw [← Real.exp_add, add_comm c]
    exact Real.exp_le_exp.mpr (hc τ)
  have hn : a * Real.exp c * a ≤ (n : ℝ) := Nat.le_ceil _
  have hlog : 0 ≤ Real.log (2 + ‖F τ‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (F τ)])
  have hlogBound : Real.log (1 + ‖F (δ • τ)‖) ≤ (n : ℝ) * Real.log (2 + ‖F τ‖) + d := by
    calc
      Real.log (1 + ‖F (δ • τ)‖) ≤ a * Real.exp (orbitDepth Γ o (δ • τ)) + b :=
        (hcomparison (δ • τ)).1
      _ ≤ a * (Real.exp c * Real.exp (orbitDepth Γ o τ)) + b :=
        add_le_add_left (mul_le_mul_of_nonneg_left hcExp ha) b
      _ = (a * Real.exp c) * Real.exp (orbitDepth Γ o τ) + b := by rw [mul_assoc]
      _ ≤ (a * Real.exp c) * (a * Real.log (2 + ‖F τ‖) + b) + b :=
        add_le_add_left
          (mul_le_mul_of_nonneg_left (hcomparison τ).2 (mul_nonneg ha (Real.exp_pos c).le)) b
      _ = (a * Real.exp c * a) * Real.log (2 + ‖F τ‖) + d := by
        dsimp [d]
        ring
      _ ≤ (n : ℝ) * Real.log (2 + ‖F τ‖) + d :=
        add_le_add_left (mul_le_mul_of_nonneg_right hn hlog) d
  calc
    ‖F (δ • τ)‖ ≤ 1 + ‖F (δ • τ)‖ := le_add_of_nonneg_left zero_le_one
    _ = Real.exp (Real.log (1 + ‖F (δ • τ)‖)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp ((n : ℝ) * Real.log (2 + ‖F τ‖) + d) := Real.exp_le_exp.mpr hlogBound
    _ = Real.exp d * (2 + ‖F τ‖) ^ n := by
      rw [Real.exp_add, mul_comm, ← Real.log_pow, Real.exp_log (by positivity)]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
