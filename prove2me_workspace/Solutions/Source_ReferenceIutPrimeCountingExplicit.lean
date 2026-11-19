/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Source refer/iut/Iut/Implication/ChebyshevExplicit.lean, lines 62–65 and 224–266
Source snapshot SHA-256 3d36fd7292c87fae5c5f4a29cbabf654a4bddf7a2ca479120f291ccd1e762a20
The Abel summation and little-o argument is supplied by Mathlib's
Chebyshev.eventually_primeCounting_le.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

private theorem primeCountingHyp_holds :
    ∃ η : ℝ, 1 < η ∧
      ∀ x : ℝ, η ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 3 * x / (2 * Real.log x) := by
  have hlog : Real.log 4 < (3 : ℝ) / 2 := by
    rw [Real.log_four_eq]
    linarith only [Real.log_two_lt_d9]
  obtain ⟨η₀, hη₀⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (sub_pos.mpr hlog))
  refine ⟨max η₀ 2, one_lt_two.trans_le (le_max_right _ _), fun x hx => ?_⟩
  have hbound := hη₀ x ((le_max_left _ _).trans hx)
  have hcoeff : Real.log 4 + (3 / 2 - Real.log 4) = (3 : ℝ) / 2 := by linarith
  rw [hcoeff] at hbound
  calc
    _ ≤ (3 / 2 : ℝ) * x / Real.log x := hbound
    _ = _ := by rw [div_mul_eq_mul_div₀, div_div]

/-- The prime-counting certificate with factor (3/2) and an eventual threshold greater than one. -/
noncomputable def primeCountingBoundExplicit : PrimeCountingBound :=
  let η := Classical.choose primeCountingHyp_holds
  let hη := Classical.choose_spec primeCountingHyp_holds
  ⟨η, hη.1, hη.2⟩

end AbcAdaptation.Reference.Iut
