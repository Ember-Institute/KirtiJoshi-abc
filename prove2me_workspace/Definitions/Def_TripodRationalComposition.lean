/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcTripod
import Definitions.Def_AbcRationalHeight
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem rationalABCHeight_of_statementI (hI : StatementI)
    (hdeg : DegreeOneProjection) (hdiff : LogDifferentZeroProjection)
    (hheight : HeightComparisonProjection) (hcond : RadicalConductorProjection) :
    AbcAdaptation.RationalABCHeight := by
  intro ε hε
  obtain ⟨C, hC⟩ := hI 1 ε hε
  refine ⟨C, fun q h0 h1 => ?_⟩
  let x := rationalPoint q h0 h1
  have hdegree : deg x.1 = 1 := hdeg q h0 h1
  have hdifferent : logDiff x = 0 := hdiff q h0 h1
  have hheight' : Height.logHeight₁ q ≤ htCan x := hheight q h0 h1
  have hconductor : logCond x ≤
      Real.log ((UniqueFactorizationMonoid.radical
        (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ) := hcond q h0 h1
  have hstatement := hC x hdegree.le
  have hscale : (1 + ε) * logCond x ≤
      (1 + ε) * Real.log ((UniqueFactorizationMonoid.radical
        (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left hconductor (le_of_lt (add_pos zero_lt_one hε))
  calc
    Height.logHeight₁ q ≤ htCan x := hheight'
    _ ≤ (1 + ε) * (logDiff x + logCond x) + C := hstatement
    _ = (1 + ε) * logCond x + C := by rw [hdifferent, zero_add]
    _ ≤ (1 + ε) * Real.log ((UniqueFactorizationMonoid.radical
          (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ) + C := by
      linarith [hscale]

end AbcAdaptation.Tripod
