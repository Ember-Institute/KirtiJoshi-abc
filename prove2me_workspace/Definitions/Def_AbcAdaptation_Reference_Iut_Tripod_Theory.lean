/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Source data constructor adaptation only. Exact source body of Tripod.Basic.tripodTheory
uses the existing canonical point/field/height definitions and the already published
full height-theory structure. No new theorem or transport hypothesis is introduced. -/
import Definitions.Def_AbcTripod
import Definitions.Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Tripod

/-- **The concrete height theory of the tripod**: the instance of `Genl.HeightTheory` with
the tripod `(ℙ¹_ℚ, {0, 1, ∞})` as its only curve, the algebraic numbers `λ ∉ {0, 1}` as its
points, the absolute logarithmic Weil height, the log-different and the log-conductor of
`ℚ(λ)`, and the valuation-bounded compactly bounded subsets. -/
noncomputable def tripodTheory : AbcAdaptation.Reference.Genl.HeightTheory where
  Curve := Unit
  Pt _ := Pt
  Hyperbolic _ := True
  DivisorFree _ := False
  ptLE _ := ptLE
  ptEQ _ := ptEQ
  ptLE_zero _ := ptLE_zero
  ptLE_succ _ := ptLE_succ
  htCan _ := htCan
  logDiff _ := logDiff
  logCond _ := logCond
  tripod := ()
  hyperbolic_tripod := trivial
  CBS := CompactlyBounded
  cbsSet := CompactlyBounded.set

end AbcAdaptation.Tripod
