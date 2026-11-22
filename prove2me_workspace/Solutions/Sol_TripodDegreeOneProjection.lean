/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/ClassicalAbc.lean
-/
import Definitions.Def_AbcTripod

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution : DegreeOneProjection := by
  intro q h0 h1
  change (minpoly ℚ (algebraMap ℚ Qbar q)).natDegree = 1
  rw [minpoly.eq_X_sub_C]
  exact Polynomial.natDegree_X_sub_C q
