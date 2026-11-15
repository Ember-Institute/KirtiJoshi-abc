/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation of the accepted reference proof at its reusable registered name;
imports and surrounding context are reduced to numerical inputs. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real



end Iut

end AbcAdaptation.Reference

theorem AbcAdaptation.Reference.Iut.log_le_self_of_pos {y : ℝ} (hy : 0 < y) : Real.log y ≤ y := by
  linarith [Real.log_le_sub_one_of_pos hy]
