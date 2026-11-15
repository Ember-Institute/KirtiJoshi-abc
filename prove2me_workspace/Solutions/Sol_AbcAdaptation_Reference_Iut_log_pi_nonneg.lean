/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Adaptation draft: exact original declaration retained; imports and surrounding
context reduced to numerical inputs. Compiler semantic identity is pending. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v



end Iut

end AbcAdaptation.Reference
theorem solution : 0 ≤ Real.log Real.pi :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])
