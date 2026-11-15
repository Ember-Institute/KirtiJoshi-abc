/- Adaptation draft: two complete original definition commands, unchanged bodies and source contexts. Original source notice retained. No acceptance or publication is claimed. -/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference


universe w

namespace Iut

open Finset Real

namespace LocalHeightData

variable (L : LocalHeightData)

/-- The part of `log(q_∀)` supported at the places of residue characteristic `q`. -/
noncomputable def heightEq (q : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v = q), (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

/-- The part of `log(q_∀)` supported away from the residue characteristics `a` and `b`
(for `a = 2`, `b = ℓ`: the `log(q)` of the initial Θ-data, whose bad places are those
not dividing `2ℓ`). -/
noncomputable def heightOther (a b : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v ≠ a ∧ L.p v ≠ b),
    (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

end LocalHeightData

end Iut

end AbcAdaptation.Reference
