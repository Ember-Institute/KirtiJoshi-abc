/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: TateCurvesTheta/TateCurve/JInvariant.lean
Original authors: The tate-curves-theta contributors
Original repository: https://github.com/lana-agents/tate-curves-theta
Original commit: ca6c2279d3cea0690cdb01328e727118d5485d68
Original license: Apache-2.0; the original copyright and license notice is retained below.
-/
/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Normed.Field.Basic
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_Basic
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Weierstrass
import Mathlib.Topology.MetricSpace.Ultra.Basic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# The `j`-invariant of the Tate curve

The `j`-invariant of `E_q : y² + xy = x³ + a₄x + a₆` as an explicit element of `K`:
`tateJ = c₄³/Δ` with `c₄ = 1 - 48a₄`. Ultrametrically the invariants have exact norms
`‖c₄‖ = 1` and `‖Δ‖ = ‖q‖` (`Discriminant.lean`), so

* `norm_tateJ` : `‖j(E_q)‖ = ‖q‖⁻¹`, in particular
* `one_lt_norm_tateJ` : `‖j(E_q)‖ > 1` — the Tate curve always has non-integral
  `j`-invariant, the analytic incarnation of potentially multiplicative reduction.

This is the input for the existence and uniqueness of the Tate parameter with prescribed
`j`-invariant (`QParameter/JParametrization.lean`): `q ↦ j(E_q)` is an injective map onto
`{j : ‖j‖ > 1}`.

## Main definitions and results

* `TateCurvesTheta.TateParameter.tateJ`: the `j`-invariant `c₄³/Δ` of `E_q`.
* `TateCurvesTheta.TateParameter.tateJ_eq_j`: agreement with Mathlib's
  `WeierstrassCurve.j` under `(12 : K) ≠ 0`.
* `TateCurvesTheta.TateParameter.norm_tateCurve_c₄`: `‖c₄(E_q)‖ = 1`.
* `TateCurvesTheta.TateParameter.norm_tateJ`, `one_lt_norm_tateJ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

variable (t : TateParameter K)

/-- **The `j`-invariant of the Tate curve** `E_q`, as the explicit element `c₄³/Δ` of `K`
(independent of the `IsElliptic` instance; see `tateJ_eq_j` for the agreement with
Mathlib's `WeierstrassCurve.j`). -/
def tateJ : K := t.tateCurve.c₄ ^ 3 / t.tateCurve.Δ

end TateParameter

end TateCurvesTheta

end

end AbcAdaptation.Reference
