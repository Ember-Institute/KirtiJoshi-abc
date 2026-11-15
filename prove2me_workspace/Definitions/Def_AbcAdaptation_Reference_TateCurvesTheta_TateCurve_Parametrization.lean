/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: TateCurvesTheta/TateCurve/Parametrization.lean
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
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_Basic
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Weierstrass
import Mathlib.Topology.MetricSpace.Ultra.Basic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# The Tate parametrization: coordinate series `X(u)`, `Y(u)` and their convergence

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), Tate's
analytic parametrization of the curve `E_q` sends a point `u : Kˣ` to the affine point
`(X(u), Y(u))`, where (Silverman, *Advanced Topics*, Ch. V, Thm 3.1)
```
X q u = ∑' n : ℤ, qⁿ u / (1 - qⁿ u)²  - 2 s₁(q),
Y q u = ∑' n : ℤ, (qⁿ u)² / (1 - qⁿ u)³ + s₁(q),
```
with `sₖ(q)` the Eisenstein-type series of `TateCurvesTheta/TateCurve/Weierstrass.lean`.

This file fixes that normalization, defines the general terms `Xterm`, `Yterm` and the
coordinate functions `X`, `Y`, and proves the two defining series are unconditionally
`Summable` over a complete nonarchimedean field. This is the analytic-convergence foundation
for the full parametrization isomorphism `Kˣ/qᶻ ≅ E_q(K)`, whose hard core (the Weierstrass
equation for `(X(u), Y(u))` and the group isomorphism) is developed in a sibling file.

## Convergence

As in the theta-series issue, convergence needs completeness (`[CompleteSpace K]`) and the
ultrametric triangle inequality (`[IsUltrametricDist K]`) on top of the metric datum of a
`TateParameter`; these are added locally with a seam comment. In a complete nonarchimedean
group a family is summable as soon as its terms tend to zero along `cofinite`
(`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`), and here the term norm decays on
both ends of `ℤ`: writing `x = qⁿ u` with `‖x‖ = ‖q‖ⁿ ‖u‖`, the ultrametric isosceles law gives
`‖1 - x‖ = max 1 ‖x‖`, so
```
‖Xterm n‖ = ‖x‖ / (max 1 ‖x‖)²  =  ‖x‖       (‖x‖ < 1),   ‖x‖⁻¹  (‖x‖ > 1),
‖Yterm n‖ = ‖x‖² / (max 1 ‖x‖)³ =  ‖x‖²      (‖x‖ < 1),   ‖x‖⁻¹  (‖x‖ > 1).
```
Since `‖x‖ = ‖q‖ⁿ ‖u‖ → 0` as `n → +∞` and `→ +∞` as `n → -∞` (`0 < ‖q‖ < 1`), both term
norms tend to `0` on `atTop` and on `atBot`, i.e. on all of `cofinite = atBot ⊔ atTop`. (The
single index — if any — with `‖x‖ = 1` is irrelevant to a cofinite limit.)

## Main definitions

* `TateCurvesTheta.TateParameter.Xterm`, `TateParameter.Yterm`: the general terms of the
  coordinate series.
* `TateCurvesTheta.TateParameter.X`, `TateParameter.Y`: the Tate coordinate functions.

## Main results

* `TateParameter.norm_one_sub_of_norm_ne_one`: `‖1 - x‖ = max 1 ‖x‖` when `‖x‖ ≠ 1`.
* `TateParameter.one_sub_qzpow_mul_ne_zero`: `1 - qⁿ u ≠ 0` for `u ∉ qᶻ`.
* `TateParameter.Xterm_summable`, `TateParameter.Yterm_summable`: the coordinate series
  converge over a complete nonarchimedean field.
* `TateParameter.X_q_smul`, `TateParameter.Y_q_smul`: `q`-periodicity of the coordinate
  functions, `X(q·u) = X(u)` and `Y(q·u) = Y(u)` — the invariance that makes the Tate
  parametrization descend to the analytic quotient `Kˣ/qᶻ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]

variable (t : TateParameter K)

/-- The general term `qⁿ u / (1 - qⁿ u)²` of the `X`-coordinate series, indexed by `n : ℤ`. -/
def Xterm (u : Kˣ) (n : ℤ) : K :=
  (t.q : K) ^ n * (u : K) / (1 - (t.q : K) ^ n * (u : K)) ^ 2

/-- The general term `(qⁿ u)² / (1 - qⁿ u)³` of the `Y`-coordinate series, indexed by `n : ℤ`. -/
def Yterm (u : Kˣ) (n : ℤ) : K :=
  ((t.q : K) ^ n * (u : K)) ^ 2 / (1 - (t.q : K) ^ n * (u : K)) ^ 3

/-- The **Tate `X`-coordinate** `X q u = ∑' n, qⁿ u / (1 - qⁿ u)² - 2 s₁(q)`. -/
def X (u : Kˣ) : K := (∑' n : ℤ, t.Xterm u n) - 2 * t.eisenstein 1

/-- The **Tate `Y`-coordinate** `Y q u = ∑' n, (qⁿ u)² / (1 - qⁿ u)³ + s₁(q)`. -/
def Y (u : Kˣ) : K := (∑' n : ℤ, t.Yterm u n) + t.eisenstein 1

section Nonarchimedean

variable [IsUltrametricDist K]

variable [CompleteSpace K]

end Nonarchimedean

end TateParameter

end TateCurvesTheta

end

end AbcAdaptation.Reference
