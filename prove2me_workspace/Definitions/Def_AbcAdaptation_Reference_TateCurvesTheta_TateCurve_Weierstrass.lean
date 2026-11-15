/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: TateCurvesTheta/TateCurve/Weierstrass.lean
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
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
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
import Mathlib.Topology.MetricSpace.Ultra.Basic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# The Tate Weierstrass model `E_q`

Given a Tate parameter `q` over a complete nonarchimedean field `K`, the Tate curve is the
elliptic curve with the classical Weierstrass equation
`y² + xy = x³ + a₄(q) x + a₆(q)`, where the coefficients are built from the Eisenstein-type
`q`-series
`sₖ(q) = ∑_{m ≥ 1} mᵏ qᵐ / (1 - qᵐ)`
via `a₄(q) = -5 s₃(q)` and `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12`
(Silverman, *Advanced Topics*, Ch. V, Thm 3.1).

This file constructs those coefficients, proves the defining `q`-series converge, and packages
the resulting `WeierstrassCurve K`. Upgrading it to an `EllipticCurve K` requires the classical
modular identity `Δ = q ∏_{n ≥ 1} (1 - qⁿ)²⁴` and is deferred to a dependent issue.

## Specialization of the base field

`TateCurvesTheta.TateParameter` is defined over an arbitrary `NormedField`. Convergence of the
Eisenstein series genuinely needs two extra hypotheses, added locally here (matching the seam
convention of `QParameter/BaseChange.lean`):

* `[IsUltrametricDist K]` (nonarchimedean absolute value): it forces `‖1 - qᵐ‖ = 1`, so every
  term of `sₖ(q)` has norm `‖(m : K)‖ᵏ · ‖q‖ᵐ ≤ ‖q‖ᵐ` — a purely geometric bound (in the
  ultrametric world the naive polynomial factor `mᵏ` is harmless because `‖(m : K)‖ ≤ 1`);
* `[CompleteSpace K]`: the norm-summable family is then summable in `K`.

## Main definitions

* `TateCurvesTheta.TateParameter.eisenstein`: the `q`-series `sₖ(q)`.
* `TateCurvesTheta.TateParameter.a₄`, `TateParameter.a₆`: the Tate coefficients.
* `TateCurvesTheta.TateParameter.tateCurve`: the Weierstrass curve `E_q : WeierstrassCurve K`.

## Main results

* `TateParameter.norm_one_sub_qpow`: `‖1 - qⁿ⁺¹‖ = 1`.
* `TateParameter.eisenstein_summand_summable`: the family defining `sₖ(q)` is summable.
* `TateParameter.tateCurve_b₂`, `_b₄`, `_b₆`, `_b₈`: the `b`-invariants of `E_q`, groundwork for
  the deferred discriminant computation.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V, Theorem 3.1.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]

variable (t : TateParameter K)

/-- The **Eisenstein-type `q`-series** `sₖ(q) = ∑_{m ≥ 1} mᵏ qᵐ / (1 - qᵐ)`, indexed by
`m = n + 1` over `n : ℕ`. It is the building block of the Tate coefficients. -/
def eisenstein (k : ℕ) : K :=
  ∑' n : ℕ, ((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))

section Nonarchimedean

variable [IsUltrametricDist K]

variable [CompleteSpace K]

end Nonarchimedean

/-- The Tate coefficient `a₄(q) = -5 s₃(q)`. -/
def a₄ : K := -5 * t.eisenstein 3

/-- The Tate coefficient `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12`. -/
def a₆ : K := -(5 * t.eisenstein 3 + 7 * t.eisenstein 5) / 12

/-- The **Tate Weierstrass curve** `E_q : y² + xy = x³ + a₄(q) x + a₆(q)`. -/
def tateCurve : WeierstrassCurve K where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := t.a₄
  a₆ := t.a₆

end TateParameter

end TateCurvesTheta

end

end AbcAdaptation.Reference
