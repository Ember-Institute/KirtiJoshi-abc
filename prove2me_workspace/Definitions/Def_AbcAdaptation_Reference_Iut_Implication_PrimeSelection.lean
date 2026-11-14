/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

namespace AbcAdaptation.Reference


/-!
# Prime selection for Corollary 2.2 (IUT IV, Proposition 2.1(ii) and (P1)–(P3))

The proof of IUT IV, Corollary 2.2 chooses, for an elliptic curve `E_F` of height
`h = log(q_∀)`, a prime `ℓ` such that

* (P1) `√h ≤ ℓ ≤ 10δ·√h·log(2δh)`;
* (P2) `ℓ` divides no nonzero local height `h_v`;
* (P3) if `ℓ = p_v` for some bad place `v` then `h_v < √h`.

The tool is IUT IV, Proposition 2.1(ii): from Chebyshev-type bounds `(2/3)x ≤ θ(x) ≤ 2x`
for `x ≥ ξ_prm`, for every finite set `A` of primes there is a prime `p ∉ A` with
`p ≤ 2(θ_A + ξ_prm)`, where `θ_A = ∑_{p ∈ A} log p`. The Chebyshev bounds themselves are
the explicit certificate `ChebyshevBound` (taxis #6), discharged from Mathlib in
`ChebyshevExplicit.lean` (`chebyshevBoundExplicit`); everything else in this file is proved.

The local heights enter through `LocalHeightData`: a finite family of bad places with
residue characteristics `p_v`, local heights `h_v ≥ 1`, and residue degrees `f_v ≥ 1`,
with `[F : ℚ]·h = ∑_v h_v·f_v·log p_v` and `[F : ℚ] ≤ δ` — the data of the `q`-divisor
of `E_F` in the notation of IUT IV, Theorem 1.10 and [GenEll], Definition 3.3.
-/

universe w

namespace Iut

open Finset Real

/-- **IUT IV, Proposition 2.1(ii)** as an explicit certificate: a threshold `ξ_prm ≥ 5`
beyond which Chebyshev's function `θ(x) = ∑_{p ≤ x} log p` satisfies
`(2/3)·x ≤ θ(x) ≤ 2·x` (the printed upper factor is `4/3`; the factor `2` suffices here and is
what Mathlib's `θ(x) ≤ (log 4)·x` gives, see `chebyshevBoundExplicit`; taxis #6). -/
structure ChebyshevBound where
  /-- The threshold `ξ_prm`. -/
  ξ : ℝ
  /-- `ξ_prm ≥ 5`. -/
  five_le : 5 ≤ ξ
  /-- The lower Chebyshev bound. -/
  lower : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x
  /-- The upper Chebyshev bound. -/
  upper : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 2 * x

/-- `θ_A = ∑_{p ∈ A} log p` for a finite set of natural numbers. -/
noncomputable def thetaSet (A : Finset ℕ) : ℝ := ∑ p ∈ A, Real.log p











namespace ChebyshevBound

variable (cheb : ChebyshevBound)



end ChebyshevBound

/-- **Local height data** of an elliptic curve `E_F` over a number field `F` in the
sense of IUT IV, Theorem 1.10 / [GenEll], Definition 3.3: a finite family of bad places
with residue characteristics `p_v`, local heights `h_v ≥ 1`, and residue degrees
`f_v ≥ 1`, such that `[F : ℚ]·h = ∑_v h_v·f_v·log p_v`, where `h = log(q_∀)` is the
normalized degree of the `q`-divisor. -/
structure LocalHeightData : Type (w + 1) where
  /-- The index type of the bad places. -/
  ι : Type w
  /-- The bad places. -/
  bad : Finset ι
  /-- The residue characteristic of a bad place. -/
  p : ι → ℕ
  /-- The local height `h_v = ord_v(q_v)` at a bad place. -/
  hv : ι → ℕ
  /-- The residue degree `f_v`. -/
  f : ι → ℕ
  /-- The degree `[F : ℚ]`. -/
  deg : ℕ
  /-- `[F : ℚ] ≥ 1`. -/
  one_le_deg : 1 ≤ deg
  /-- Residue characteristics are prime. -/
  p_prime : ∀ v ∈ bad, (p v).Prime
  /-- Local heights at bad places are positive. -/
  one_le_hv : ∀ v ∈ bad, 1 ≤ hv v
  /-- Residue degrees are positive. -/
  one_le_f : ∀ v ∈ bad, 1 ≤ f v
  /-- Over a rational prime, the residue degrees sum to at most `[F : ℚ]`
  (`∑_{v ∣ p} e_v f_v = [F : ℚ]`). -/
  sum_f_le : ∀ q : ℕ, ∑ v ∈ bad.filter (fun v => p v = q), f v ≤ deg

namespace LocalHeightData

variable (L : LocalHeightData)

/-- The height `h = log(q_∀) = (1/[F:ℚ])·∑_v h_v f_v log p_v`. -/
noncomputable def height : ℝ :=
  (∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg















end LocalHeightData

end Iut

end AbcAdaptation.Reference
