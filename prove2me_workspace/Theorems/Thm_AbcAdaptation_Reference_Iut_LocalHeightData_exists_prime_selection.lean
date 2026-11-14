/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection

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















namespace ChebyshevBound

variable (cheb : ChebyshevBound)



end ChebyshevBound



namespace LocalHeightData

variable (L : LocalHeightData)

















end LocalHeightData

end Iut

end AbcAdaptation.Reference

open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.LocalHeightData
open Finset Real
variable (L : LocalHeightData)

theorem AbcAdaptation.Reference.Iut.LocalHeightData.exists_prime_selection (cheb : ChebyshevBound) (δ : ℝ) (hδ : 2 ≤ δ)
    (hdeg : (L.deg : ℝ) ≤ δ) (hξ : cheb.ξ ≤ Real.sqrt L.height) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ Real.sqrt L.height ≤ ℓ ∧
      (ℓ : ℝ) ≤ 10 * δ * Real.sqrt L.height * Real.log (2 * δ * L.height) ∧
      (∀ v ∈ L.bad, ¬ ℓ ∣ L.hv v) ∧
      (∀ v ∈ L.bad, L.p v = ℓ → (L.hv v : ℝ) < Real.sqrt L.height) := by
  sorry
