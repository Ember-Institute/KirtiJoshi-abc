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





lemma thetaSet_nonneg (A : Finset ℕ) : 0 ≤ thetaSet A :=
  Finset.sum_nonneg fun p _ => by
    rcases Nat.eq_zero_or_pos p with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)

lemma log_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)







namespace ChebyshevBound

variable (cheb : ChebyshevBound)



end ChebyshevBound



namespace LocalHeightData

variable (L : LocalHeightData)

















end LocalHeightData

end Iut

end AbcAdaptation.Reference

open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.ChebyshevBound
open Finset Real
variable (cheb : ChebyshevBound)

theorem AbcAdaptation.Reference.Iut.ChebyshevBound.exists_prime_notMem (A : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * (thetaSet A + cheb.ξ) := by
  set x : ℝ := 2 * (thetaSet A + cheb.ξ) with hx
  have hξ : 0 < cheb.ξ := by linarith [cheb.five_le]
  have hxξ : cheb.ξ ≤ x := by rw [hx]; linarith [thetaSet_nonneg A]
  have hlow := cheb.lower x hxξ
  by_contra hcon
  push Not at hcon
  -- every prime `≤ x` lies in `A`, so `θ(x) ≤ θ_A`
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ A := by
    intro p hp
    have hp' : p ∈ Nat.primesBelow (⌊x⌋₊ + 1) := hp
    rw [Nat.mem_primesBelow] at hp'
    have hple : (p : ℝ) ≤ x := by
      have h1 : p ≤ ⌊x⌋₊ := by omega
      calc (p : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
        _ ≤ x := Nat.floor_le (by linarith)
    by_contra hpA
    exact absurd hple (not_le.mpr (hcon p hp'.2 hpA))
  have hθ : Chebyshev.theta x ≤ thetaSet A := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => AbcAdaptation.Reference.Iut.log_natCast_nonneg p
  -- but `θ(x) ≥ (2/3)x = (4/3)(θ_A + ξ) > θ_A`
  have : 2 / 3 * x = 4 / 3 * (thetaSet A + cheb.ξ) := by rw [hx]; ring
  linarith [thetaSet_nonneg A]
