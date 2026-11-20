/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Rational.lean, lines 27–42
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Polynomial

/-- Polynomial identities certifying the ramification of the rational function `N / D`.
The denominator vanishes exactly at the roots of `f`. The powers of `H` and `K`
describe the fibers over `0` and `1728`. -/
structure RatCert (f N D H K R : ℂ[X]) (c : ℂ) : Prop where
  c_ne : c ≠ 0
  hN : N = C c * H ^ 3
  hK : N - 1728 * D = C c * K ^ 2
  hcrit : derivative N * D - N * derivative D = R * H ^ 2 * K
  f_dvd_D : ∃ q, D = f * q
  D_dvd_f : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = D * q
  R_dvd_f : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = R * q
  H_cop : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * H + b * f = C d
  K_cop : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * K + b * f = C d
  H_sqf : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * derivative H + b * H = C d
  K_sqf : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * derivative K + b * K = C d
  deg : D.natDegree < N.natDegree
  D_ne : D ≠ 0

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
