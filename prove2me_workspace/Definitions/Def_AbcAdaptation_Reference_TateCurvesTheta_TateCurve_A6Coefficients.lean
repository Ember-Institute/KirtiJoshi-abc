/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Weierstrass

noncomputable section

namespace AbcAdaptation.Reference.TateCurvesTheta

/-- The integer coefficient `cₘ = (5 m³ + 7 m⁵)/12` (with `m = n + 1`) of the `a₆` series. It is a
genuine integer thanks to `twelve_dvd_five_mul_cube_add_seven_mul_pow`. -/
def a₆Coeff (n : ℕ) : ℕ := (5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12

/-- The term-wise divisibility `12 ∣ 5 m³ + 7 m⁵` underlying the integrality of the Tate
coefficient `a₆`. Proved by checking all residues in `ZMod 12`. -/
lemma twelve_dvd_five_mul_cube_add_seven_mul_pow (n : ℕ) :
    12 ∣ 5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 := by
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  refine (ZMod.natCast_eq_zero_iff _ 12).mp ?_
  push_cast
  exact h ((n : ZMod 12) + 1)

/-- Defining property of `a₆Coeff`: `12 · cₘ = 5 m³ + 7 m⁵`. -/
lemma twelve_mul_a₆Coeff (n : ℕ) :
    12 * a₆Coeff n = 5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 :=
  Nat.mul_div_cancel' (twelve_dvd_five_mul_cube_add_seven_mul_pow n)

/-- The leading coefficient of the `a₆` series is `c₀ = (5 + 7)/12 = 1`. -/
@[simp] lemma a₆Coeff_zero : a₆Coeff 0 = 1 := by decide

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The common analytic factor `qⁿ⁺¹ / (1 - qⁿ⁺¹)` shared by every Eisenstein term. -/
def qFactor (n : ℕ) : K := (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))

/-- The Eisenstein series written with the shared factor pulled out. -/
lemma eisenstein_eq_tsum_qFactor (k : ℕ) :
    t.eisenstein k = ∑' n : ℕ, ((n + 1 : ℕ) : K) ^ k * t.qFactor n := by
  simp only [eisenstein, qFactor, mul_div_assoc]

/-- The term-wise identity `5 (m³ Q) + 7 (m⁵ Q) = 12 (cₘ Q)`, where `Q = qᵐ/(1-qᵐ)` and
`cₘ = a₆Coeff`, packaging the divisibility `12 ∣ 5 m³ + 7 m⁵`. -/
lemma term_combo (n : ℕ) :
    5 * (((n + 1 : ℕ) : K) ^ 3 * t.qFactor n) + 7 * (((n + 1 : ℕ) : K) ^ 5 * t.qFactor n)
      = 12 * ((a₆Coeff n : K) * t.qFactor n) := by
  have hcast : 5 * ((n + 1 : ℕ) : K) ^ 3 + 7 * ((n + 1 : ℕ) : K) ^ 5 = 12 * (a₆Coeff n : K) := by
    have h : ((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 : ℕ) : K) = ((12 * a₆Coeff n : ℕ) : K) := by
      rw [twelve_mul_a₆Coeff]
    push_cast at h ⊢
    linear_combination h
  linear_combination t.qFactor n * hcast

end TateParameter
end AbcAdaptation.Reference.TateCurvesTheta
