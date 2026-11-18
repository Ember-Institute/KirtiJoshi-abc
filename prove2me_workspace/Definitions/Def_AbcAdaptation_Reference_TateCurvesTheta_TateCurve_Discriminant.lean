/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Lean.Elab.Tactic.Omega
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Series

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

lemma a₄_def : t.a₄ = -5 * t.eisenstein 3 := rfl
@[simp] lemma tateCurve_a₁ : t.tateCurve.a₁ = 1 := rfl
@[simp] lemma tateCurve_a₂ : t.tateCurve.a₂ = 0 := rfl
@[simp] lemma tateCurve_a₃ : t.tateCurve.a₃ = 0 := rfl
@[simp] lemma tateCurve_a₄ : t.tateCurve.a₄ = t.a₄ := rfl
@[simp] lemma tateCurve_a₆ : t.tateCurve.a₆ = t.a₆ := rfl

/-- The `b₂`-invariant of the Tate curve is `1`. -/
lemma tateCurve_b₂ : t.tateCurve.b₂ = 1 := by
  simp only [WeierstrassCurve.b₂, tateCurve_a₁, tateCurve_a₂]; ring

/-- The `b₄`-invariant of the Tate curve is `2 a₄(q)`. -/
lemma tateCurve_b₄ : t.tateCurve.b₄ = 2 * t.a₄ := by
  simp only [WeierstrassCurve.b₄, tateCurve_a₄, tateCurve_a₁, tateCurve_a₃]; ring

/-- The `b₆`-invariant of the Tate curve is `4 a₆(q)`. -/
lemma tateCurve_b₆ : t.tateCurve.b₆ = 4 * t.a₆ := by
  simp only [WeierstrassCurve.b₆, tateCurve_a₆, tateCurve_a₃]; ring

/-- The `b₈`-invariant of the Tate curve is `a₆(q) - a₄(q)²`. -/
lemma tateCurve_b₈ : t.tateCurve.b₈ = t.a₆ - t.a₄ ^ 2 := by
  simp only [WeierstrassCurve.b₈, tateCurve_a₆, tateCurve_a₄, tateCurve_a₁, tateCurve_a₂,
    tateCurve_a₃]; ring

variable [IsUltrametricDist K]

/-- In a nonarchimedean normed field, every natural-number literal `≥ 2` has norm `≤ 1`. -/
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

omit [IsUltrametricDist K] in
/-- `‖q‖² ≤ ‖q‖`, since `0 < ‖q‖ < 1`. -/
private lemma norm_q_sq_le : ‖(t.q : K)‖ ^ 2 ≤ ‖(t.q : K)‖ := by
  calc ‖(t.q : K)‖ ^ 2
      ≤ ‖(t.q : K)‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by norm_num)
    _ = ‖(t.q : K)‖ := pow_one _

/-- Each term of the Eisenstein series `sₖ(q)` has norm `≤ ‖q‖ⁿ⁺¹`: the natural-number factor
`(n + 1)ᵏ` is harmless (`‖(n + 1 : K)‖ ≤ 1`) and the denominator `1 - qⁿ⁺¹` has norm `1`. -/
private lemma norm_eisenstein_term_le (k n : ℕ) :
    ‖((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))‖
      ≤ ‖(t.q : K)‖ ^ (n + 1) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, t.norm_one_sub_qpow n, div_one]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 ^ k * ‖(t.q : K)‖ ^ (n + 1) := by
        gcongr
        exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
    _ = ‖(t.q : K)‖ ^ (n + 1) := by rw [one_pow, one_mul]

variable [CompleteSpace K]

/-- **Leading term of the Eisenstein series.** `sₖ(q) = q + O(q²)`: the `m = 1` term is
`q / (1 - q) = q + q²/(1 - q)` and every later term has norm `≤ ‖q‖²`, so in the ultrametric world
`‖sₖ(q) - q‖ ≤ ‖q‖²`. -/
lemma norm_eisenstein_sub_q_le (k : ℕ) :
    ‖t.eisenstein k - (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  have hsum := t.eisenstein_summand_summable k
  rw [eisenstein, hsum.tsum_eq_zero_add]
  -- The `n = 0` term is `q / (1 - q)`; fold the subtracted `q` into it.
  have hq0 : ((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1))
      - (t.q : K) = (t.q : K) ^ 2 / (1 - (t.q : K)) := by
    have hne : (1 : K) - (t.q : K) ≠ 0 := by
      simpa using t.one_sub_qpow_ne_zero 0
    simp only [Nat.cast_one, one_pow, pow_one, zero_add]
    field_simp
    ring
  rw [show (((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1))
        + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1 + 1)
          / (1 - (t.q : K) ^ (n + 1 + 1))) - (t.q : K)
      = (((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1)) - (t.q : K))
        + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1 + 1)
          / (1 - (t.q : K) ^ (n + 1 + 1)) from by ring]
  rw [hq0]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- `‖q²/(1-q)‖ = ‖q‖²`.
    rw [norm_div, norm_pow, show (1 : K) - (t.q : K) = 1 - (t.q : K) ^ (0 + 1) by rw [pow_one],
      t.norm_one_sub_qpow 0, div_one]
  · -- `‖∑ later terms‖ ≤ ‖q‖²`.
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun n => ?_)
    refine (t.norm_eisenstein_term_le k (n + 1)).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-- The Eisenstein series is norm-bounded by `‖q‖`: `‖sₖ(q)‖ ≤ ‖q‖`. -/
lemma norm_eisenstein_le (k : ℕ) : ‖t.eisenstein k‖ ≤ ‖(t.q : K)‖ := by
  have h := t.norm_eisenstein_sub_q_le k
  rw [show t.eisenstein k = (t.eisenstein k - (t.q : K)) + (t.q : K) from by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_refl _))
  exact h.trans t.norm_q_sq_le

/-- The Tate coefficient `a₄(q) = -5 s₃(q)` is norm-bounded by `‖q‖`. -/
lemma norm_a₄_le : ‖t.a₄‖ ≤ ‖(t.q : K)‖ := by
  simp only [a₄_def, norm_mul, norm_neg]
  calc ‖(5 : K)‖ * ‖t.eisenstein 3‖
      ≤ 1 * ‖(t.q : K)‖ :=
        mul_le_mul (norm_ofNat_le_one 5) (t.norm_eisenstein_le 3) (norm_nonneg _) zero_le_one
    _ = ‖(t.q : K)‖ := one_mul _

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The discriminant of the Tate curve in terms of its coefficients.** Expanding
`Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` with the Tate `b`-invariants `b₂ = 1`, `b₄ = 2a₄`,
`b₆ = 4a₆`, `b₈ = a₆ - a₄²` gives a polynomial in `a₄(q), a₆(q)`. -/
lemma tateCurve_Δ_eq :
    t.tateCurve.Δ = -t.a₆ + t.a₄ ^ 2 - 64 * t.a₄ ^ 3 - 432 * t.a₆ ^ 2 + 72 * t.a₄ * t.a₆ := by
  simp only [WeierstrassCurve.Δ, t.tateCurve_b₂, t.tateCurve_b₄, t.tateCurve_b₆, t.tateCurve_b₈]
  ring

/-- **Leading-term estimate for the discriminant**: `‖Δ(E_q) - q‖ ≤ ‖q‖²` — the
discriminant is `q` to leading order (the `q`-expansion `Δ = q - 24q² + …`). -/
lemma norm_tateCurve_Δ_sub_q_le (h12 : (12 : K) ≠ 0) :
    ‖t.tateCurve.Δ - (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  have hΔ := t.tateCurve_Δ_eq
  -- `Δ - q` is a sum of five terms each of norm `≤ ‖q‖²`.
  have hrw : t.tateCurve.Δ - (t.q : K)
      = -(t.a₆ + (t.q : K)) + t.a₄ ^ 2 + (-64) * t.a₄ ^ 3 + (-432) * t.a₆ ^ 2
          + 72 * t.a₄ * t.a₆ := by
    rw [hΔ]; ring
  rw [hrw]
  have b1 : ‖-(t.a₆ + (t.q : K))‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    rw [norm_neg]; exact t.norm_a₆_add_q_le h12
  have b2 : ‖t.a₄ ^ 2‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) t.norm_a₄_le 2
  have b3 : ‖(-64 : K) * t.a₄ ^ 3‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    rw [norm_mul, norm_neg, norm_pow]
    calc ‖(64 : K)‖ * ‖t.a₄‖ ^ 3
        ≤ 1 * ‖(t.q : K)‖ ^ 3 :=
          mul_le_mul (norm_ofNat_le_one 64) (pow_le_pow_left₀ (norm_nonneg _) t.norm_a₄_le 3)
            (pow_nonneg (norm_nonneg _) 3) zero_le_one
      _ = ‖(t.q : K)‖ ^ 3 := one_mul _
      _ ≤ ‖(t.q : K)‖ ^ 2 :=
          pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by norm_num)
  have b4 : ‖(-432 : K) * t.a₆ ^ 2‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    rw [norm_mul, norm_neg, norm_pow]
    calc ‖(432 : K)‖ * ‖t.a₆‖ ^ 2
        ≤ 1 * ‖(t.q : K)‖ ^ 2 :=
          mul_le_mul (norm_ofNat_le_one 432)
            (pow_le_pow_left₀ (norm_nonneg _) (t.norm_a₆_le h12) 2)
            (pow_nonneg (norm_nonneg _) 2) zero_le_one
      _ = ‖(t.q : K)‖ ^ 2 := one_mul _
  have b5 : ‖(72 : K) * t.a₄ * t.a₆‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    rw [norm_mul, norm_mul, pow_two]
    calc ‖(72 : K)‖ * ‖t.a₄‖ * ‖t.a₆‖
        ≤ 1 * ‖(t.q : K)‖ * ‖(t.q : K)‖ :=
          mul_le_mul
            (mul_le_mul (norm_ofNat_le_one 72) t.norm_a₄_le (norm_nonneg _) zero_le_one)
            (t.norm_a₆_le h12) (norm_nonneg _) (by positivity)
      _ = ‖(t.q : K)‖ * ‖(t.q : K)‖ := by rw [one_mul]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 b2)) b3)) b4)) b5)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The strict inequality `‖q‖² < ‖q‖` for a Tate parameter. -/
lemma norm_q_sq_lt : ‖(t.q : K)‖ ^ 2 < ‖(t.q : K)‖ := by
  calc ‖(t.q : K)‖ ^ 2 = ‖(t.q : K)‖ * ‖(t.q : K)‖ := by rw [pow_two]
    _ < 1 * ‖(t.q : K)‖ := by
        gcongr
        exacts [t.norm_q_pos, t.norm_lt_one]
    _ = ‖(t.q : K)‖ := one_mul _

/-- **The exact norm of the discriminant**: `‖Δ(E_q)‖ = ‖q‖`, by the ultrametric isosceles
law applied to the leading-term estimate. -/
theorem norm_tateCurve_Δ (h12 : (12 : K) ≠ 0) : ‖t.tateCurve.Δ‖ = ‖(t.q : K)‖ := by
  have hDnorm := t.norm_tateCurve_Δ_sub_q_le h12
  have hlt : ‖t.tateCurve.Δ - (t.q : K)‖ < ‖(t.q : K)‖ :=
    lt_of_le_of_lt hDnorm t.norm_q_sq_lt
  have hup : ‖t.tateCurve.Δ‖ ≤ ‖(t.q : K)‖ := by
    have h := IsUltrametricDist.norm_add_le_max (t.tateCurve.Δ - (t.q : K)) (t.q : K)
    simpa using h.trans (max_le hlt.le le_rfl)
  have hdown : ‖(t.q : K)‖ ≤ ‖t.tateCurve.Δ‖ := by
    by_contra hcon
    rw [not_le] at hcon
    have h := IsUltrametricDist.norm_add_le_max ((t.q : K) - t.tateCurve.Δ) t.tateCurve.Δ
    rw [sub_add_cancel] at h
    have : ‖(t.q : K) - t.tateCurve.Δ‖ < ‖(t.q : K)‖ := by rwa [norm_sub_rev]
    exact absurd (h.trans_lt (max_lt this hcon)) (lt_irrefl _)
  exact le_antisymm hup hdown

/-- **Nonvanishing of the discriminant.** Over a complete nonarchimedean field with
`(12 : K) ≠ 0`, `Δ(E_q) ≠ 0`: indeed `‖Δ(E_q)‖ = ‖q‖ > 0`. -/
theorem tateCurve_Δ_ne_zero (h12 : (12 : K) ≠ 0) : t.tateCurve.Δ ≠ 0 := by
  intro h
  have := t.norm_tateCurve_Δ h12
  rw [h, norm_zero] at this
  exact absurd this.symm (ne_of_gt t.norm_q_pos)

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter
