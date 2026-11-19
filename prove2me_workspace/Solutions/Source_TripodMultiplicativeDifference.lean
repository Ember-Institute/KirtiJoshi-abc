/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original path Iut/Tower/MultiplicativeKernel.lean
-/
import Solutions.Source_TripodMultiplicativeSlopes

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.MultKernel

open WeierstrassCurve WeierstrassCurve.Affine
open JoshiTeich.Act1Scene1.ReductionKernel (valuation_natCast_le_one)
open scoped Classical

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) {μ : K}

/-! ### The Legendre equation and integrality -/

section Curve

-- a model `W` of the Legendre curve `y² = x(x − 1)(x − μ)`: the coefficient hypotheses
variable {W : Affine K} (hW₁ : W.a₁ = 0) (hW₂ : W.a₂ = -(1 + μ)) (hW₃ : W.a₃ = 0)
  (hW₄ : W.a₄ = μ) (hW₆ : W.a₆ = 0)
include hW₁ hW₂ hW₃ hW₄ hW₆

/-! ### The difference `σ Q − Q` at the node -/

section Difference

variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
include hμ h2 hσμ hσ hvσ

/-- **`σ Q − Q` has nonsingular reduction** for a point `Q = (x, y)` reducing to the node
(`v(x) < 1`): it is `0`, or an affine point with `1 ≤ v(x)`. -/
theorem sub_eq_zero_or_one_le {x y : K} (h : W.Nonsingular x y)
    (h' : W.Nonsingular (σ x) (σ y)) (hx : v x < 1) :
    Point.some (σ x) (σ y) h' - Point.some x y h = 0 ∨
      ∃ (x' y' : K) (h'' : W.Nonsingular x' y'),
        Point.some (σ x) (σ y) h' - Point.some x y h = Point.some x' y' h'' ∧ 1 ≤ v x' := by
  have hneg : ∀ a b : K, W.negY a b = -b := fun a b => by
    simp [negY, hW₁, hW₃]
  rw [sub_eq_add_neg, Point.neg_some]
  by_cases hxy : σ x = x ∧ σ y = W.negY x (W.negY x y)
  · left
    exact Point.add_of_Y_eq hxy.1 hxy.2
  · right
    refine ⟨_, _, _, Point.add_some hxy, ?_⟩
    simp only [hneg, neg_neg] at hxy
    -- the slope of the chord
    set L := W.slope (σ x) x (σ y) (W.negY x y) with hL
    have haddX : W.addX (σ x) x L = (L ^ 2 + 1) + (μ - σ x - x) := by
      simp only [addX, hW₁, hW₂]; ring
    have hrest : v (μ - σ x - x) < 1 :=
      (Valuation.map_sub _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt hμ (by rw [hvσ]; exact hx))) hx)
    suffices key : 1 < v L ∨ (v L ≤ 1 ∧ v (L ^ 2 + 1) = 1) by
      rw [haddX]
      rcases key with hL1 | ⟨hL1, hL2⟩
      · have hL2 : 1 < v (L ^ 2 + 1) := by
          rw [Valuation.map_add_eq_of_lt_left, map_pow]
          · exact one_lt_pow₀ hL1 two_ne_zero
          · rw [map_pow, map_one]; exact one_lt_pow₀ hL1 two_ne_zero
        rw [Valuation.map_add_eq_of_lt_left _ (hrest.trans hL2)]
        exact hL2.le
      · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hL2]; exact hrest), hL2]
    -- compute the slope
    by_cases hxx : σ x = x
    · -- `σ Q = −Q`, `σ Q − Q = −2Q`
      have hyy : σ y = -y := by
        rcases Y_eq_of_X_eq h'.1 h.1 hxx with hh | hh
        · exact absurd ⟨hxx, hh⟩ hxy
        · rw [hh, hneg]
      have hy0 : y ≠ 0 := by
        intro h0
        exact hxy ⟨hxx, by rw [hyy, h0, neg_zero]⟩
      -- the branch invariants are moved to their negatives, contradiction or middle component
      by_cases hμx : v μ < v x
      · exfalso
        -- `t = y/x` is a unit with `σ t = −t`, so `v(2t) < 1`
        have hvx0 : v x ≠ 0 := (lt_of_le_of_lt zero_le hμx).ne'
        have ht1 : v (y / x) = 1 := by
          rw [map_div₀, valuation_y_eq v hW₁ hW₂ hW₃ hW₄ hW₆ h.1 hx hμx, div_self hvx0]
        have hσt := hσ (y / x) ht1.le
        rw [map_div₀, hyy, hxx, neg_div] at hσt
        have e : -(y / x) - y / x = -(2 * (y / x)) := by ring
        rw [e, Valuation.map_neg, map_mul, h2, one_mul, ht1] at hσt
        exact lt_irrefl _ hσt
      · -- middle component: the tangent slope `f'(x)/(−2y)` is non-integral
        left
        have hxμ : v x ≤ v μ := not_lt.mp hμx
        have hμ0 : μ ≠ 0 := fun h0 => by
          rw [h0, map_zero] at hxμ
          have hx0 : x = 0 := (Valuation.zero_iff _).mp (le_antisymm hxμ zero_le)
          have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
          rw [hx0, zero_mul, zero_mul, pow_eq_zero_iff two_ne_zero] at this
          exact hy0 this
        have hyne : ¬ (-y = y) := by
          intro hcon
          have h2ne : (2 : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
          exact hy0 ((mul_eq_zero.mp (show 2 * y = 0 by linear_combination -hcon)).resolve_left
            h2ne)
        have hLeq : L = (3 * x ^ 2 + 2 * -(1 + μ) * x + μ) / (-y - y) := by
          rw [hL, hxx, hyy, Affine.slope, if_pos rfl]
          simp only [hneg, neg_neg, if_neg hyne, hW₁, hW₂, hW₄, zero_mul, sub_zero]
        set c := x / μ with hc
        set t := y / μ with ht
        have hxc : x = μ * c := by rw [hc]; field_simp
        have hyt : y = μ * t := by rw [ht]; field_simp
        have hμpos : 0 < v μ := lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hμ0))
        have hc1 : v c ≤ 1 := by
          rw [hc, map_div₀, div_le_one₀ hμpos]; exact hxμ
        have ht1 : v t ≤ 1 := by
          rw [ht, map_div₀, div_le_one₀ hμpos]
          exact valuation_y_le v hW₁ hW₂ hW₃ hW₄ hW₆ h.1 hx hxμ
        have htsq : t ^ 2 = c * (c - 1) * (μ * c - 1) := by
          have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
          rw [hxc, hyt] at this
          apply mul_left_cancel₀ (pow_ne_zero 2 hμ0)
          linear_combination this
        have hσt : σ t = -t := by
          rw [ht, map_div₀, hyy, hσμ, neg_div]
        have ht0 : v t < 1 := by
          have := hσ t ht1
          have e : -t - t = -(2 * t) := by ring
          rw [hσt, e, Valuation.map_neg, map_mul, h2, one_mul] at this
          exact this
        have ht0' : t ≠ 0 := by
          intro h0
          apply hy0
          rw [hyt, h0, mul_zero]
        have hg := valuation_c_mul_sub_one_lt v hμ hc1 htsq ht0
        have h2ne : (2 : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
        have hLc : L = (3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1) / (-(2 * t)) := by
          rw [hLeq, hxc, hyt, div_eq_div_iff]
          · ring
          · have e : -(μ * t) - μ * t = -(2 * (μ * t)) := by ring
            rw [e]
            exact neg_ne_zero.mpr (mul_ne_zero h2ne (mul_ne_zero hμ0 ht0'))
          · exact neg_ne_zero.mpr (mul_ne_zero h2ne ht0')
        have hnum : v (3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1) = 1 := by
          have e : 3 * μ * c ^ 2 - 2 * (1 + μ) * c + 1 = (1 - 2 * c) + μ * c * (3 * c - 2) := by
            ring
          rw [e, Valuation.map_add_eq_of_lt_left, valuation_one_sub_two_mul_eq_one v h2 hg]
          rw [valuation_one_sub_two_mul_eq_one v h2 hg, map_mul, map_mul]
          calc v μ * v c * v (3 * c - 2) ≤ v μ * 1 * 1 := by
                gcongr
                · exact (Valuation.map_sub _ _ _).trans (max_le
                    (by rw [map_mul]; exact mul_le_one' (valuation_natCast_le_one v
                      3) hc1) (valuation_natCast_le_one v 2))
            _ < 1 := by rw [mul_one, mul_one]; exact hμ
        rw [hLc, map_div₀, hnum, Valuation.map_neg, map_mul, h2, one_mul, one_div,
          one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr ht0')))]
        exact ht0
    · -- `σ x ≠ x`: the chord
      rw [hL, hneg, slope_of_X_ne hxx, sub_neg_eq_add]
      by_cases hμx : v μ < v x
      · exact slope_branch v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hvσ h.1 hx hμx hxx
      · exact Or.inl (slope_middle v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ h.1 hx
          (not_lt.mp hμx) hxx)

end Difference

end Curve

end AbcAdaptation.Reference.Iut.MultKernel
