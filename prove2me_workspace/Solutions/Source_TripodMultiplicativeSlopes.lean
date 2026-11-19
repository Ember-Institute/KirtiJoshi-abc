/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original path Iut/Tower/MultiplicativeKernel.lean
-/
import Solutions.Source_ReferenceIutTowerTorsionRigid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.MultKernel

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) {μ : K}

/-! ### The Legendre equation and integrality -/

section Curve

-- a model `W` of the Legendre curve `y² = x(x − 1)(x − μ)`: the coefficient hypotheses
variable {W : Affine K} (hW₁ : W.a₁ = 0) (hW₂ : W.a₂ = -(1 + μ)) (hW₃ : W.a₃ = 0)
  (hW₄ : W.a₄ = μ) (hW₆ : W.a₆ = 0)
include hW₁ hW₂ hW₃ hW₄ hW₆
omit [LinearOrderedCommGroupWithZero Γ] in
/-- The Legendre equation `y² = x(x − 1)(x − μ)`. -/
lemma legendre_eq {x y : K} (h : W.Equation x y) :
    y ^ 2 = x * (x - 1) * (x - μ) := by
  rw [equation_iff, hW₁, hW₂, hW₃, hW₄, hW₆] at h
  linear_combination h

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(x − 1) = 1` for `v(x) < 1`. -/
lemma valuation_sub_one_eq_one {x : K} (hx : v x < 1) : v (x - 1) = 1 := by
  rw [Valuation.map_sub_eq_of_lt_right _ (by rw [map_one]; exact hx), map_one]

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(x − μ) ≤ max (v x) (v μ)`. -/
lemma valuation_sub_le_max (x : K) : v (x - μ) ≤ max (v x) (v μ) := Valuation.map_sub _ _ _

/-- The `y`-coordinate of a point of the node: `v(y)² = v(x)·v(x − μ)` for `v(x) < 1`. -/
lemma valuation_y_sq {x y : K} (h : W.Equation x y) (hx : v x < 1) :
    v y ^ 2 = v x * v (x - μ) := by
  rw [← map_pow, legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h, map_mul, map_mul,
    valuation_sub_one_eq_one v hx, mul_one]

/-- In the regime `v(μ) < v(x) < 1`, `v(y) = v(x)`. -/
lemma valuation_y_eq {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hμx : v μ < v x) : v y = v x := by
  have h1 := valuation_y_sq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx
  rw [Valuation.map_sub_eq_of_lt_left _ hμx, ← sq] at h1
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp h1

/-- In the regime `v(x) ≤ v(μ)`, `v(y) ≤ v(μ)`. -/
lemma valuation_y_le {x y : K} (h : W.Equation x y) (hx : v x < 1) (hxμ : v x ≤ v μ) :
    v y ≤ v μ := by
  have h1 := valuation_y_sq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx
  have h2 : v y ^ 2 ≤ v μ ^ 2 := by
    rw [h1, sq]
    exact mul_le_mul' hxμ ((valuation_sub_le_max v x).trans (max_le hxμ le_rfl))
  exact (pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h2

/-! ### The middle component: `c = x/μ`, `t = y/μ` -/

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- On the middle component, `t̄ = 0` forces `c̄(c̄ − 1) = 0`: `v(c(c − 1)) < 1` when `v(t) < 1`,
for `t² = c(c − 1)(μc − 1)` with `c` integral and `v(μ) < 1`. -/
lemma valuation_c_mul_sub_one_lt (hμ : v μ < 1) {c t : K} (hc : v c ≤ 1)
    (htsq : t ^ 2 = c * (c - 1) * (μ * c - 1)) (ht : v t < 1) : v (c * (c - 1)) < 1 := by
  have e : c * (c - 1) = μ * c ^ 2 * (c - 1) - t ^ 2 := by
    rw [htsq]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [map_mul, map_mul, map_pow]
    calc v μ * v c ^ 2 * v (c - 1) ≤ v μ * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ zero_le hc
          · exact (Valuation.map_sub _ _ _).trans (max_le hc (by rw [map_one]))
      _ < 1 := by rw [mul_one, mul_one]; exact hμ
  · rw [map_pow]; exact pow_lt_one₀ zero_le ht two_ne_zero

omit hW₁ hW₂ hW₃ hW₄ hW₆ in
/-- `v(1 − 2c) = 1` when `v(c(c − 1)) < 1` and `v(2) = 1`: `(1 − 2c)² = 1 − 4c(c − 1)`. -/
lemma valuation_one_sub_two_mul_eq_one (h2 : v 2 = 1) {c : K} (hg : v (c * (c - 1)) < 1) :
    v (1 - 2 * c) = 1 := by
  have hsq : (1 - 2 * c) ^ 2 = 1 + 4 * (c * (c - 1)) := by ring
  have h4 : v 4 = 1 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have : v ((1 - 2 * c) ^ 2) = 1 := by
    rw [hsq, Valuation.map_add_eq_of_lt_left, map_one]
    rw [map_one, map_mul, h4, one_mul]
    exact hg
  exact valuation_eq_one_of_sq v this

/-! ### The chord through `σ Q` and `−Q` at the node -/

section Node

variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
include hμ h2 hσμ hσ hvσ

omit hσμ in
/-- **Regime `v(μ) < v(x)`**: the slope `L = (σ y + y)/(σ x − x)` of the chord through `σ Q` and
`−Q` has `v(L) > 1`, or is integral with `v(L² + 1) = 1`. -/
lemma slope_branch {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hμx : v μ < v x) (hne : σ x ≠ x) :
    1 < v ((σ y + y) / (σ x - x)) ∨
      (v ((σ y + y) / (σ x - x)) ≤ 1 ∧ v (((σ y + y) / (σ x - x)) ^ 2 + 1) = 1) := by
  have hvx0 : v x ≠ 0 := (lt_of_le_of_lt zero_le hμx).ne'
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hvx0
  -- the branch invariant `t = y/x`, a unit with `t² ≡ −1`
  set t := y / x with ht
  have hty : y = t * x := by rw [ht]; field_simp
  have ht1 : v t = 1 := by
    rw [ht, map_div₀, valuation_y_eq v hW₁ hW₂ hW₃ hW₄ hW₆ h hx hμx, div_self hvx0]
  have htsq : v (t ^ 2 + 1) < 1 := by
    have e : t ^ 2 + 1 = (x - μ) + μ / x := by
      rw [ht]; field_simp
      linear_combination legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · exact (valuation_sub_le_max v x).trans_lt (max_lt hx hμ)
    · rw [map_div₀, div_lt_one₀ (lt_of_le_of_lt zero_le hμx)]; exact hμx
  have hσt : v (σ t - t) < 1 := hσ t ht1.le
  have hσt1 : v (σ t) = 1 := by rw [hvσ]; exact ht1
  have hσy : σ y = σ t * σ x := by rw [hty, map_mul]
  -- `c = σ x / x`, a unit
  set c := σ x / x with hc
  have hc1 : v c = 1 := by
    rw [hc, map_div₀, hvσ, div_self hvx0]
  have hcne : c - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro hcon
    exact hne (by rw [← div_eq_one_iff_eq hx0]; exact hcon)
  have hL : (σ y + y) / (σ x - x) = (c * σ t + t) / (c - 1) := by
    rw [hσy, hty, hc]
    have hc1' : σ x / x - 1 ≠ 0 := hcne
    field_simp [hx0, sub_ne_zero.mpr hne, hc1']
  rw [hL]
  have hc1le : v (c + 1) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hc1.le (by rw [map_one]))
  have hnum_le : v (c * σ t + t) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le (by rw [map_mul, hc1, one_mul, hσt1]) ht1.le)
  by_cases hc' : v (c - 1) < 1
  · left
    have hnum : v (c * σ t + t) = 1 := by
      have e : c * σ t + t = 2 * t + ((c - 1) * t + c * (σ t - t)) := by ring
      have h1 : v ((c - 1) * t + c * (σ t - t)) < 1 := by
        refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
        · rw [map_mul, ht1, mul_one]; exact hc'
        · rw [map_mul, hc1, one_mul]; exact hσt
      have h2t : v (2 * t) = 1 := by rw [map_mul, h2, ht1, mul_one]
      rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [h2t]; exact h1), h2t]
    rw [map_div₀, hnum, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr hcne)))]
    exact hc'
  · right
    have hc1' : v (c - 1) = 1 := by
      refine le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hc1.le (by rw [map_one]))) ?_
      exact not_lt.mp hc'
    have hLint : v ((c * σ t + t) / (c - 1)) ≤ 1 := by
      rw [map_div₀, hc1', div_one]
      exact hnum_le
    refine ⟨hLint, ?_⟩
    -- `L² + 1 = (−4c + A + B)/(c − 1)²` with `A ≡ 0 ≡ B`
    set A := (c * σ t + t) ^ 2 - (c + 1) ^ 2 * t ^ 2 with hA
    set B := (c + 1) ^ 2 * (t ^ 2 + 1) with hB
    have e : ((c * σ t + t) / (c - 1)) ^ 2 + 1 = (-4 * c + (A + B)) / (c - 1) ^ 2 := by
      rw [hA, hB]
      field_simp
      ring
    have h4c : v (-4 * c) = 1 := by
      rw [map_mul, Valuation.map_neg, hc1, mul_one]
      have : (4 : K) = 2 ^ 2 := by norm_num
      rw [this, map_pow, h2, one_pow]
    have hAv : v A < 1 := by
      have e2 : A = c * (σ t - t) * ((c * σ t + t) + (c + 1) * t) := by rw [hA]; ring
      rw [e2, map_mul, map_mul, hc1, one_mul]
      calc v (σ t - t) * v ((c * σ t + t) + (c + 1) * t) ≤ v (σ t - t) * 1 := by
            refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le hnum_le ?_)) _
            rw [map_mul, ht1, mul_one]; exact hc1le
        _ < 1 := by rw [mul_one]; exact hσt
    have hBv : v B < 1 := by
      rw [hB, map_mul, map_pow]
      calc v (c + 1) ^ 2 * v (t ^ 2 + 1) ≤ 1 * v (t ^ 2 + 1) :=
            mul_le_mul_left (pow_le_one₀ zero_le hc1le) _
        _ < 1 := by rw [one_mul]; exact htsq
    have hAB : v (A + B) < 1 := (Valuation.map_add _ _ _).trans_lt (max_lt hAv hBv)
    rw [e, map_div₀, map_pow, hc1', one_pow, div_one,
      Valuation.map_add_eq_of_lt_left _ (by rw [h4c]; exact hAB), h4c]

/-- **Regime `v(x) ≤ v(μ)`** (the middle component): the slope `L = (σ y + y)/(σ x − x)` has
`v(L) > 1`. -/
lemma slope_middle {x y : K} (h : W.Equation x y) (hx : v x < 1)
    (hxμ : v x ≤ v μ) (hne : σ x ≠ x) : 1 < v ((σ y + y) / (σ x - x)) := by
  have hμ0 : μ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hxμ
    exact hne (by rw [(Valuation.zero_iff _).mp (le_antisymm hxμ zero_le), map_zero])
  -- `c = x/μ`, `t = y/μ`, integral, with `t² = c(c − 1)(μc − 1)`
  set c := x / μ with hc
  set t := y / μ with ht
  have hxc : x = μ * c := by rw [hc]; field_simp
  have hyt : y = μ * t := by rw [ht]; field_simp
  have hc1 : v c ≤ 1 := by
    rw [hc, map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
      hμ0)))]
    exact hxμ
  have ht1 : v t ≤ 1 := by
    rw [ht, map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
      hμ0)))]
    exact valuation_y_le v hW₁ hW₂ hW₃ hW₄ hW₆ h hx hxμ
  have htsq : t ^ 2 = c * (c - 1) * (μ * c - 1) := by
    have := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h
    rw [hxc, hyt] at this
    have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
    apply mul_left_cancel₀ hμ2
    linear_combination this
  have hσc : v (σ c - c) < 1 := hσ c hc1
  have hσt : v (σ t - t) < 1 := hσ t ht1
  have hσx : σ x = μ * σ c := by rw [hxc, map_mul, hσμ]
  have hσy : σ y = μ * σ t := by rw [hyt, map_mul, hσμ]
  have hcne : σ c - c ≠ 0 := by
    intro h0
    exact hne (by rw [hσx, hxc, sub_eq_zero.mp h0])
  have hL : (σ y + y) / (σ x - x) = (σ t + t) / (σ c - c) := by
    rw [hσy, hyt, hσx, hxc]
    field_simp
  rw [hL]
  by_cases ht0 : v t = 1
  · have hnum : v (σ t + t) = 1 := by
      have e : σ t + t = 2 * t + (σ t - t) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left, map_mul, h2, ht0, mul_one]
      rw [map_mul, h2, ht0, mul_one]; exact hσt
    rw [map_div₀, hnum, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr hcne)))]
    exact hσc
  · have ht0' : v t < 1 := lt_of_le_of_ne ht1 ht0
    -- `t̄ = 0`, so `c̄ ∈ {0, 1}` and `g(c) = t²` has `g'(c̄) = ±1`
    have hg : v (c * (c - 1)) < 1 := valuation_c_mul_sub_one_lt v hμ hc1 htsq ht0'
    -- the identity `(σt − t)(σt + t) = (σc − c)·h` with `v(h) = 1`
    set hh := μ * (σ c ^ 2 + σ c * c + c ^ 2) - (1 + μ) * (σ c + c) + 1 with hhh
    have hid : (σ t - t) * (σ t + t) = (σ c - c) * hh := by
      have hσsq : σ t ^ 2 = σ c * (σ c - 1) * (μ * σ c - 1) := by
        rw [← map_pow, htsq]
        simp only [map_mul, map_sub, map_one, hσμ]
      rw [hhh]
      linear_combination hσsq - htsq
    have hh1 : v hh = 1 := by
      -- `hh ≡ 1 − 2c ≡ ±1` since `c(c − 1) ≡ 0`
      have e : hh = (1 - 2 * c) + (μ * (σ c ^ 2 + σ c * c + c ^ 2) - μ * (σ c + c) -
          (σ c - c)) := by rw [hhh]; ring
      have h12c : v (1 - 2 * c) = 1 := valuation_one_sub_two_mul_eq_one v h2 hg
      rw [e, Valuation.map_add_eq_of_lt_left, h12c]
      rw [h12c]
      refine (Valuation.map_sub _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt ?_ ?_)) hσc)
      · rw [map_mul]
        calc v μ * v (σ c ^ 2 + σ c * c + c ^ 2) ≤ v μ * 1 := by
              refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le
                ((Valuation.map_add _ _ _).trans (max_le ?_ ?_)) ?_)) _
              · rw [map_pow, hvσ]; exact pow_le_one₀ zero_le hc1
              · rw [map_mul, hvσ]; exact mul_le_one' hc1 hc1
              · rw [map_pow]; exact pow_le_one₀ zero_le hc1
          _ < 1 := by rw [mul_one]; exact hμ
      · rw [map_mul]
        calc v μ * v (σ c + c) ≤ v μ * 1 := by
              refine mul_le_mul_right ((Valuation.map_add _ _ _).trans (max_le ?_ hc1)) _
              rw [hvσ]; exact hc1
          _ < 1 := by rw [mul_one]; exact hμ
    have htne : σ t - t ≠ 0 := by
      intro h0
      rw [h0, zero_mul, eq_comm, mul_eq_zero] at hid
      rcases hid with hid | hid
      · exact hcne hid
      · rw [hid, map_zero] at hh1; exact zero_ne_one hh1
    have hL' : (σ t + t) / (σ c - c) = hh / (σ t - t) := by
      rw [div_eq_div_iff hcne htne]
      linear_combination hid
    rw [hL', map_div₀, hh1, one_div, one_lt_inv₀ (lt_of_le_of_ne zero_le
      (Ne.symm ((Valuation.ne_zero_iff _).mpr htne)))]
    exact hσt

end Node

end Curve

end AbcAdaptation.Reference.Iut.MultKernel
