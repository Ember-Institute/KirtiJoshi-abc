/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableTwo.lean
-/
import Solutions.Source_ReferenceIutStableModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve

/-! ## Flex points -/

section Flex

variable {K : Type*} [Field K]

/-- **Flex data** of a Weierstrass curve `W` over a field: an affine point `(x, y)` on `W` which
is not `2`-torsion (`D := 2y + a₁x + a₃ ≠ 0`), and the slope `λ = N/D` of the tangent line at
`(x, y)` (`N := 3x² + 2a₂x + a₄ − a₁y`), subject to `λ² + a₁λ − a₂ − 3x = 0`, which says
`x(2P) = x(P)`, i.e. `2P = −P`, i.e. `3P = 0`. -/
structure FlexData (W : WeierstrassCurve K) where
  /-- The `x`-coordinate. -/
  x : K
  /-- The `y`-coordinate. -/
  y : K
  /-- The tangent slope. -/
  lam : K
  /-- The point lies on `W`. -/
  equation : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  /-- The point is not `2`-torsion. -/
  ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0
  /-- `λ · D = N`. -/
  lam_mul : lam * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  /-- `x(2P) = x(P)`. -/
  lam_sq : lam ^ 2 + W.a₁ * lam - W.a₂ - 3 * x = 0

variable {W : WeierstrassCurve K}

/-- The `x`-coordinate of a flex point is a root of the `3`-division polynomial
`ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`. -/
lemma FlexData.psi3 (d : FlexData W) :
    3 * d.x ^ 4 + W.b₂ * d.x ^ 3 + 3 * W.b₄ * d.x ^ 2 + 3 * W.b₆ * d.x + W.b₈ = 0 := by
  have h1 := d.lam_mul
  have h2 := d.lam_sq
  have h3 := d.equation
  simp only [b₂, b₄, b₆, b₈]
  linear_combination (-(2 * d.y + W.a₁ * d.x + W.a₃) ^ 2) * h2 +
    (d.lam * (2 * d.y + W.a₁ * d.x + W.a₃) + (3 * d.x ^ 2 + 2 * W.a₂ * d.x + W.a₄ - W.a₁ * d.y) +
      W.a₁ * (2 * d.y + W.a₁ * d.x + W.a₃)) * h1 +
    (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * d.x)) * h3

section Point

variable [DecidableEq K]

/-- An affine point `P` with `3P = 0` is not `2`-torsion and satisfies `x(2P) = x(P)`. -/
private lemma flex_of_three_nsmul {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    y ≠ W.toAffine.negY x y ∧ W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
  have h2 : 2 • (Affine.Point.some x y h : W.toAffine.Point) = -Affine.Point.some x y h := by
    rw [eq_neg_iff_add_eq_zero, ← succ_nsmul]
    exact hP
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    rw [two_nsmul, Affine.Point.add_self_of_Y_eq hy] at h2
    exact Affine.Point.some_ne_zero h (neg_eq_zero.mp h2.symm)
  refine ⟨hy, ?_⟩
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hy, Affine.Point.neg_some,
    Affine.Point.some.injEq] at h2
  exact h2.1

/-- The flex data of an affine point of order `3`. -/
noncomputable def FlexData.ofPoint {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) : FlexData W :=
  have hy := (flex_of_three_nsmul h hP).1
  have hD : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hD
    apply hy
    simp only [Affine.negY]
    linear_combination hD
  { x := x
    y := y
    lam := W.toAffine.slope x x y y
    equation := (Affine.equation_iff _ _).mp h.1
    ne := hD
    lam_mul := by
      rw [Affine.slope_of_Y_ne rfl hy]
      have e : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
        simp only [Affine.negY]
        ring
      rw [e]
      exact div_mul_cancel₀ _ hD
    lam_sq := by
      have := (flex_of_three_nsmul h hP).2
      simp only [Affine.addX] at this
      linear_combination this }

@[simp] lemma FlexData.ofPoint_x {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : 3 • (Affine.Point.some x y h : W.toAffine.Point) = 0) : (FlexData.ofPoint h hP).x = x :=
  rfl

end Point

/-- **Transport of flex data along a change of variables** `x = u²X + r`, `y = u³Y + u²sX + t`:
the point `(X, Y) = (u⁻²(x − r), u⁻³(y − s(x − r) − t))` with tangent slope `u⁻¹(λ − s)`. -/
def FlexData.variableChange (d : FlexData W) (C : VariableChange K) : FlexData (C • W) where
  x := (C.u : K)⁻¹ ^ 2 * (d.x - C.r)
  y := (C.u : K)⁻¹ ^ 3 * (d.y - C.s * (d.x - C.r) - C.t)
  lam := (C.u : K)⁻¹ * (d.lam - C.s)
  equation := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 6 * d.equation
  ne := by
    simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
    have e : 2 * ((C.u : K)⁻¹ ^ 3 * (d.y - C.s * (d.x - C.r) - C.t)) +
        (C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * ((C.u : K)⁻¹ ^ 2 * (d.x - C.r)) +
        (C.u : K)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) =
        (C.u : K)⁻¹ ^ 3 * (2 * d.y + W.a₁ * d.x + W.a₃) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero C.u.ne_zero)) d.ne
  lam_mul := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 4 * d.lam_mul
  lam_sq := by
    simp only [variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
    linear_combination (C.u : K)⁻¹ ^ 2 * d.lam_sq

@[simp] lemma FlexData.variableChange_x (d : FlexData W) (C : VariableChange K) :
    (d.variableChange C).x = (C.u : K)⁻¹ ^ 2 * (d.x - C.r) := rfl

/-- **The normal form of a flex**: the change of variables `x = X + x(P)`, `y = Y + λX + y(P)`
moves the flex point to the origin with horizontal tangent, giving the model
`y² + (a₁ + 2λ)xy + (a₃ + a₁x(P) + 2y(P))y = x³`. -/
lemma FlexData.variableChange_eq (d : FlexData W) :
    (⟨1, d.x, d.lam, d.y⟩ : VariableChange K) • W =
      ⟨W.a₁ + 2 * d.lam, 0, W.a₃ + d.x * W.a₁ + 2 * d.y, 0, 0⟩ := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one]
  · ring
  · linear_combination -d.lam_sq
  · ring
  · linear_combination -d.lam_mul
  · linear_combination -d.equation

end Flex

/-! ## Integrality of roots -/

section Integrality

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/-- A root of a monic quadratic with integral coefficients is integral. -/
private lemma valuation_le_one_of_quadratic {x a b : K} (h : x ^ 2 + a * x + b = 0) (ha : v a ≤ 1)
    (hb : v b ≤ 1) : v x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  have h1 : v (a * x + b) < v (x ^ 2) := by
    rw [map_pow]
    refine lt_of_le_of_lt (Valuation.map_add v _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_of_le_one_left zero_le ha).trans_lt (lt_self_pow₀ hx (by norm_num))
    · exact hb.trans_lt (one_lt_pow₀ hx (by norm_num))
  have h2 := Valuation.map_add_eq_of_lt_left v h1
  rw [← add_assoc, h, map_zero, map_pow] at h2
  exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx)) h2.symm

/-- A root of `3x⁴ + c₃x³ + c₂x² + c₁x + c₀` with integral coefficients is integral when `3` is
a unit. -/
lemma valuation_le_one_of_quartic (h3 : v 3 = 1) {x c₃ c₂ c₁ c₀ : K}
    (h : 3 * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0) (hc₃ : v c₃ ≤ 1) (hc₂ : v c₂ ≤ 1)
    (hc₁ : v c₁ ≤ 1) (hc₀ : v c₀ ≤ 1) : v x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  have hx1 : 1 ≤ v x := hx.le
  have key : ∀ (c : K) (n : ℕ), v c ≤ 1 → n ≤ 3 → v (c * x ^ n) ≤ v x ^ 3 := by
    intro c n hc hn
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le hc).trans (pow_le_pow_right₀ hx1 hn)
  have h1 : v (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) < v (3 * x ^ 4) := by
    rw [map_mul, h3, one_mul, map_pow]
    refine lt_of_le_of_lt ?_ (pow_lt_pow_right₀ hx (by norm_num : 3 < 4))
    refine v.map_add_le (v.map_add_le (v.map_add_le ?_ ?_) ?_) ?_
    · exact key c₃ 3 hc₃ le_rfl
    · exact key c₂ 2 hc₂ (by norm_num)
    · simpa using key c₁ 1 hc₁ (by norm_num)
    · simpa using key c₀ 0 hc₀ (by norm_num)
  have h2 := Valuation.map_add_eq_of_lt_left v h1
  have e : 3 * x ^ 4 + (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) =
      3 * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ := by ring
  rw [e, h, map_zero, map_mul, h3, one_mul, map_pow] at h2
  exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx)) h2.symm

/-- On an integral model, the `x`-coordinate of a flex point is integral (for `v(3) = 1`). -/
lemma FlexData.valuation_x_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (h3 : v 3 = 1) : v d.x ≤ 1 :=
  valuation_le_one_of_quartic v h3 d.psi3 hW.b₂ (by rw [map_mul, h3, one_mul]; exact hW.b₄)
    (by rw [map_mul, h3, one_mul]; exact hW.b₆) hW.b₈

/-- On an integral model, the `y`-coordinate of a flex point with integral `x`-coordinate is
integral. -/
lemma FlexData.valuation_y_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (hx : v d.x ≤ 1) : v d.y ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  refine valuation_le_one_of_quadratic v (a := W.a₁ * d.x + W.a₃)
    (b := -(d.x ^ 3 + W.a₂ * d.x ^ 2 + W.a₄ * d.x + W.a₆)) (by linear_combination d.equation) ?_ ?_
  · rw [← Valuation.mem_integer_iff] at *
    exact add_mem (mul_mem h₁ hx) h₃
  · rw [← Valuation.mem_integer_iff] at *
    exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2)))
      (mul_mem h₄ hx)) h₆)

/-- On an integral model, the tangent slope at a flex point with integral `x`-coordinate is
integral. -/
lemma FlexData.valuation_lam_le_one {W : WeierstrassCurve K} (d : FlexData W)
    (hW : IsIntegralModel v W) (hx : v d.x ≤ 1) : v d.lam ≤ 1 := by
  obtain ⟨h₁, h₂, -, -, -⟩ := hW
  refine valuation_le_one_of_quadratic v (a := W.a₁) (b := -W.a₂ - 3 * d.x)
    (by linear_combination d.lam_sq) h₁ ?_
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (neg_mem h₂) (mul_mem (ofNat_mem _ 3) hx)

end Integrality

end AbcAdaptation.Reference.Iut
