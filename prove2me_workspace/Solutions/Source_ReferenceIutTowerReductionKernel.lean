/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/ReductionKernel.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Torsion.EDS
import ArithmeticTeichmullerSpaces.Act1Scene1.ReductionKernel
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ReductionKernel

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open JoshiTeich.Act1Scene1.ReductionKernel (valuation_y_le_one sub_eq_zero_or_one_lt)
open scoped Classical

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ)

/-- `v(f(x)) = v(x)^{deg f}` for `v(x) > 1`, when the coefficients of `f` are integral and its
leading coefficient is a unit. -/
private theorem valuation_eval_eq_pow {f : K[X]} (hf : ∀ i, v (f.coeff i) ≤ 1)
    (hlead : v f.leadingCoeff = 1) {x : K} (hx : 1 < v x) :
    v (f.eval x) = v x ^ f.natDegree := by
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  rw [eval_eq_sum_range, Finset.sum_range_succ]
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, ← leadingCoeff, hlead, one_mul]
  rw [Valuation.map_add_eq_of_lt_right, htop]
  rw [htop]
  refine Valuation.map_sum_lt _ (pow_ne_zero _ hx0) fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow]
  calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul_left (hf i) _
    _ = v x ^ i := one_mul _
    _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi

variable {W : Affine K}

/-- `Ψ₂Sq(x) = (2y)²` on the curve, for `a₁ = a₃ = 0`. -/
private lemma Ψ₂Sq_eval_eq_sq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (h : W.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y) ^ 2 := by
  rw [equation_iff, ha₁, ha₃] at h
  simp only [Ψ₂Sq, b₂, b₄, b₆, ha₁, ha₃, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination 4 * h.symm

/-- The normalized EDS at a point is `Ψₙ'(x)·(2y)^{[n even]}`. -/
private lemma normEDS_eq_eval_preΨ' (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (h : W.Equation x y)
    (n : ℕ) :
    normEDS (2 * y) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n =
      (W.preΨ' n).eval x * if Even n then 2 * y else 1 := by
  rw [normEDS, preNormEDS_ofNat, preΨ', ← coe_evalRingHom, map_preNormEDS', coe_evalRingHom,
    eval_pow, Ψ₂Sq_eval_eq_sq ha₁ ha₃ h]
  simp only [Int.even_coe_nat]
  ring_nf

/-- The coefficients of `Ψₙ'` are integral when the coefficients of `W` are. -/
private lemma valuation_coeff_preΨ'_le_one (ha₁ : v W.a₁ ≤ 1) (ha₂ : v W.a₂ ≤ 1) (ha₃ : v W.a₃ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (n i : ℕ) : v ((W.preΨ' n).coeff i) ≤ 1 := by
  let W₀ : WeierstrassCurve v.integer :=
    ⟨⟨W.a₁, ha₁⟩, ⟨W.a₂, ha₂⟩, ⟨W.a₃, ha₃⟩, ⟨W.a₄, ha₄⟩, ⟨W.a₆, ha₆⟩⟩
  have hW : W = W₀.map (v.integer.subtype) := by
    ext <;> rfl
  rw [hW, map_preΨ', coeff_map]
  exact ((W₀.preΨ' n).coeff i).2

variable [NeZero (2 : K)]

/-- A short model with the same odd division polynomial as an integral model has no
prime-to-residue-characteristic torsion with nonintegral x coordinate. -/
theorem nsmul_ne_zero_of_one_lt_of_preΨ'_eq {W' : Affine K}
    (ha₁ : W'.a₁ = 0) (ha₃ : W'.a₃ = 0) (h₁ : v W.a₁ ≤ 1) (h₂ : v W.a₂ ≤ 1)
    (h₃ : v W.a₃ ≤ 1) (h₄ : v W.a₄ ≤ 1) (h₆ : v W.a₆ ≤ 1) {n : ℕ}
    (hodd : Odd n) (hn : v (n : K) = 1) (hpre : W'.preΨ' n = W.preΨ' n)
    {x y : K} (h : W'.Nonsingular x y) (hx : 1 < v x) :
    n • Point.some x y h ≠ 0 := by
  rw [Ne, JoshiTeich.ReferenceIut.Torsion.smul_eq_zero_iff_eds ha₁ ha₃ h,
    JoshiTeich.ReferenceIut.Torsion.eds, normEDS_eq_eval_preΨ' ha₁ ha₃ h.1,
    if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one, hpre]
  intro h0
  have hn0 : (n : K) ≠ 0 := fun h => by rw [h, map_zero] at hn; exact zero_ne_one hn
  have hlead : v (W.preΨ' n).leadingCoeff = 1 := by
    rw [W.leadingCoeff_preΨ' hn0, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    exact hn
  have := valuation_eval_eq_pow v (valuation_coeff_preΨ'_le_one v h₁ h₂ h₃ h₄ h₆ n) hlead hx
  rw [h0, map_zero] at this
  exact pow_ne_zero _ (zero_lt_one.trans hx).ne' this.symm

/-- The kernel of reduction has no odd prime-to-residue-characteristic torsion
on a short Weierstrass model. -/
theorem nsmul_ne_zero_of_one_lt (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) {n : ℕ} (hodd : Odd n)
    (hn : v (n : K) = 1) {x y : K} (h : W.Nonsingular x y) (hx : 1 < v x) :
    n • Point.some x y h ≠ 0 :=
  nsmul_ne_zero_of_one_lt_of_preΨ'_eq v ha₁ ha₃
    (by rw [ha₁, map_zero]; exact zero_le_one) ha₂
    (by rw [ha₃, map_zero]; exact zero_le_one) ha₄ ha₆ hodd hn rfl h hx

/-- **Prime-to-`p` torsion points are integral**. -/
theorem valuation_le_one_of_nsmul_eq_zero (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) {n : ℕ} (hodd : Odd n)
    (hn : v (n : K) = 1) {x y : K} (h : W.Nonsingular x y) (hP : n • Point.some x y h = 0) :
    v x ≤ 1 ∧ v y ≤ 1 := by
  have hx : v x ≤ 1 := by
    by_contra hcon
    exact nsmul_ne_zero_of_one_lt v ha₁ ha₃ ha₂ ha₄ ha₆ hodd hn h (not_le.mp hcon) hP
  exact ⟨hx, valuation_y_le_one v ha₁ ha₃ ha₂ ha₄ ha₆ h.1 hx⟩

/-- **The reduction map is injective on the prime-to-`p` torsion**: two congruent `n`-torsion
points (`n` odd, `v(n) = 1`) with nonsingular reduction are equal. -/
theorem eq_of_nsmul_eq_zero_of_congr (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₂ : v W.a₂ ≤ 1)
    (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) (h2 : v 2 = 1) {n : ℕ}
    (hodd : Odd n) (hn : v (n : K) = 1) {x₁ y₁ x₂ y₂ : K} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hP : n • Point.some x₁ y₁ h₁ = 0)
    (hQ : n • Point.some x₂ y₂ h₂ = 0) (hx : v (x₁ - x₂) < 1) (hy : v (y₁ - y₂) < 1)
    (hns : v (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = 1 ∨ v (2 * y₁) = 1) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  obtain ⟨hx₁, hy₁⟩ := valuation_le_one_of_nsmul_eq_zero v ha₁ ha₃ ha₂ ha₄ ha₆ hodd hn h₁ hP
  obtain ⟨hx₂, hy₂⟩ := valuation_le_one_of_nsmul_eq_zero v ha₁ ha₃ ha₂ ha₄ ha₆ hodd hn h₂ hQ
  rcases sub_eq_zero_or_one_lt v ha₁ ha₃ ha₂ h2 h₁ h₂ hx₁ hy₁ hx₂ hy₂ hx hy hns with
    h0 | ⟨x, y, h, hsub, hx'⟩
  · exact sub_eq_zero.mp h0
  · exfalso
    have hD : n • (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) = 0 := by
      rw [nsmul_sub, hP, hQ, sub_zero]
    rw [hsub] at hD
    exact nsmul_ne_zero_of_one_lt v ha₁ ha₃ ha₂ ha₄ ha₆ hodd hn h hx' hD

end AbcAdaptation.Reference.Iut.ReductionKernel
