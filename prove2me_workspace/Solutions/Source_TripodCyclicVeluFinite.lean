/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/TorsionNewton.lean (apply_x_le_legendre) and
Iut/Tripod/CyclicIsogeny.lean (apply_xOf_le and crude_bound)
-/
import Solutions.Source_TripodCyclicVeluArch

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open WeierstrassCurve NumberField
open JoshiTeich.Act1Scene1.IutCyclicVelu (veluRatio xCoordinate)
open JoshiTeich.Act1Scene1.IutTorsionNewton (apply_x_le apply_sum_le translatedSum)
open JoshiTeich.Act1Scene1.IutVeluPolynomial (veluRatio_mul)
open JoshiTeich.ReferenceIut.Anabelian (vcEquiv vcX vcY)
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] {W : WeierstrassCurve K}

/-- The Newton bound on a Legendre curve at any finite place. When `1 < w l`,
the change of variables `x = l² X` gives a model with integral coefficients. -/
theorem apply_x_le_legendre [W.IsElliptic] (w : FinitePlace K) {l : K}
    (hW : W = legendre l) (hl0 : l ≠ 0) {n : ℕ} (hn : 1 ≤ n) {x y : K}
    (h : W.toAffine.Nonsingular x y)
    (hP : n • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    w (n : K) ^ 2 * w x ≤ max 1 (w l) ^ 2 := by
  have hW₁ : W.a₁ = 0 := congrArg WeierstrassCurve.a₁ hW
  have hW₂ : W.a₂ = -(1 + l) := congrArg WeierstrassCurve.a₂ hW
  have hW₃ : W.a₃ = 0 := congrArg WeierstrassCurve.a₃ hW
  have hW₄ : W.a₄ = l := congrArg WeierstrassCurve.a₄ hW
  have hW₆ : W.a₆ = 0 := congrArg WeierstrassCurve.a₆ hW
  by_cases hl : w l ≤ 1
  · have h₂ : w W.a₂ ≤ 1 := by
      rw [hW₂, map_neg_eq_map]
      exact (FinitePlace.add_le w _ _).trans (max_le (by simp) hl)
    have h₄ : w W.a₄ ≤ 1 := by simpa only [hW₄] using hl
    have h₆ : w W.a₆ ≤ 1 := by simp [hW₆]
    rw [max_eq_left hl, one_pow]
    exact apply_x_le w hW₁ hW₃ h₂ h₄ h₆ hn h hP
  · have hl : 1 < w l := lt_of_not_ge hl
    let C : VariableChange K := ⟨Units.mk0 l hl0, 0, 0, 0⟩
    have hlinv : w l⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hl.le
    have hC₁ : (C • W).a₁ = 0 := by
      simp [variableChange_a₁, C, hW₁]
    have hC₃ : (C • W).a₃ = 0 := by
      simp [variableChange_a₃, C, hW₃]
    have hC₂ : w (C • W).a₂ ≤ 1 := by
      have hcancel : l⁻¹ ^ 2 * l = l⁻¹ := by
        rw [pow_two, mul_assoc, inv_mul_cancel₀ hl0, mul_one]
      have hcoeff : (C • W).a₂ = -(l⁻¹ ^ 2 + l⁻¹) := by
        calc
          (C • W).a₂ = l⁻¹ ^ 2 * -(1 + l) := by
            simp [variableChange_a₂, C, hW₂]
          _ = _ := by rw [mul_neg, mul_add, mul_one, hcancel]
      rw [hcoeff, map_neg_eq_map]
      refine (FinitePlace.add_le w _ _).trans (max_le ?_ hlinv)
      rw [map_pow]
      exact pow_le_one₀ (apply_nonneg w _) hlinv
    have hC₄ : w (C • W).a₄ ≤ 1 := by
      have hcoeff : (C • W).a₄ = l⁻¹ ^ 3 := by
        calc
          (C • W).a₄ = l⁻¹ ^ 4 * l := by
            simp [variableChange_a₄, C, hW₄]
          _ = _ := by
            rw [show l⁻¹ ^ 4 = l⁻¹ ^ 3 * l⁻¹ from pow_succ _ 3,
              mul_assoc, inv_mul_cancel₀ hl0, mul_one]
      rw [hcoeff, map_pow]
      exact pow_le_one₀ (apply_nonneg w _) hlinv
    have hC₆ : w (C • W).a₆ ≤ 1 := by
      simp [variableChange_a₆, C, hW₆]
    have hP' : n • vcEquiv C W (Affine.Point.some x y h) = 0 := by
      rw [← map_nsmul, hP, map_zero]
    change n • Affine.Point.some (vcX C x) (vcY C x y) _ = 0 at hP'
    have hX : vcX C x = x / l ^ 2 := by simp [vcX, C]
    have hN := apply_x_le w hC₁ hC₃ hC₂ hC₄ hC₆ hn _ hP'
    have hlpos : 0 < w l ^ 2 := pow_pos (lt_trans zero_lt_one hl) _
    rw [hX, map_div₀, map_pow, ← mul_div_assoc, div_le_iff₀ hlpos, one_mul] at hN
    rw [max_eq_right hl.le]
    exact hN

/-- The Vélu bound on a Legendre curve at any finite place. -/
theorem crude_bound [W.IsElliptic] (H : AddSubgroup W.toAffine.Point) [Fintype H]
    {l : K} (hW : W = legendre l) (hl0 : l ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hH : Nat.card H = ℓ) (w : FinitePlace K)
    {T R : W.toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    w (veluRatio H T R) * w (xCoordinate T - xCoordinate R) * w ((4 * ℓ : ℕ) : K) ^ 2 ≤
      max 1 (w l) ^ 2 := by
  have hodd := hℓ.odd_of_ne_two hℓ2
  have hcard : Fintype.card H = ℓ := (Fintype.card_eq_nat_card).trans hH
  have hmul := veluRatio_mul W H two_ne_zero (hcard ▸ hodd) T R hT0 hT2 hRT
  let N : ℕ := 4 * ℓ
  have hN : 1 ≤ N := Nat.mul_pos (by decide) hℓ.pos
  have hpoint (S : W.toAffine.Point) (hS0 : S ≠ 0) (hS : N • S = 0) :
      w ((N : K) ^ 2 * xCoordinate S) ≤ max 1 (w l) ^ 2 := by
    rcases S with _ | ⟨a, b, h⟩
    · exact (hS0 rfl).elim
    · rw [map_mul, map_pow]
      exact apply_x_le_legendre w hW hl0 hN h hS
  have hsum : w ((N : K) ^ 2 * translatedSum H T R) ≤ max 1 (w l) ^ 2 := by
    rw [translatedSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine apply_sum_le w Finset.univ _ (sq_nonneg _) fun Q _ => ?_
    obtain ⟨⟨hTQ0, hTQ⟩, ⟨hRQ0, hRQ⟩⟩ := translate_torsion H hH hodd hT0 hT2 hRT Q
    rw [mul_sub, sub_eq_add_neg]
    refine (FinitePlace.add_le w _ _).trans (max_le (hpoint _ hTQ0 hTQ) ?_)
    rw [map_neg_eq_map]
    exact hpoint _ hRQ0 hRQ
  calc
    w (veluRatio H T R) * w (xCoordinate T - xCoordinate R) * w (N : K) ^ 2 =
        w ((N : K) ^ 2 * translatedSum H T R) := by
      rw [map_mul, map_pow, ← hmul, map_mul, mul_comm (w (N : K) ^ 2)]
    _ ≤ _ := hsum

end AbcAdaptation.Tripod.Cyclic
