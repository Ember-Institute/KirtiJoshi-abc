/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original paths Iut/Tower/IntegralTorsion.lean and Iut/Tripod/StableOdd.lean
-/
import Solutions.Source_ReferenceIutTowerReductionKernel
import Solutions.Source_ReferenceIutVariableChangePoint
import ArithmeticTeichmullerSpaces.Act1Scene1.IutGeometricTorsionBasis
import Mathlib.RingTheory.Valuation.Integral

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- A Weierstrass model is integral for the valuation if all five coefficients are integral. -/
def IsIntegralModel (v : Valuation K Γ) (W : WeierstrassCurve K) : Prop :=
  v W.a₁ ≤ 1 ∧ v W.a₂ ≤ 1 ∧ v W.a₃ ≤ 1 ∧ v W.a₄ ≤ 1 ∧ v W.a₆ ≤ 1

lemma IsIntegralModel.b₄ {v : Valuation K Γ} {W : WeierstrassCurve K}
    (h : IsIntegralModel v W) : v W.b₄ ≤ 1 := by
  obtain ⟨h₁, _, h₃, h₄, _⟩ := h
  rw [← Valuation.mem_integer_iff] at h₁ h₃ h₄ ⊢
  exact add_mem (mul_mem (ofNat_mem _ 2) h₄) (mul_mem h₁ h₃)

namespace IntegralTorsion

open WeierstrassCurve.Affine Polynomial
open JoshiTeich.Act1Scene1.IutGeometricTorsion
open scoped Classical

variable (W : WeierstrassCurve K)

private lemma completeSquare_b₂ : (completeSquare W • W).b₂ = W.b₂ := by
  rw [variableChange_b₂]
  simp [completeSquare]

private lemma completeSquare_b₄ : (completeSquare W • W).b₄ = W.b₄ := by
  rw [variableChange_b₄]
  simp [completeSquare]

private lemma completeSquare_b₆ : (completeSquare W • W).b₆ = W.b₆ := by
  rw [variableChange_b₆]
  simp [completeSquare]

private lemma completeSquare_b₈ : (completeSquare W • W).b₈ = W.b₈ := by
  rw [variableChange_b₈]
  simp [completeSquare]

private lemma completeSquare_preΨ' (n : ℕ) : (completeSquare W • W).preΨ' n = W.preΨ' n := by
  simp only [preΨ', Ψ₂Sq, Ψ₃, preΨ₄, completeSquare_b₂, completeSquare_b₄,
    completeSquare_b₆, completeSquare_b₈]

private lemma vcX_completeSquare (x : K) : Anabelian.vcX (completeSquare W) x = x := by
  simp [Anabelian.vcX, completeSquare]

variable {W}
variable (v : Valuation K Γ)

/-- On an integral model, an affine point with nonintegral x coordinate has
nonzero odd multiple when the multiplier is a valuation unit. -/
theorem nsmul_ne_zero_of_one_lt [NeZero (2 : K)] (hW : IsIntegralModel v W)
    {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hx : 1 < v x) :
    n • Point.some x y h ≠ 0 := by
  intro h0
  let C := completeSquare W
  let e := Anabelian.vcEquiv C W
  have h0' : n • e (Point.some x y h) = 0 := by rw [← map_nsmul, h0, map_zero]
  change n • Anabelian.vcEquiv C W (Point.some x y h) = 0 at h0'
  rw [Anabelian.vcEquiv_apply, Anabelian.vcPoint_some] at h0'
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hx' : 1 < v (Anabelian.vcX C x) := by
    change 1 < v (Anabelian.vcX (completeSquare W) x)
    rwa [vcX_completeSquare]
  exact ReductionKernel.nsmul_ne_zero_of_one_lt_of_preΨ'_eq v
    (completeSquare_a₁ W) (completeSquare_a₃ W) h₁ h₂ h₃ h₄ h₆ hodd hn
    (completeSquare_preΨ' W n) ((Anabelian.nonsingular_vc C W x y).mp h) hx' h0'

/-- The affine Weierstrass equation is monic in the y coordinate. -/
private theorem valuation_y_le_one (hW : IsIntegralModel v W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : v x ≤ 1) : v y ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  rw [← Valuation.mem_integer_iff] at h₁ h₂ h₃ h₄ h₆ hx
  let a : v.integer := ⟨W.a₁ * x + W.a₃, add_mem (mul_mem h₁ hx) h₃⟩
  let b : v.integer := ⟨x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆,
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem h₂ (pow_mem hx 2)))
      (mul_mem h₄ hx)) h₆⟩
  apply (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp
  refine ⟨X ^ 2 + (C a * X - C b), monic_X_pow_add ?_, ?_⟩
  · exact (degree_sub_le _ _).trans_lt (max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    change y ^ 2 + ((W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0
    have he := (equation_iff x y).mp h
    linear_combination he

/-- Odd prime-to-residue-characteristic torsion points are integral on an integral model. -/
theorem valuation_le_one_of_nsmul_eq_zero [NeZero (2 : K)] (hW : IsIntegralModel v W)
    {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hP : n • Point.some x y h = 0) :
    v x ≤ 1 ∧ v y ≤ 1 := by
  have hx : v x ≤ 1 :=
    le_of_not_gt fun hlt => nsmul_ne_zero_of_one_lt v hW hodd hn h hlt hP
  exact ⟨hx, valuation_y_le_one v hW h.1 hx⟩

end IntegralTorsion
end AbcAdaptation.Reference.Iut
