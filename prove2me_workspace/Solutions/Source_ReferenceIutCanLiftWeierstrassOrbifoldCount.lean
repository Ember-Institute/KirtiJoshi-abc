/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/R3Count.lean, the cubic symmetries,
and Oka/Uniformization/R3.lean, the polynomial conclusion of le_pmDeck_or.
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialOrbifoldCount
import Solutions.Source_ReferenceIutCanLiftPolynomialRigidity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial WeierstrassCurve

/-- A quadratic polynomial vanishing at three distinct points has all coefficients zero. -/
private theorem quadratic_eq_zero {K : Type*} [Field K] {α β γ : K} {E : Finset K}
    (hE : E.card = 3) (h : ∀ w ∈ E, α * w ^ 2 + β * w + γ = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hE
  have hx := h x (by simp)
  have hy := h y (by simp)
  have hz := h z (by simp)
  have hxy' : α * (x + y) + β = 0 := by
    have : (x - y) * (α * (x + y) + β) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxy)
  have hxz' : α * (x + z) + β = 0 := by
    have : (x - z) * (α * (x + z) + β) = 0 := by linear_combination hx - hz
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxz)
  have hα : α = 0 := by
    have : (y - z) * α = 0 := by linear_combination hxy' - hxz'
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hyz)
  have hβ : β = 0 := by
    rw [hα] at hxy'
    linear_combination hxy'
  refine ⟨hα, hβ, ?_⟩
  rw [hα, hβ] at hx
  linear_combination hx

variable {W : WeierstrassCurve ℂ} [W.IsElliptic]

omit [W.IsElliptic] in
private theorem twoTorsion_cubic_eq_zero {w : ℂ} (hw : w ∈ E₂ W) :
    4 * w ^ 3 + W.b₂ * w ^ 2 + 2 * W.b₄ * w + W.b₆ = 0 := by
  rw [E₂, Multiset.mem_toFinset, mem_roots (tq_ne_zero (W := W)), IsRoot, tq_eval] at hw
  exact hw

private theorem c₆_eq_zero_of_reflection {c : ℂ} (hreflect : ∀ w ∈ E₂ W, 2 * c - w ∈ E₂ W) :
    W.c₆ = 0 := by
  obtain ⟨ha, -, hc⟩ := quadratic_eq_zero
    (α := 24 * c + 2 * W.b₂) (β := -48 * c ^ 2 - 4 * W.b₂ * c)
    (γ := 32 * c ^ 3 + 4 * W.b₂ * c ^ 2 + 4 * W.b₄ * c + 2 * W.b₆)
    (card_E₂ (W := W)) fun w hw ↦ by
      have h₁ := twoTorsion_cubic_eq_zero hw
      have h₂ := twoTorsion_cubic_eq_zero (hreflect w hw)
      linear_combination h₁ + h₂
  have hb₂ : W.b₂ = -12 * c := by linear_combination ha / 2
  rw [hb₂] at hc
  rw [WeierstrassCurve.c₆, hb₂]
  linear_combination -108 * hc

private theorem c₄_eq_zero_of_cube {c ρ : ℂ} (hcube : ∀ w ∈ E₂ W, (w - c) ^ 3 = ρ) :
    W.c₄ = 0 := by
  obtain ⟨ha, hb, -⟩ := quadratic_eq_zero
    (α := W.b₂ + 12 * c) (β := 2 * W.b₄ - 12 * c ^ 2)
    (γ := W.b₆ + 4 * ρ + 4 * c ^ 3) (card_E₂ (W := W)) fun w hw ↦ by
      linear_combination twoTorsion_cubic_eq_zero hw - 4 * hcube w hw
  have hb₂ : W.b₂ = -12 * c := by linear_combination ha
  rw [WeierstrassCurve.c₄, hb₂]
  linear_combination -12 * hb

/-- Away from the two exceptional j-invariants, a nonconstant polynomial with
fiberwise constant weighted ramification for the two-torsion roots is injective. -/
theorem polynomial_eval_injective_of_hemi_orbifold {s : ℂ[X]} (hs : 0 < s.natDegree)
    (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728)
    (h : ∀ w w', s.eval w = s.eval w' →
      polynomialRamificationIdx s w * hemiMultiplicity (E₂ W) w =
        polynomialRamificationIdx s w' * hemiMultiplicity (E₂ W) w') :
    Function.Injective s.eval := by
  have hD : s.natDegree = 1 := by
    rcases polynomial_orbifold_count hs (card_E₂ (W := W)) h with hD | ⟨_, c, hc⟩ | ⟨_, c, ρ, hc⟩
    · exact hD
    · exfalso
      apply hj₁₇₂₈
      have hc₆ := c₆_eq_zero_of_reflection hc
      have hrel := (W.c_relation).symm
      rw [hc₆, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hrel
      rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
        mul_comm, ← div_eq_mul_inv, div_eq_iff W.isUnit_Δ.ne_zero]
      exact hrel
    · exact (hj₀ (W.j_eq_zero (c₄_eq_zero_of_cube hc))).elim
  have ha : s.coeff 1 ≠ 0 := by
    have hlead := leadingCoeff_ne_zero.mpr (show s ≠ 0 by rintro rfl; simp at hs)
    rwa [leadingCoeff, hD] at hlead
  intro w w' hww'
  rw [eq_X_add_C_of_natDegree_le_one hD.le] at hww'
  simp only [eval_add, eval_mul, eval_C, eval_X, add_left_inj] at hww'
  exact mul_left_cancel₀ ha hww'

end AbcAdaptation.Reference.Iut.Anabelian
