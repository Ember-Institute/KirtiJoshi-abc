/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original path Iut/Tower/MultiplicativeKernel.lean
-/
import Solutions.Source_TripodMultiplicativeDifference
import Mathlib.Tactic.Abel

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

/-! ### Rigidity on `E₀` and unipotence -/

section Unipotent

variable (σ : K →+* K) (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
  (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
  {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1)
  (φ : W.Point →+ W.Point)
  (hφ : ∀ (x y : K) (h : W.Nonsingular x y),
    ∃ h' : W.Nonsingular (σ x) (σ y), φ (Point.some x y h) = Point.some (σ x) (σ y) h')
include hμ h2 hσμ hσ hvσ hodd hn hφ

omit hσμ hvσ in
/-- **Inertia fixes the prime-to-`p` torsion of `E₀`**: an `n`-torsion point `(x, y)` with
`1 ≤ v(x)` is fixed by `φ`. -/
theorem map_eq_self_of_one_le {x y : K} (h : W.Nonsingular x y)
    (hQ : n • Point.some x y h = 0) (hx : 1 ≤ v x) : φ (Point.some x y h) = Point.some x y h := by
  letI : NeZero (2 : K) := ⟨fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2⟩
  obtain ⟨h', hφ'⟩ := hφ x y h
  rw [hφ']
  have hW2 : v W.a₂ ≤ 1 := by
    rw [hW₂, Valuation.map_neg]
    exact (Valuation.map_add _ _ _).trans (max_le (by rw [map_one]) hμ.le)
  have hW4 : v W.a₄ ≤ 1 := by rw [hW₄]; exact hμ.le
  have hW6 : v W.a₆ ≤ 1 := by rw [hW₆, map_zero]; exact zero_le_one
  obtain ⟨hx1, hy1⟩ := ReductionKernel.valuation_le_one_of_nsmul_eq_zero v hW₁ hW₃ hW2 hW4 hW6
    hodd hn h hQ
  have hxu : v x = 1 := le_antisymm hx1 hx
  -- nonsingular reduction: `x̄ ≠ 0`
  have hns : v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 ∨ v (2 * y) = 1 := by
    by_cases hy : v (2 * y) = 1
    · exact Or.inr hy
    · left
      have hy' : v y < 1 := by
        rw [map_mul, h2, one_mul] at hy
        exact lt_of_le_of_ne hy1 hy
      -- `y² = x(x − 1)(x − μ)` with `v x = 1`, `v(x − μ) = 1`, so `v(x − 1) < 1`
      have hxμ : v (x - μ) = 1 := by
        rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hxu]; exact hμ), hxu]
      have hx1' : v (x - 1) < 1 := by
        have e := legendre_eq hW₁ hW₂ hW₃ hW₄ hW₆ h.1
        have : v (y ^ 2) = v (x - 1) := by
          rw [e, map_mul, map_mul, hxu, hxμ, one_mul, mul_one]
        rw [map_pow] at this
        rw [← this]
        exact pow_lt_one₀ zero_le hy' two_ne_zero
      -- `f'(x) = 1 + (3(x² − 1) − 2(x − 1) − 2μx + μ)`
      have e : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ =
          1 + (3 * ((x - 1) * (x + 1)) - 2 * (x - 1) - 2 * (μ * x) + μ) := by
        rw [hW₂, hW₄]; ring
      rw [e, Valuation.map_add_eq_of_lt_left, map_one]
      rw [map_one]
      have h3 : v (3 : K) ≤ 1 := valuation_natCast_le_one v 3
      have hx1le : v (x + 1) ≤ 1 :=
        (Valuation.map_add _ _ _).trans (max_le hx1 (by rw [map_one]))
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt
        (max_lt ((Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)) ?_)) hμ)
      · rw [map_mul, map_mul]
        calc v 3 * (v (x - 1) * v (x + 1)) ≤ 1 * (v (x - 1) * 1) := by gcongr
          _ < 1 := by rw [one_mul, mul_one]; exact hx1'
      · rw [map_mul, h2, one_mul]; exact hx1'
      · rw [map_mul, map_mul, h2, one_mul, hxu, mul_one]; exact hμ
  have hQ' : n • Point.some (σ x) (σ y) h' = 0 := by
    rw [← hφ', ← map_nsmul, hQ, map_zero]
  exact (ReductionKernel.eq_of_nsmul_eq_zero_of_congr v hW₁ hW₃ hW2 hW4 hW6 h2 hodd hn h h'
    hQ hQ' (by rw [Valuation.map_sub_swap]; exact hσ x hx1)
    (by rw [Valuation.map_sub_swap]; exact hσ y hy1) hns).symm

/-- **Unipotence**: `φ(φ Q − Q) = φ Q − Q` for every `n`-torsion point `Q`. -/
theorem map_sub_map_eq_self (Q : W.Point) (hQ : n • Q = 0) : φ (φ Q - Q) = φ Q - Q := by
  cases Q with
  | zero =>
    change φ (φ 0 - 0) = φ 0 - 0
    rw [map_zero, sub_zero, map_zero]
  | some x y h =>
    by_cases hx : v x < 1
    · obtain ⟨h', hφ'⟩ := hφ x y h
      rw [hφ']
      rcases sub_eq_zero_or_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ h h' hx with
        h0 | ⟨x', y', h'', hsub, hx'⟩
      · rw [h0, map_zero]
      · rw [hsub]
        have hR : n • Point.some x' y' h'' = 0 := by
          rw [← hsub, nsmul_sub, hQ, ← hφ', ← map_nsmul, hQ, map_zero, sub_zero]
        exact map_eq_self_of_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hodd hn φ hφ h'' hR hx'
    · have := map_eq_self_of_one_le v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσ hodd hn φ hφ h hQ
        (not_lt.mp hx)
      rw [this, sub_self, map_zero]

omit hW₁ hW₂ hW₃ hW₄ hW₆ hμ h2 hσμ hσ hvσ hodd hn hφ in
/-- `φ^k Q = Q + k(φ Q − Q)` when `φ` fixes `φ Q − Q`. -/
lemma iterate_eq_add_nsmul {G : Type*} [AddCommGroup G] (ψ : G →+ G) {Q : G}
    (hQ : ψ (ψ Q - Q) = ψ Q - Q) (k : ℕ) : ψ^[k] Q = Q + k • (ψ Q - Q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hQ, succ_nsmul]
    abel

/-- **`φ^n Q = Q`** for every `n`-torsion point `Q`. -/
theorem iterate_map_eq_self (Q : W.Point) (hQ : n • Q = 0) : (⇑φ)^[n] Q = Q := by
  rw [iterate_eq_add_nsmul φ (map_sub_map_eq_self v hW₁ hW₂ hW₃ hW₄ hW₆ σ hμ h2 hσμ hσ hvσ hodd
    hn φ hφ Q hQ), nsmul_sub, ← map_nsmul, hQ, map_zero, sub_zero, add_zero]

end Unipotent

end Curve

end AbcAdaptation.Reference.Iut.MultKernel
