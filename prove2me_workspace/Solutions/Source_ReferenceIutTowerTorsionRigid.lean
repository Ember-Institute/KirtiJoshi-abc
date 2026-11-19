/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/TorsionRigid.lean
-/
import Solutions.Source_ReferenceIutTowerInertia
import Solutions.Source_ReferenceIutTowerReductionKernel
import Solutions.Source_TripodPlaceUnder
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

section Valuation

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/-- `v(s) = 1` if `v(s²) = 1`. -/
lemma valuation_eq_one_of_sq {s : K} (hs : v (s ^ 2) = 1) : v s = 1 := by
  rw [map_pow] at hs
  rcases lt_trichotomy (v s) 1 with h | h | h
  · exact absurd hs (pow_lt_one₀ zero_le h two_ne_zero).ne
  · exact h
  · exact absurd hs (one_lt_pow₀ h two_ne_zero).ne'

/-- **Rigidity of square roots**: a square root `s` of a `σ`-invariant unit `a` with
`v(σ s − s) < 1` is fixed by `σ` (at `v(2) = 1`). -/
theorem sqrt_fixed_of_valuation_sub_lt (σ : K →+* K) {s a : K} (hs : s ^ 2 = a) (hσa : σ a = a)
    (ha : v a = 1) (h2 : v 2 = 1) (hσ : v (σ s - s) < 1) : σ s = s := by
  have hs' : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, hσa]
  have hmul : (σ s - s) * (σ s + s) = 0 := by linear_combination hs'
  rcases mul_eq_zero.mp hmul with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hvs : v s = 1 := valuation_eq_one_of_sq v (by rw [hs]; exact ha)
    have : σ s - s = -(2 * s) := by linear_combination h
    rw [this, Valuation.map_neg, map_mul, h2, hvs, one_mul] at hσ
    exact lt_irrefl _ hσ

end Valuation

/-- An automorphism of `K/k` fixing a generating set of `K/k` is the identity. -/
theorem algEquiv_eq_one_of_fixed {k K : Type*} [Field k] [Field K] [Algebra k K] {S : Set K}
    (hS : IntermediateField.adjoin k S = ⊤) (σ : K ≃ₐ[k] K) (h : ∀ s ∈ S, σ s = s) : σ = 1 := by
  ext x
  rw [AlgEquiv.one_apply]
  have hx : x ∈ IntermediateField.adjoin k S := by rw [hS]; trivial
  refine IntermediateField.adjoin_induction (F := k) (p := fun y _ => σ y = y) (mem := h)
    (algebraMap := fun y => σ.commutes y) (add := fun y z _ _ hy hz => by rw [map_add, hy, hz])
    (inv := fun y _ hy => by rw [map_inv₀, hy])
    (mul := fun y z _ _ hy hz => by rw [map_mul, hy, hz]) hx

/-! ### The Galois action on the torsion -/

section Torsion

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (W : WeierstrassCurve k)

/-- **Inertia fixes the prime-to-`p` torsion at a good place**: for `σ : K →ₐ[k] K` with
`v(σ x − x) < 1` for all `v`-integral `x`, and an `n`-torsion point `P` of `E(K)` (`n` odd,
`v(n) = 1`) of a curve `y² = x³ + a₂x² + a₄x + a₆` over `k` with `v`-integral coefficients and
`v(Δ) = 1` (at `v(2) = 1`), `σ P = P`. -/
theorem map_eq_self_of_nsmul_eq_zero (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (ha₂ : v (algebraMap k K W.a₂) ≤ 1) (ha₄ : v (algebraMap k K W.a₄) ≤ 1)
    (ha₆ : v (algebraMap k K W.a₆) ≤ 1) (hΔ : v (algebraMap k K W.Δ) = 1) (h2 : v 2 = 1)
    {n : ℕ} (hodd : Odd n)
    (hn : v (n : K) = 1) (σ : K →ₐ[k] K) (hσ : ∀ x : K, v x ≤ 1 → v (σ x - x) < 1)
    (P : (Affine.baseChange W K).Point) (hP : n • P = 0) :
    Point.map (W' := W) (S := k) σ P = P := by
  letI : NeZero (2 : K) := ⟨fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2⟩
  cases P with
  | zero => exact map_zero _
  | some x y h =>
    rw [Point.map_some]
    have hW1 : (Affine.baseChange W K).a₁ = 0 := by
      change algebraMap k K W.a₁ = 0
      rw [ha₁, map_zero]
    have hW3 : (Affine.baseChange W K).a₃ = 0 := by
      change algebraMap k K W.a₃ = 0
      rw [ha₃, map_zero]
    have hW2 : v (Affine.baseChange W K).a₂ ≤ 1 := ha₂
    have hW4 : v (Affine.baseChange W K).a₄ ≤ 1 := ha₄
    have hW6 : v (Affine.baseChange W K).a₆ ≤ 1 := ha₆
    have hWΔ : v (Affine.baseChange W K).Δ = 1 := by
      change v ((W.map (algebraMap k K)).Δ) = 1
      rw [map_Δ]; exact hΔ
    have hPσ : n • Point.some (σ x) (σ y)
        ((Affine.baseChange_nonsingular (W := W) σ.injective x y).mpr h) = 0 := by
      rw [← Point.map_some (W' := W) (S := k) σ h, ← map_nsmul, hP, map_zero]
    obtain ⟨hx, hy⟩ := ReductionKernel.valuation_le_one_of_nsmul_eq_zero v hW1 hW3 hW2 hW4 hW6
      hodd hn h hP
    have hσx : v (σ x) ≤ 1 := by
      have : σ x = (σ x - x) + x := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le (hσ x hx).le hx)
    have hns := JoshiTeich.Act1Scene1.ReductionKernel.nonsingular_reduction_of_Δ v hW1 hW3 hW2 hW4 hW6 hWΔ h2
      ((Affine.baseChange_nonsingular (W := W) σ.injective x y).mpr h).1 hσx
    exact ReductionKernel.eq_of_nsmul_eq_zero_of_congr v hW1 hW3 hW2 hW4 hW6 h2 hodd hn _ h
      hPσ hP (hσ x hx) (hσ y hy) hns

end Torsion

section NumberField

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {v : FinitePlace K} {u : FinitePlace k} (hvu : FinitePlace.LiesOver v u)
include hvu

/-- **Néron–Ogg–Shafarevich**: if `Gal(K/k)` acts faithfully on the `n`-torsion `E(K)[n]` of a
curve `E : y² = x³ + a₂x² + a₄x + a₆` over `k` with `v`-integral coefficients and `v(Δ) = 1`,
`n` odd with `v(n) = 1` and `p ≠ 2`, then `e(v/u) = 1`. -/
theorem relRamIdx_eq_one_of_torsion (W : WeierstrassCurve k) (ha₁ : W.a₁ = 0)
    (ha₃ : W.a₃ = 0)
    (ha₂ : v.maximalIdeal.valuation K (algebraMap k K W.a₂) ≤ 1)
    (ha₄ : v.maximalIdeal.valuation K (algebraMap k K W.a₄) ≤ 1)
    (ha₆ : v.maximalIdeal.valuation K (algebraMap k K W.a₆) ≤ 1)
    (hΔ : v.maximalIdeal.valuation K (algebraMap k K W.Δ) = 1) (h2 : residueChar v ≠ 2)
    {n : ℕ} (hodd : Odd n)
    (hn : v.maximalIdeal.valuation K (n : K) = 1)
    (hgen : ∀ σ : K ≃ₐ[k] K, (∀ P : (Affine.baseChange W K).Point, n • P = 0 →
      Point.map (W' := W) (S := k) (σ : K →ₐ[k] K) P = P) → σ = 1) :
    Tripod.relRamIdx v u = 1 :=
  relRamIdx_eq_one_of_inertia_trivial hvu fun σ hσ => hgen σ fun P hP =>
    map_eq_self_of_nsmul_eq_zero _ W ha₁ ha₃ ha₂ ha₄ ha₆ hΔ (Tripod.valuation_two_eq_one_of_ne h2) hodd
      hn (σ : K →ₐ[k] K) hσ P hP

end NumberField

section Tower

open NumberField

variable {k₀ k K : Type*} [Field k₀] [NumberField k₀] [Field k] [NumberField k] [Field K]
  [NumberField K] [Algebra k₀ k] [Algebra k K] [Algebra k₀ K] [IsScalarTower k₀ k K]
  {v : FinitePlace K} {u : FinitePlace k₀} (hvu : FinitePlace.LiesOver v u)
include hvu

/-- The place of `k` below `v` lies over the place of `k₀ ⊆ k` below `v`. -/
lemma liesOver_placeUnder_of_liesOver : FinitePlace.LiesOver (Tripod.placeUnder (k := k) v) u := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : v.maximalIdeal.asIdeal.LiesOver (Tripod.placeUnder (k := k) v).maximalIdeal.asIdeal :=
    Tripod.liesOver_placeUnder v
  exact Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal _ _

/-- `e(v/u) = e(w/u)·e(v/w)` for `w` the place of `k` below `v`. -/
lemma relRamIdx_eq_mul_placeUnder :
    Tripod.relRamIdx v u =
      Tripod.relRamIdx (Tripod.placeUnder (k := k) v) u *
        Tripod.relRamIdx v (Tripod.placeUnder (k := k) v) := by
  haveI : v.maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal := hvu
  haveI : v.maximalIdeal.asIdeal.LiesOver (Tripod.placeUnder (k := k) v).maximalIdeal.asIdeal :=
    Tripod.liesOver_placeUnder v
  haveI : (Tripod.placeUnder (k := k) v).maximalIdeal.asIdeal.LiesOver u.maximalIdeal.asIdeal :=
    liesOver_placeUnder_of_liesOver hvu
  exact Ideal.ramificationIdx'_algebra_tower' u.maximalIdeal.asIdeal
    (Tripod.placeUnder (k := k) v).maximalIdeal.asIdeal v.maximalIdeal.asIdeal

end Tower

end AbcAdaptation.Reference.Iut
