/-
Adaptation provenance: original accepted source AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/Legendre.lean
Source AST parser: ci-018604-c1b9825d. Full actual proof closure: ci-018611-e639140c.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace AbcAdaptation.Tripod
open WeierstrassCurve

section Invariants
variable {R : Type*} [CommRing R] (l : R)

@[simp] private lemma legendre_a₁ : (legendre l).a₁ = 0 := rfl

@[simp] private lemma legendre_a₂ : (legendre l).a₂ = -(1 + l) := rfl

@[simp] private lemma legendre_a₃ : (legendre l).a₃ = 0 := rfl

@[simp] private lemma legendre_a₄ : (legendre l).a₄ = l := rfl

@[simp] private lemma legendre_a₆ : (legendre l).a₆ = 0 := rfl

private lemma legendre_b₂ : (legendre l).b₂ = -4 * (1 + l) := by
  simp only [b₂, legendre_a₁, legendre_a₂]; ring

private lemma legendre_b₄ : (legendre l).b₄ = 2 * l := by
  simp only [b₄, legendre_a₁, legendre_a₃, legendre_a₄]; ring

private lemma legendre_b₆ : (legendre l).b₆ = 0 := by
  simp only [b₆, legendre_a₃, legendre_a₆]; ring

private lemma legendre_b₈ : (legendre l).b₈ = -l ^ 2 := by
  simp only [b₈, legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆]; ring

/-- `Δ(E_λ) = 16 λ² (λ − 1)²`. -/
private lemma legendre_Δ : (legendre l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [Δ, legendre_b₂, legendre_b₄, legendre_b₆, legendre_b₈]; ring

end Invariants

section Field
variable {K : Type*} [Field K]

/-- `E_λ` is an elliptic curve for `λ ∉ {0, 1}` in a field of characteristic `≠ 2`. -/
theorem legendre_isElliptic [NeZero (2 : K)] {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    (legendre l).IsElliptic := by
  refine ⟨?_⟩
  rw [legendre_Δ, isUnit_iff_ne_zero]
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr h1))

end Field
end AbcAdaptation.Tripod
