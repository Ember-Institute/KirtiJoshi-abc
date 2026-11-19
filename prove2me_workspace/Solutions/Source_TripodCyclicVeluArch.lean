/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicIsogeny.lean (translate_torsion and arch_bound)
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutVeluTracePolynomial
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PointMap
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open WeierstrassCurve NumberField
open JoshiTeich.Act1Scene1.IutCyclicVelu
open JoshiTeich.Act1Scene1.IutTorsionNewton (translatedSum)
open JoshiTeich.Act1Scene1.IutVeluPolynomial (coset_notMem veluRatio_mul)
open JoshiTeich.ReferenceIut.Anabelian (pointMap pointMap_some)
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] {W : WeierstrassCurve K}
variable (H : AddSubgroup W.toAffine.Point) [Fintype H]

/-- The subgroup translates of a point of order two and its half are nonzero
`4ℓ`-torsion points. -/
theorem translate_torsion {ℓ : ℕ} (hH : Nat.card H = ℓ) (hodd : Odd ℓ)
    {T R : W.toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T)
    (Q : H) :
    (T + Q.1 ≠ 0 ∧ (4 * ℓ) • (T + Q.1) = 0) ∧
      (R + Q.1 ≠ 0 ∧ (4 * ℓ) • (R + Q.1) = 0) := by
  have hcard : Fintype.card H = ℓ := (Fintype.card_eq_nat_card).trans hH
  have hT : T ∉ H := notMem_of_add_self H (hcard ▸ hodd) hT0 hT2
  have hR : R ∉ H := fun h => hT (hRT ▸ H.add_mem h h)
  have hT4 : 4 • T = 0 := by
    have h : 2 • T = 0 := by simpa only [two_nsmul] using hT2
    rw [show (4 : ℕ) = 2 * 2 by rfl, mul_nsmul, h, nsmul_zero]
  have hR4 : 4 • R = 0 := by
    have h : 2 • R = T := by simpa only [two_nsmul] using hRT
    rw [show (4 : ℕ) = 2 * 2 by rfl, mul_nsmul, h, two_nsmul, hT2]
  have hQ : ℓ • Q.1 = 0 := by
    have h := congrArg Subtype.val (card_nsmul_eq_zero (x := Q))
    simpa only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero, hcard] using h
  have hQ4 : (4 * ℓ) • Q.1 = 0 := by
    rw [Nat.mul_comm, mul_nsmul, hQ, nsmul_zero]
  refine ⟨⟨fun hz => coset_notMem W H T hT Q (hz ▸ H.zero_mem), ?_⟩,
    ⟨fun hz => coset_notMem W H R hR Q (hz ▸ H.zero_mem), ?_⟩⟩
  · rw [nsmul_add, hQ4, add_zero, mul_nsmul, hT4, nsmul_zero]
  · rw [nsmul_add, hQ4, add_zero, mul_nsmul, hR4, nsmul_zero]

/-- The archimedean Vélu bound for a Legendre model with bounded log parameters. -/
theorem arch_bound [W.IsElliptic] {l : K} (hW : W = legendre l)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hH : Nat.card H = ℓ)
    {c C₀ : ℝ} (hC₀ : LegendreTorsionXBound c C₀)
    (v : InfinitePlace K) (hv₁ : |Real.log (v l)| ≤ c) (hv₂ : |Real.log (v (l - 1))| ≤ c)
    {T R : W.toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    v (veluRatio H T R) * v (xCoordinate T - xCoordinate R) ≤
      2 * ℓ * (C₀ * (4 * ℓ) ^ 2) := by
  have hodd := hℓ.odd_of_ne_two hℓ2
  have hcard : Fintype.card H = ℓ := (Fintype.card_eq_nat_card).trans hH
  have hmul := veluRatio_mul W H two_ne_zero (hcard ▸ hodd) T R hT0 hT2 hRT
  have hN : 1 ≤ 4 * ℓ := Nat.mul_pos (by decide) hℓ.pos
  have hmap : W.map v.embedding = legendre (v.embedding l) := by
    rw [hW]
    ext <;> simp [legendre]
  have hl₁ : |Real.log ‖v.embedding l‖| ≤ c := by
    rwa [InfinitePlace.norm_embedding_eq]
  have hl₂ : |Real.log ‖v.embedding l - 1‖| ≤ c := by
    rwa [← map_one v.embedding, ← map_sub, InfinitePlace.norm_embedding_eq]
  have hterm (S : W.toAffine.Point) (hS0 : S ≠ 0) (hS : (4 * ℓ) • S = 0) :
      v (xCoordinate S) ≤ C₀ * (4 * ℓ) ^ 2 := by
    rcases S with _ | ⟨a, b, h⟩
    · exact (hS0 rfl).elim
    · have hS' : (4 * ℓ) • pointMap W v.embedding (Affine.Point.some a b h) = 0 := by
        rw [← map_nsmul, hS, map_zero]
      rw [pointMap_some] at hS'
      have hbound := hC₀ _ hl₁ hl₂ _ hmap hN _ hS'
      change v a ≤ _
      rw [← InfinitePlace.norm_embedding_eq v a]
      exact_mod_cast hbound
  rw [← map_mul, hmul, translatedSum, ← Finset.sum_sub_distrib,
    ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ Q : H, ‖v.embedding (xCoordinate (T + Q.1) - xCoordinate (R + Q.1))‖
        ≤ ∑ _Q : H, 2 * (C₀ * (4 * ℓ) ^ 2) := by
          refine Finset.sum_le_sum fun Q _ => ?_
          obtain ⟨⟨hTQ0, hTQ⟩, ⟨hRQ0, hRQ⟩⟩ := translate_torsion H hH hodd hT0 hT2 hRT Q
          rw [map_sub]
          refine (norm_sub_le _ _).trans ?_
          rw [InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq, two_mul]
          exact add_le_add (hterm _ hTQ0 hTQ) (hterm _ hRQ0 hRQ)
    _ = 2 * ℓ * (C₀ * (4 * ℓ) ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      ring

end AbcAdaptation.Tripod.Cyclic
