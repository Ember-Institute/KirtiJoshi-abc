/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/HemiUnique.lean, `natDegree_eq_one_of_etale`

Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3Count.lean, polynomial root counts
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial
open scoped BigOperators

section Roots

variable {K : Type*} [Field K]

/-- The ramification index of `s` at `w`. -/
noncomputable def polynomialRamificationIdx (s : K[X]) (w : K) : ℕ :=
  rootMultiplicity w (s - C (s.eval w))

/-- The multiplicity: `2` on `E₂`, `1` elsewhere. -/
def hemiMultiplicity [DecidableEq K] (E₂ : Finset K) (w : K) : ℕ := if w ∈ E₂ then 2 else 1

/-- A fiber polynomial of a nonconstant polynomial is nonzero. -/
theorem polynomial_sub_C_ne_zero {s : K[X]} (hs : 0 < s.natDegree) (v : K) : s - C v ≠ 0 := by
  intro h
  have hdeg : (s - C v).natDegree = s.natDegree := natDegree_sub_C
  rw [h, natDegree_zero] at hdeg
  exact (Nat.ne_of_gt hs) hdeg.symm

/-- The roots of the fiber polynomial are precisely the points in that fiber. -/
theorem mem_polynomial_roots_sub_C [DecidableEq K] {s : K[X]} (hs : 0 < s.natDegree)
    {v w : K} :
    w ∈ (s - C v).roots.toFinset ↔ s.eval w = v := by
  rw [Multiset.mem_toFinset, mem_roots (polynomial_sub_C_ne_zero hs v), IsRoot, eval_sub, eval_C,
    sub_eq_zero]

private theorem sum_rootMultiplicity_sub_C [DecidableEq K] [IsAlgClosed K] (s : K[X]) (v : K) :
    ∑ w ∈ (s - C v).roots.toFinset, rootMultiplicity w (s - C v) = s.natDegree := by
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_sub_C]

/-- A nonconstant polynomial has positive ramification index at each point. -/
theorem polynomialRamificationIdx_pos {s : K[X]} (hs : 0 < s.natDegree) (w : K) :
    0 < polynomialRamificationIdx s w := by
  rw [polynomialRamificationIdx, rootMultiplicity_pos (polynomial_sub_C_ne_zero hs _)]
  simp

/-- The ramification index minus one is the root multiplicity of the derivative. -/
theorem polynomialRamificationIdx_sub_one [CharZero K] (s : K[X]) (w : K) :
    polynomialRamificationIdx s w - 1 = rootMultiplicity w (derivative s) := by
  have h := derivative_rootMultiplicity_of_root (p := s - C (s.eval w)) (t := w) (by simp)
  rw [derivative_sub, derivative_C, sub_zero] at h
  rw [polynomialRamificationIdx, h]

/-- In characteristic zero, the derivative counts total finite ramification. -/
theorem sum_rootMultiplicity_polynomial_derivative [DecidableEq K] [IsAlgClosed K]
    [CharZero K] (s : K[X]) :
    ∑ w ∈ (derivative s).roots.toFinset, rootMultiplicity w (derivative s) =
      s.natDegree - 1 := by
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    natDegree_derivative]

/-- The sum of the ramification indices in a fiber is the degree. -/
theorem sum_polynomialRamificationIdx_fiber [DecidableEq K] [IsAlgClosed K]
    {s : K[X]} (hs : 0 < s.natDegree) (v : K) :
    ∑ w ∈ (s - C v).roots.toFinset, polynomialRamificationIdx s w = s.natDegree := by
  rw [Finset.sum_congr rfl fun w hw ↦ by
    rw [polynomialRamificationIdx, (mem_polynomial_roots_sub_C hs).mp hw]]
  exact sum_rootMultiplicity_sub_C s v

end Roots

section Degree

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K]

/-- **A polynomial map étale for the multiplicities `m = 2` on a `3`-element set, on both sides,
has degree `1`.** -/
theorem natDegree_eq_one_of_etale {p : K[X]} (hp : 0 < p.natDegree) {E : Finset K}
    (hE : E.card = 3)
    (h : ∀ w, polynomialRamificationIdx p w * hemiMultiplicity E w = hemiMultiplicity E (p.eval w)) :
    p.natDegree = 1 := by
  set D := p.natDegree
  have hmult : ∀ w, hemiMultiplicity E w = if w ∈ E then 2 else 1 := fun w ↦ rfl
  -- points of `E`: unramified, mapped into `E`
  have hEw : ∀ w ∈ E, polynomialRamificationIdx p w = 1 ∧ p.eval w ∈ E := by
    intro w hw
    have h1 := h w
    have hpos := polynomialRamificationIdx_pos hp w
    rw [hmult w, if_pos hw, hmult] at h1
    split_ifs at h1 with h2
    · exact ⟨by omega, h2⟩
    · omega
  -- points outside `E`
  have hNw : ∀ w, w ∉ E → polynomialRamificationIdx p w = hemiMultiplicity E (p.eval w) := by
    intro w hw
    have h1 := h w
    rwa [hmult w, if_neg hw, mul_one] at h1
  set F : K → Finset K := fun t ↦ (p - C t).roots.toFinset
  have hF : ∀ t w, w ∈ F t ↔ p.eval w = t := fun t w ↦ mem_polynomial_roots_sub_C hp
  set S := E.biUnion F
  have hS : ∀ w, w ∈ S ↔ p.eval w ∈ E := by
    intro w
    simp only [S, Finset.mem_biUnion, hF]
    exact ⟨fun ⟨t, ht, hwt⟩ ↦ hwt ▸ ht, fun hw ↦ ⟨_, hw, rfl⟩⟩
  have hES : E ⊆ S := fun w hw ↦ (hS w).mpr (hEw w hw).2
  have hdisj : (E : Set K).PairwiseDisjoint F := by
    intro v _ v' _ hvv'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    exact hvv' (((hF v w).mp hw).symm.trans ((hF v' w).mp hw'))
  have hsumF : ∀ t, ∑ w ∈ F t, polynomialRamificationIdx p w = D :=
    sum_polynomialRamificationIdx_fiber hp
  -- total ramification over `E`
  have htot : ∑ w ∈ S, polynomialRamificationIdx p w = 3 * D := by
    rw [Finset.sum_biUnion hdisj, Finset.sum_congr rfl fun t _ ↦ hsumF t, Finset.sum_const,
      hE, smul_eq_mul]
  have hsplit : ∑ w ∈ S, polynomialRamificationIdx p w = 3 + 2 * (S \ E).card := by
    rw [← Finset.sum_sdiff hES]
    have e1 : ∑ w ∈ S \ E, polynomialRamificationIdx p w = ∑ _w ∈ S \ E, 2 := by
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      obtain ⟨hwS, hwE⟩ := Finset.mem_sdiff.mp hw
      rw [hNw w hwE, hmult, if_pos ((hS w).mp hwS)]
    have e2 : ∑ w ∈ E, polynomialRamificationIdx p w = ∑ _w ∈ E, 1 :=
      Finset.sum_congr rfl fun w hw ↦ (hEw w hw).1
    rw [e1, e2, Finset.sum_const, Finset.sum_const, hE, smul_eq_mul, smul_eq_mul]
    ring
  -- Riemann–Hurwitz: the critical points are exactly `S \ E`, each simple
  have hderiv0 : derivative p ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hcrit : (derivative p).roots.toFinset = S \ E := by
    ext w
    rw [Multiset.mem_toFinset, mem_roots hderiv0, ← rootMultiplicity_pos hderiv0,
      ← polynomialRamificationIdx_sub_one, Finset.mem_sdiff, hS]
    constructor
    · intro hw
      have hwE : w ∉ E := fun hw' ↦ by rw [(hEw w hw').1] at hw; omega
      refine ⟨?_, hwE⟩
      by_contra hpE
      rw [hNw w hwE, hmult, if_neg hpE] at hw; omega
    · rintro ⟨hpE, hwE⟩
      rw [hNw w hwE, hmult, if_pos hpE]; omega
  have hRH : (S \ E).card = D - 1 := by
    rw [← sum_rootMultiplicity_polynomial_derivative p, hcrit, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    obtain ⟨hwS, hwE⟩ := Finset.mem_sdiff.mp hw
    rw [← polynomialRamificationIdx_sub_one, hNw w hwE, hmult, if_pos ((hS w).mp hwS)]
  omega

end Degree

end AbcAdaptation.Reference.Iut.Anabelian
