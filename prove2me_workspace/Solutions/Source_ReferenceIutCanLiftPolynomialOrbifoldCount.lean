/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3Count.lean
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
For a polynomial with three points of multiplicity two, assume that ramification
index times multiplicity is constant on each fiber. The sum of derivative
multiplicities restricts the critical and marked values and gives the symmetry
of the marked set in degrees two and three.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial
open scoped BigOperators

section FiberArithmetic

variable {ι : Type*} [DecidableEq ι]

private theorem positive_defect_shape {M n a D : ℕ} (hM : 2 ≤ M)
    (hE : 0 < a → Even M) (hD : 2 * D = 2 * M * n + M * a)
    (hpos : 0 < (M - 2) * (2 * n + a)) (hbound : (M - 2) * (2 * n + a) ≤ 2) :
    (M - 2) * (2 * n + a) = 2 ∧
      ((D = 2 ∧ n = 0 ∧ a = 1) ∨ (D = 3 ∧ n = 1 ∧ a = 0)) := by
  have hw : 1 ≤ 2 * n + a := by
    by_contra hw
    have hz : 2 * n + a = 0 := by omega
    simp [hz] at hpos
  have hle : M - 2 ≤ (M - 2) * (2 * n + a) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M - 2) hw
  have hne : M ≠ 2 := by
    rintro rfl
    simp at hpos
  rcases (by omega : M = 3 ∨ M = 4) with rfl | rfl
  · norm_num at hpos hbound
    have ha : a = 0 := by
      by_contra ha
      obtain ⟨r, hr⟩ := hE (Nat.pos_of_ne_zero ha)
      omega
    have hn : n = 1 := by omega
    rw [hn, ha] at hD ⊢
    exact ⟨by decide, Or.inr ⟨by omega, rfl, rfl⟩⟩
  · norm_num at hpos hbound
    have hw : 2 * n + a = 1 := by omega
    have hn : n = 0 := by omega
    have ha : a = 1 := by omega
    rw [hw]
    rw [hn, ha] at hD
    exact ⟨by decide, Or.inl ⟨by omega, hn, ha⟩⟩

/-- Here n counts the unmarked points and a counts the marked points in each fiber. -/
private theorem two_special_fibers {D : ℕ} (hD₂ : 2 ≤ D) {V : Finset ι} {M n a : ι → ℕ}
    (hM : ∀ v ∈ V, 2 ≤ M v) (hF : ∀ v ∈ V, 1 ≤ n v + a v)
    (hEven : ∀ v ∈ V, 0 < a v → Even (M v))
    (hD : ∀ v ∈ V, 2 * D = 2 * M v * n v + M v * a v)
    (hRH : ∑ v ∈ V, ((D : ℤ) - n v - a v) = (D : ℤ) - 1)
    (hA : ∑ v ∈ V, a v = 3) :
    ∃ i j, V = {i, j} ∧
      ((D = 2 ∧ n i = 0 ∧ a i = 1 ∧ n j = 0 ∧ a j = 2) ∨
        (D = 3 ∧ n i = 1 ∧ a i = 0 ∧ a j = 3)) := by
  let T (v : ι) : ℕ := (M v - 2) * (2 * n v + a v)
  have hT : ∀ v ∈ V, (T v : ℤ) = 2 * D - 4 * n v - 2 * a v := by
    intro v hv
    have hd : (2 * D : ℤ) = 2 * M v * n v + M v * a v := by
      exact_mod_cast hD v hv
    dsimp only [T]
    push_cast [Nat.cast_sub (hM v hv)]
    linear_combination -hd
  have hsumT : ∑ v ∈ V, (T v : ℤ) = (4 - 2 * V.card) * D + 2 := by
    rw [Finset.sum_congr rfl hT]
    have hA' : ∑ v ∈ V, (a v : ℤ) = 3 := by exact_mod_cast hA
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      at hRH ⊢
    linear_combination 4 * hRH + 2 * hA'
  have hk₂ : V.card ≤ 2 := by
    by_contra hk
    have hcard : (3 : ℤ) ≤ V.card := by exact_mod_cast (by omega : 3 ≤ V.card)
    have hle : (4 - 2 * (V.card : ℤ)) * D ≤ -2 * (D : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have hnonneg : 0 ≤ ∑ v ∈ V, (T v : ℤ) :=
      Finset.sum_nonneg fun v _ ↦ by positivity
    rw [hsumT] at hnonneg
    omega
  have hk₀ : V.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at hA
    omega
  have hk₁ : V.card ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    have hvV : v ∈ V := by simp [hv]
    have hTv := hT v hvV
    rw [hv, Finset.sum_singleton, Finset.card_singleton] at hsumT
    omega
  obtain ⟨i, j, hij, hV⟩ := Finset.card_eq_two.mp (by omega : V.card = 2)
  have hi : i ∈ V := by simp [hV]
  have hj : j ∈ V := by simp [hV]
  have hsum : T i + T j = 2 := by
    rw [hV, Finset.sum_pair hij, Finset.card_pair hij] at hsumT
    omega
  have hfinish (u v : ι) (hu : u ∈ V) (hv : v ∈ V) (huv : u ≠ v)
      (hVuv : V = {u, v}) (hS : T u + T v = 2) (hpos : 0 < T u) :
      ((D = 2 ∧ n u = 0 ∧ a u = 1 ∧ n v = 0 ∧ a v = 2) ∨
        (D = 3 ∧ n u = 1 ∧ a u = 0 ∧ a v = 3)) := by
    have hbound : T u ≤ 2 := by omega
    obtain ⟨htwo, hshape⟩ :=
      positive_defect_shape (hM u hu) (hEven u hu) (hD u hu) hpos hbound
    have hTu : T u = 2 := htwo
    have hTv : T v = 0 := by omega
    have hMv : M v = 2 := by
      rcases mul_eq_zero.mp (show (M v - 2) * (2 * n v + a v) = 0 from hTv) with h | h
      · have := hM v hv
        omega
      · have := hF v hv
        omega
    have ha := hA
    rw [hVuv, Finset.sum_pair huv] at ha
    rcases hshape with ⟨h₂, hn, hau⟩ | ⟨h₃, hn, hau⟩
    · have hav : a v = 2 := by omega
      have hd := hD v hv
      rw [h₂, hMv, hav] at hd
      exact Or.inl ⟨h₂, hn, hau, by omega, hav⟩
    · exact Or.inr ⟨h₃, hn, hau, by omega⟩
  by_cases hpos : 0 < T i
  · exact ⟨i, j, hV, hfinish i j hi hj hij hV hsum hpos⟩
  · have hV' : V = {j, i} := hV.trans (Finset.pair_comm i j)
    exact ⟨j, i, hV', hfinish j i hj hi hij.symm hV' (by omega) (by omega)⟩

end FiberArithmetic

section Fibers

variable {K : Type*} [Field K] [DecidableEq K]

private noncomputable abbrev fiber (s : K[X]) (v : K) : Finset K :=
  (s - C v).roots.toFinset

private noncomputable abbrev specialValues (s : K[X]) (E : Finset K) : Finset K :=
  (E ∪ (derivative s).roots.toFinset).image s.eval

private theorem fibers_disjoint {s : K[X]} (hs : 0 < s.natDegree) (V : Finset K) :
    (V : Set K).PairwiseDisjoint (fiber s) := by
  intro v _ v' _ hvv'
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  exact hvv' (((mem_polynomial_roots_sub_C hs).mp hw).symm.trans
    ((mem_polynomial_roots_sub_C hs).mp hw'))

private theorem sum_fiber_defects [IsAlgClosed K] [CharZero K] {s : K[X]} (hs : 0 < s.natDegree) (E : Finset K) :
    ∑ v ∈ specialValues s E, ((s.natDegree : ℤ) - (fiber s v).card) =
      (s.natDegree : ℤ) - 1 := by
  let V := specialValues s E
  have hderiv : derivative s ≠ 0 := derivative_ne_zero.mpr (Nat.ne_of_gt hs)
  have hcrit : (derivative s).roots.toFinset ⊆ V.biUnion (fiber s) := by
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨s.eval w,
      Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩,
      (mem_polynomial_roots_sub_C hs).mpr rfl⟩
  have htotal :
      ∑ v ∈ V, ∑ w ∈ fiber s v, (polynomialRamificationIdx s w - 1) = s.natDegree - 1 := by
    rw [← Finset.sum_biUnion (fibers_disjoint hs V)]
    simp_rw [polynomialRamificationIdx_sub_one]
    rw [← Finset.sum_subset hcrit, sum_rootMultiplicity_polynomial_derivative]
    intro w _ hw
    rw [rootMultiplicity_eq_zero]
    intro hr
    exact hw (Multiset.mem_toFinset.mpr ((mem_roots hderiv).mpr hr))
  have hcast (v : K) :
      ((∑ w ∈ fiber s v, (polynomialRamificationIdx s w - 1) : ℕ) : ℤ) =
        (s.natDegree : ℤ) - (fiber s v).card := by
    have hsum := sum_polynomialRamificationIdx_fiber hs v
    have hle : (fiber s v).card ≤ s.natDegree := by
      rw [← hsum, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun w _ ↦ polynomialRamificationIdx_pos hs w
    rw [Finset.sum_tsub_distrib (fiber s v)
      (f := polynomialRamificationIdx s) (g := fun _ ↦ 1)
      (fun w _ ↦ polynomialRamificationIdx_pos hs w),
      hsum, ← Finset.card_eq_sum_ones, Nat.cast_sub hle]
  have htotal' := congrArg (fun z : ℕ ↦ (z : ℤ)) htotal
  have hdeg : 1 ≤ s.natDegree := Nat.succ_le_of_lt hs
  rw [Nat.cast_sum, Nat.cast_sub hdeg, Nat.cast_one] at htotal'
  simpa only [hcast] using htotal'

private theorem sum_marked_points {s : K[X]} (hs : 0 < s.natDegree) (E : Finset K) :
    ∑ v ∈ specialValues s E, (fiber s v ∩ E).card = E.card := by
  let V := specialValues s E
  have hdisj : (V : Set K).PairwiseDisjoint fun v ↦ fiber s v ∩ E := by
    intro v hv v' hv' hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (fibers_disjoint hs V hv hv' hne))
  change ∑ v ∈ V, (fiber s v ∩ E).card = E.card
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨_, _, _, hw⟩
    exact hw
  · intro hw
    exact ⟨s.eval w, Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩,
      (mem_polynomial_roots_sub_C hs).mpr rfl, hw⟩

private theorem weighted_fiber_degree [IsAlgClosed K] {s : K[X]} (hs : 0 < s.natDegree) {E : Finset K}
    {v : K} {M : ℕ}
    (hM : ∀ w ∈ fiber s v, polynomialRamificationIdx s w * hemiMultiplicity E w = M) :
    2 * s.natDegree = 2 * M * (fiber s v \ E).card + M * (fiber s v ∩ E).card := by
  rw [← sum_polynomialRamificationIdx_fiber hs v, Finset.mul_sum,
    ← Finset.sum_sdiff (Finset.inter_subset_left : fiber s v ∩ E ⊆ fiber s v),
    Finset.sdiff_inter_self_left]
  have hu : ∑ w ∈ fiber s v \ E, 2 * polynomialRamificationIdx s w =
      ∑ _w ∈ fiber s v \ E, 2 * M := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have h := hM w (Finset.mem_sdiff.mp hw).1
    rw [hemiMultiplicity, if_neg (Finset.mem_sdiff.mp hw).2, mul_one] at h
    rw [h]
  have hm : ∑ w ∈ fiber s v ∩ E, 2 * polynomialRamificationIdx s w =
      ∑ _w ∈ fiber s v ∩ E, M := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have h := hM w (Finset.mem_inter.mp hw).1
    rw [hemiMultiplicity, if_pos (Finset.mem_inter.mp hw).2] at h
    rw [← h, mul_comm]
  rw [hu, hm, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  ring

private theorem exceptional_polynomial_fibers [IsAlgClosed K] [CharZero K] {s : K[X]}
    (hs : 0 < s.natDegree) (hs₂ : 2 ≤ s.natDegree) {E : Finset K} (hE : E.card = 3)
    (h : ∀ w w', s.eval w = s.eval w' →
      polynomialRamificationIdx s w * hemiMultiplicity E w =
        polynomialRamificationIdx s w' * hemiMultiplicity E w') :
    ∃ i j, specialValues s E = {i, j} ∧ (fiber s i).card = 1 ∧
      ((s.natDegree = 2 ∧ fiber s i ⊆ E ∧ fiber s j ⊆ E) ∨
        (s.natDegree = 3 ∧ E ⊆ fiber s j)) := by
  set V := specialValues s E
  let n : K → ℕ := fun v ↦ (fiber s v \ E).card
  let a : K → ℕ := fun v ↦ (fiber s v ∩ E).card
  have hV : ∀ v ∈ V, ∃ w ∈ E ∪ (derivative s).roots.toFinset, s.eval w = v :=
    fun v hv ↦ Finset.mem_image.mp hv
  choose! w hw hwv using hV
  let M : K → ℕ := fun v ↦ polynomialRamificationIdx s (w v) * hemiMultiplicity E (w v)
  have hM : ∀ v ∈ V, ∀ u ∈ fiber s v, polynomialRamificationIdx s u * hemiMultiplicity E u = M v :=
    fun v hv u hu ↦ h u (w v) (((mem_polynomial_roots_sub_C hs).mp hu).trans (hwv v hv).symm)
  have hm : ∀ v ∈ V, 2 ≤ M v := by
    intro v hv
    have hpos := polynomialRamificationIdx_pos hs (w v)
    rcases Finset.mem_union.mp (hw v hv) with he | hc
    · simp only [M, hemiMultiplicity, if_pos he]
      omega
    · have hderiv : derivative s ≠ 0 := derivative_ne_zero.mpr (Nat.ne_of_gt hs)
      have hroot : 0 < rootMultiplicity (w v) (derivative s) := by
        rw [rootMultiplicity_pos hderiv]
        exact (mem_roots hderiv).mp (Multiset.mem_toFinset.mp hc)
      have hidx : 2 ≤ polynomialRamificationIdx s (w v) := by
        rw [← polynomialRamificationIdx_sub_one] at hroot
        omega
      have hmult : 1 ≤ hemiMultiplicity E (w v) := by
        unfold hemiMultiplicity
        split_ifs <;> omega
      exact Nat.mul_le_mul hidx hmult
  have hcard (v : K) : (fiber s v).card = n v + a v :=
    (Finset.card_sdiff_add_card_inter (fiber s v) E).symm
  have hF : ∀ v ∈ V, 1 ≤ n v + a v := by
    intro v hv
    rw [← hcard v]
    exact Finset.card_pos.mpr ⟨w v, (mem_polynomial_roots_sub_C hs).mpr (hwv v hv)⟩
  have hEven : ∀ v ∈ V, 0 < a v → Even (M v) := by
    intro v hv ha
    obtain ⟨u, hu⟩ : (fiber s v ∩ E).Nonempty := Finset.card_pos.mp ha
    have hmu := hM v hv u (Finset.mem_inter.mp hu).1
    rw [hemiMultiplicity, if_pos (Finset.mem_inter.mp hu).2] at hmu
    exact ⟨polynomialRamificationIdx s u, by omega⟩
  have hd : ∀ v ∈ V, 2 * s.natDegree = 2 * M v * n v + M v * a v :=
    fun v hv ↦ weighted_fiber_degree hs (hM v hv)
  have hRH := sum_fiber_defects hs E
  simp only [hcard, Nat.cast_add] at hRH
  simp only [sub_add_eq_sub_sub] at hRH
  have hA : ∑ v ∈ V, a v = 3 := (sum_marked_points hs E).trans hE
  obtain ⟨i, j, hVij, hshape⟩ := two_special_fibers hs₂ hm hF hEven hd hRH hA
  refine ⟨i, j, hVij, ?_, ?_⟩
  · rw [hcard]
    rcases hshape with ⟨_, hn, ha, _⟩ | ⟨_, hn, ha, _⟩ <;> rw [hn, ha]
  · rcases hshape with ⟨h₂, hni, _, hnj, _⟩ | ⟨h₃, _, _, haj⟩
    · have hsub {v : K} (hv : n v = 0) : fiber s v ⊆ E := by
        have hempty : fiber s v \ E = ∅ := Finset.card_eq_zero.mp hv
        exact Finset.sdiff_eq_empty_iff_subset.mp hempty
      exact Or.inl ⟨h₂, hsub hni, hsub hnj⟩
    · have heq : fiber s j ∩ E = E := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by rw [hE]; exact haj.ge)
      refine Or.inr ⟨h₃, ?_⟩
      rw [← heq]
      exact Finset.inter_subset_left

end Fibers

section Symmetry

variable {K : Type*} [Field K]

/-- A polynomial with a root of full multiplicity is a power of a linear factor. -/
private theorem eq_C_mul_X_sub_C_pow {p : K[X]} (hp : p ≠ 0) {c : K}
    (hc : rootMultiplicity c p = p.natDegree) :
    p = C p.leadingCoeff * (X - C c) ^ p.natDegree := by
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd p c
  rw [hc] at hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hp hq
  have hdeg : q.natDegree = 0 := by
    have h := congrArg natDegree hq
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero c)) hq0, natDegree_pow,
      natDegree_X_sub_C, mul_one] at h
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg] at hq
  have hlc : p.leadingCoeff = q.coeff 0 := by
    rw [hq, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_X_sub_C, one_pow, one_mul,
      leadingCoeff_C]
  rw [hlc, mul_comm]
  exact hq

private theorem fiber_polynomial_of_singleton [DecidableEq K] [IsAlgClosed K] {s : K[X]}
    (hs : 0 < s.natDegree) {v c : K} (hf : fiber s v = {c}) :
    s - C v = C (s - C v).leadingCoeff * (X - C c) ^ s.natDegree := by
  have h := sum_polynomialRamificationIdx_fiber hs v
  have hcv : s.eval c = v := by
    apply (mem_polynomial_roots_sub_C hs).mp
    change c ∈ fiber s v
    rw [hf]
    exact Finset.mem_singleton_self c
  change ∑ w ∈ fiber s v, polynomialRamificationIdx s w = s.natDegree at h
  rw [hf, Finset.sum_singleton, polynomialRamificationIdx, hcv] at h
  simpa only [natDegree_sub_C] using
    eq_C_mul_X_sub_C_pow (polynomial_sub_C_ne_zero hs v) (h.trans natDegree_sub_C.symm)

/-- A polynomial with fiberwise constant weighted ramification at three marked points
has degree one, or the marked set has reflection symmetry in degree two or cube symmetry
in degree three. -/
theorem polynomial_orbifold_count [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {s : K[X]} (hs : 0 < s.natDegree) {E : Finset K} (hE : E.card = 3)
    (h : ∀ w w', s.eval w = s.eval w' →
      polynomialRamificationIdx s w * hemiMultiplicity E w =
        polynomialRamificationIdx s w' * hemiMultiplicity E w') :
    s.natDegree = 1 ∨ (s.natDegree = 2 ∧ ∃ c, ∀ w ∈ E, 2 * c - w ∈ E) ∨
      (s.natDegree = 3 ∧ ∃ c ρ, ∀ w ∈ E, (w - c) ^ 3 = ρ) := by
  rcases (by omega : s.natDegree = 1 ∨ 2 ≤ s.natDegree) with h₁ | hge
  · exact Or.inl h₁
  obtain ⟨i, j, hV, hFi, hshape⟩ := exceptional_polynomial_fibers hs hge hE h
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hFi
  have hform := fiber_polynomial_of_singleton hs hc
  rcases hshape with ⟨h₂, hi, hj⟩ | ⟨h₃, hj⟩
  · right
    left
    refine ⟨h₂, c, fun w hw ↦ ?_⟩
    have hwV : s.eval w ∈ specialValues s E :=
      Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
    rw [hV, Finset.mem_insert, Finset.mem_singleton] at hwV
    rcases hwV with hwi | hwj
    · have hwf : w ∈ fiber s i := (mem_polynomial_roots_sub_C hs).mpr hwi
      rw [hc, Finset.mem_singleton] at hwf
      rw [hwf, two_mul, add_sub_cancel_right]
      exact hi (by rw [hc]; simp)
    · apply hj
      apply (mem_polynomial_roots_sub_C hs).mpr
      rw [h₂] at hform
      have h₁' := congrArg (eval w) hform
      have h₂' := congrArg (eval (2 * c - w)) hform
      simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_X] at h₁' h₂'
      linear_combination h₂' - h₁' + hwj
  · right
    right
    refine ⟨h₃, c, (j - i) / (s - C i).leadingCoeff, fun w hw ↦ ?_⟩
    have hlc := leadingCoeff_ne_zero.mpr (polynomial_sub_C_ne_zero hs i)
    have h' := congrArg (eval w) hform
    have hwj : s.eval w = j := (mem_polynomial_roots_sub_C hs).mp (hj hw)
    simp only [eval_sub, eval_C, hwj, eval_mul, eval_pow, eval_X, h₃] at h'
    apply (eq_div_iff hlc).2
    simpa only [mul_comm] using h'.symm

end Symmetry

end AbcAdaptation.Reference.Iut.Anabelian
