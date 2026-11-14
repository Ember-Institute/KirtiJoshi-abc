/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors; The genl contributors

Independent source-proof adaptation of Belyi/CurveField/CoordRing.lean:38-163
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: d21848a412ff4da577615f237816c973cbe3dfd0790f0123f8ff3bc5b11eb180.
The original source's finite place set is the support of the actual existing
Divisor M. The existing coordRing and CuspGenerators are preserved exactly.
The cusp specialization also adapts Genl/Curves/BelyiDescent.lean:289-304
at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
Source SHA-256: fab56e0073e8ad10a1cea54552ba10a62df5cef54da2f572136975cffe375596.
This module contains substantial source proofs; it belongs to the local
Solutions/Source layer and is not a platform Definition submission.
See source-consumer.json for source spans and actual consumers.
-/
import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors

set_option autoImplicit false
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
variable [IsCurveField M.K]

/-- Source CoordRing.lean:38-63, on the existing actual place carrier. -/
theorem mem_chartRing_iff_forall {t : M.K} [Fact (Transcendental ℚ t)] (f : M.K) :
    f ∈ chartRing t ↔ ∀ P : Place M.K, t ∈ P.1 → f ∈ P.1 := by
  refine ⟨fun hf P hP => mem_of_mem_chartRing P.1 P.ratCast_mem hP hf, fun hf => ?_⟩
  set s : Set M.K := Set.range (algebraMap ℚ M.K) ∪ {t} with hs
  have hmem : f ∈ (⨅ V : {V : ValuationSubring M.K // s ⊆ V.toSubring}, V.1.toSubring) := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    by_cases htop : V = ⊤
    · subst htop
      exact trivial
    · have hq : ∀ q : ℚ, (q : M.K) ∈ V := fun q => hV (Or.inl ⟨q, eq_ratCast _ q⟩)
      exact hf ⟨V, htop, hq⟩ (hV (Or.inr rfl))
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) f := hmem
  have heq : (Algebra.adjoin ℚ {t}).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_eq_ring_closure]
  let e : Subring.closure s →+* Algebra.adjoin ℚ {t} :=
    { toFun := fun a => ⟨a.1, by rw [← Subalgebra.mem_toSubring, heq]; exact a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq e (RingHom.id M.K) (by ext a; rfl) hint

/-- Source CoordRing.lean:66-114. Actual large effective polar realization
produces a transcendental function with exactly the support of D as poles.
The input is the already defined polar multiplicity, not a supplied law. -/
theorem exists_notMem_iff_support
    (hRealize : ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P)
    (D : Divisor M) (hD : D ≠ 0) :
    ∃ t : M.K, Transcendental ℚ t ∧ ∀ P : Place M.K, t ∉ P.1 ↔ D P ≠ 0 := by
  classical
  obtain ⟨N1, hN1⟩ := hRealize
  set A₀ : Divisor M := ∑ P ∈ D.support, Finsupp.single P 1 with hA₀
  have hA₀P : ∀ P, A₀ P = if P ∈ D.support then 1 else 0 := by
    intro P
    rw [hA₀, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hA₀nonneg : 0 ≤ A₀ := fun P => by rw [hA₀P P]; split_ifs <;> simp
  obtain ⟨P₀, hP₀⟩ := Finsupp.support_nonempty_iff.mpr hD
  have hdeg₀ : 0 < divisorDegree M A₀ := by
    unfold divisorDegree
    refine Finset.sum_pos' (fun P _ =>
      mul_nonneg (hA₀nonneg P) (Int.natCast_nonneg _)) ?_
    refine ⟨P₀, ?_, ?_⟩
    · exact Finsupp.mem_support_iff.mpr (by rw [hA₀P P₀, if_pos hP₀]; exact one_ne_zero)
    · change 0 < A₀ P₀ * (P₀.degree : ℤ)
      rw [hA₀P P₀, if_pos hP₀, one_mul]
      exact_mod_cast P₀.degree_pos
  set n : ℕ := N1.toNat + 1 with hn
  have hdeg : N1 ≤ divisorDegree M (n • A₀) := by
    rw [divisorDegree_nsmul]
    have h1 : (N1 : ℤ) ≤ n := by
      rw [hn]
      push_cast
      have := Int.self_le_toNat N1
      omega
    nlinarith
  have hnonneg : 0 ≤ n • A₀ := fun P => by
    simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hA₀nonneg P)
  obtain ⟨t, ht⟩ := hN1 (n • A₀) hnonneg hdeg
  have hpole : ∀ P : Place M.K, t ∉ P.1 ↔ P ∈ D.support := by
    intro P
    rw [← P.ord_neg_iff]
    have h : max 0 (-P.ord t) = (n : ℤ) * (if P ∈ D.support then 1 else 0) := by
      simpa only [poleMultiplicity, ord_eq_placeOrd, Finsupp.smul_apply,
        nsmul_eq_mul, hA₀P] using ht P
    constructor
    · intro hlt
      by_contra hPD
      rw [if_neg hPD, mul_zero] at h
      have := le_max_right 0 (-P.ord t)
      omega
    · intro hPD
      rw [if_pos hPD, mul_one] at h
      have hnpos : (0 : ℤ) < n := by rw [hn]; positivity
      by_contra hge
      push Not at hge
      rw [max_eq_left (by omega)] at h
      omega
  refine ⟨t, fun halg => ?_, fun P => (hpole P).trans Finsupp.mem_support_iff⟩
  exact (hpole P₀).mpr hP₀ (P₀.mem_of_isAlgebraic halg)

/-- Source CoordRing.lean:117-123. The target is the project's original
coordinate ring of the complement of the actual divisor support. -/
theorem coordRing_eq_chartRing {D : Divisor M} {t : M.K}
    [Fact (Transcendental ℚ t)]
    (ht : ∀ P : Place M.K, t ∉ P.1 ↔ D P ≠ 0) (f : M.K) :
    f ∈ coordRing M D ↔ f ∈ chartRing t := by
  rw [mem_chartRing_iff_forall M]
  change (∀ P : Place M.K, D P = 0 → f ∈ P.1) ↔ _
  refine forall_congr' fun P => ?_
  have hP : D P = 0 ↔ t ∈ P.1 := by
    simpa only [not_not] using (not_congr (ht P)).symm
  rw [hP]

/-- Source CoordRing.lean:126-163. Every finite set of actual regular
functions extends to generators of the complete existing coordinate ring. -/
theorem exists_finset_adjoin_eq_coordRing
    (hRealize : ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P)
    (D : Divisor M) (hD : D ≠ 0)
    (S : Finset M.K) (hS : ∀ s ∈ S, s ∈ coordRing M D) :
    ∃ G : Finset M.K, S ⊆ G ∧ Algebra.adjoin ℚ (G : Set M.K) = coordRing M D := by
  classical
  obtain ⟨t, htr, ht⟩ := exists_notMem_iff_support M hDVR hRealize D hD
  haveI : Fact (Transcendental ℚ t) := ⟨htr⟩
  letI : Algebra ℚ (chartRing t) := (chartRing t).algebra'
  obtain ⟨s₀, hs₀⟩ := (Algebra.FiniteType.out (R := ℚ) (A := chartRing t))
  set G₀ : Finset M.K := s₀.image Subtype.val with hG₀
  refine ⟨S ∪ G₀, Finset.subset_union_left, le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro g hg
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hg) with hgS | hgG
    · exact hS g hgS
    · rw [hG₀, Finset.mem_image] at hgG
      obtain ⟨a, -, rfl⟩ := hgG
      exact (coordRing_eq_chartRing M ht a.1).mpr a.2
  · intro f hf
    have hfc : f ∈ chartRing t := (coordRing_eq_chartRing M ht f).mp hf
    have h1 : (⟨f, hfc⟩ : chartRing t) ∈ Algebra.adjoin ℚ (s₀ : Set (chartRing t)) := by
      rw [hs₀]
      exact Algebra.mem_top
    have key : ∀ a : chartRing t, a ∈ Algebra.adjoin ℚ (s₀ : Set (chartRing t)) →
        (a : M.K) ∈ Algebra.adjoin ℚ ((S ∪ G₀ : Finset M.K) : Set M.K) := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
      | algebraMap q =>
        have : ((algebraMap ℚ (chartRing t) q : chartRing t) : M.K) = algebraMap ℚ M.K q := by
          have h := RingHom.ext_rat (((chartRing t).val : chartRing t →+* M.K).comp
            (algebraMap ℚ (chartRing t))) (algebraMap ℚ M.K)
          exact congrFun (congrArg DFunLike.coe h) q
        rw [this]
        exact Subalgebra.algebraMap_mem _ q
      | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
      | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
    exact key _ h1

/-- The existing reduced cusp divisor has exactly its stated coefficients. -/
theorem cuspDivisor_apply (φ : M.K) (hfin : (cusps M hDVR φ).Finite)
    (P : Place M.K) :
    cuspDivisor M hDVR φ hfin P = if P ∈ cusps M hDVR φ then 1 else 0 := by
  classical
  rw [cuspDivisor, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset]

/-- Source Genl/Curves/BelyiDescent.lean:292-295. A pole of the actual
transcendental function proves that its actual cusp divisor is nonzero. -/
theorem cuspDivisor_ne_zero (φ : M.K) (hφ : Transcendental ℚ φ)
    (hfin : (cusps M hDVR φ).Finite) : cuspDivisor M hDVR φ hfin ≠ 0 := by
  obtain ⟨P, hP⟩ := Place.exists_notMem hφ
  have hPcusp : P ∈ cusps M hDVR φ := Or.inl (by
    rw [ord_eq_placeOrd]
    exact ((P.ord_neg_iff).mpr hP).ne)
  intro hzero
  have h := cuspDivisor_apply M hDVR φ hfin P
  rw [if_pos hPcusp, hzero, Finsupp.coe_zero, Pi.zero_apply] at h
  exact zero_ne_one h

/-- Source Genl/Curves/BelyiDescent.lean:296-304. All three original
tripod functions are regular off the actual cusp set. -/
theorem tripod_regular_of_notMem_cusps (φ : M.K) (hφ : Transcendental ℚ φ)
    (P : Place M.K) (hP : P ∉ cusps M hDVR φ) :
    φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (1 - φ)⁻¹ ∈ P.1 := by
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  have hφ1 : φ - 1 ≠ 0 := by
    intro h
    apply hφ
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_one
  have hφord : ord M hDVR P φ = 0 := by
    by_contra h
    exact hP (Or.inl h)
  have hsub : ord M hDVR P (φ - 1) ≤ 0 := by
    exact not_lt.mp (fun h => hP (Or.inr h))
  have hreg := (P.ord_eq_zero_iff hφ0).mp
    (by simpa only [ord_eq_placeOrd] using hφord)
  have hdiff : φ - 1 ∈ P.1 := P.1.sub_mem hreg.1 P.1.one_mem
  have hsub0 : P.ord (φ - 1) = 0 := le_antisymm
    (by simpa only [ord_eq_placeOrd] using hsub) (P.ord_nonneg_of_mem hdiff)
  have hinv : (φ - 1)⁻¹ ∈ P.1 := ((P.ord_eq_zero_iff hφ1).mp hsub0).2
  refine ⟨hreg.1, hreg.2, ?_⟩
  rw [← neg_sub, inv_neg]
  exact P.1.neg_mem _ hinv

/-- Exact composition into the original CuspGenerators, with its complete
coordinate-ring equality and all three required memberships. -/
theorem cuspGenerators_of_polarRealization
    (hRealize : ∃ N1 : ℤ, ∀ A : Divisor M, 0 ≤ A → N1 ≤ divisorDegree M A →
      ∃ f : M.K, ∀ P : Place M.K, poleMultiplicity M hDVR f P = A P)
    (φ : M.K) (hφ : Transcendental ℚ φ) (hfin : (cusps M hDVR φ).Finite) :
    Nonempty (CuspGenerators M hDVR φ hfin) := by
  classical
  have hS : ∀ s ∈ ({φ, φ⁻¹, (1 - φ)⁻¹} : Finset M.K),
      s ∈ coordRing M (cuspDivisor M hDVR φ hfin) := by
    intro s hs P hPzero
    have hP : P ∉ cusps M hDVR φ := by
      intro hPcusp
      have hcoef := cuspDivisor_apply M hDVR φ hfin P
      rw [if_pos hPcusp] at hcoef
      exact one_ne_zero (hcoef.symm.trans hPzero)
    have hreg := tripod_regular_of_notMem_cusps M hDVR φ hφ P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hreg.1
    · exact hreg.2.1
    · exact hreg.2.2
  obtain ⟨G, hSG, hG⟩ := exists_finset_adjoin_eq_coordRing M hDVR hRealize
    (cuspDivisor M hDVR φ hfin) (cuspDivisor_ne_zero M hDVR φ hφ hfin)
    {φ, φ⁻¹, (1 - φ)⁻¹} hS
  exact ⟨⟨G, hG, hSG (by simp), hSG (by simp), hSG (by simp)⟩⟩

end AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource
