/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/LogCond.lean
Additional sources Iut/Tripod/TwoAdic.lean and Iut/Concrete/Existence.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TripodalPlaceTransport
import Solutions.Source_SL2ImageRangeCardinality
import Solutions.Source_TripodFinitePrimeCounting
import Solutions.Source_TripodLegendreValuationBounds
import Solutions.Source_TripodRelativeDegreeTower
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Classical

section Local

variable {T : Type*} [Field T] [NumberField T]

private lemma apply_eq_one_iff_valuation (𝔭 : FinitePlace T) (y : T) :
    𝔭 y = 1 ↔ 𝔭.maximalIdeal.valuation T y = 1 := by
  rw [← FinitePlace.norm_embedding_eq, norm_eq_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

/-- The log norms over a residue characteristic are bounded by the field degree times its log. -/
theorem sum_log_absNorm_filter_le (S : Finset (FinitePlace T)) (q : ℕ) :
    ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal) ≤
      Module.finrank ℚ T * Real.log q := by
  calc
    ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)
        = ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), (inertDeg T 𝔭 : ℝ) * Real.log q := by
      refine Finset.sum_congr rfl fun 𝔭 h𝔭 => ?_
      rw [absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow, (Finset.mem_filter.mp h𝔭).2]
    _ = (∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), (inertDeg T 𝔭 : ℝ)) * Real.log q := by
      rw [Finset.sum_mul]
    _ ≤ Module.finrank ℚ T * Real.log q := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg q)
      exact_mod_cast sum_inertDeg_filter_le S q

end Local

section Legendre

variable {T : Type*} [Field T] (v : Valuation T ℤᵐ⁰) {l : T}

private lemma valuation_legendreJ_le_one_of_eq_one (h256 : v 256 ≤ 1)
    (ha : v l = 1) (hb : v (l - 1) = 1) : v (legendreJ l) ≤ 1 := by
  have hc : v (l ^ 2 - l + 1) ≤ 1 := by
    have he : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
    rw [he]
    simpa only [map_mul, ha, hb, mul_one, map_one, max_self] using
      v.map_add (l * (l - 1)) 1
  simp only [legendreJ, map_div₀, map_mul, map_pow, ha, hb, one_pow, mul_one, div_one]
  exact mul_le_one₀ h256 zero_le (pow_le_one₀ zero_le hc)

private lemma one_lt_valuation_legendreJ_of_ne_one (hl0 : l ≠ 0) (hl1 : l - 1 ≠ 0)
    (h256 : v 256 = 1) (h : v l ≠ 1 ∨ v (l - 1) ≠ 1) : 1 < v (legendreJ l) := by
  have ha0 : 0 < v l := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hl0)
  have hb0 : 0 < v (l - 1) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hl1)
  simp only [legendreJ, map_div₀, map_mul, map_pow, h256, one_mul]
  rcases legendre_valuation_cases v (l := l) with
    ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, _⟩ | ⟨ha, hb, hc⟩
  · simp only [hb, hc, one_pow, mul_one]
    exact (one_lt_div₀ (pow_pos ha0 2)).2 (pow_lt_one₀ zero_le ha (by decide))
  · simp only [ha, hc, one_pow, one_mul]
    exact (one_lt_div₀ (pow_pos hb0 2)).2 (pow_lt_one₀ zero_le hb (by decide))
  · exact (h.elim (fun hne => hne ha) (fun hne => hne hb)).elim
  · rw [hb, hc, ← pow_mul, ← pow_add]
    exact (one_lt_div₀ (pow_pos ha0 (2 + 2))).2 (pow_lt_pow_right₀ ha (by decide))

end Legendre

variable (P : CurveProviders) (x : Pt)

/-- The finite places of the tripodal field where λ or λ − 1 has absolute value different from one. -/
def badT : Set (FinitePlace (tpd P x)) := {𝔭 | 𝔭 (genT P x) ≠ 1 ∨ 𝔭 (genT P x - 1) ≠ 1}

theorem badT_finite : (badT P x).Finite := by
  have h₁ := FinitePlace.hasFiniteMulSupport (genT_ne_zero P x)
  have h₂ := FinitePlace.hasFiniteMulSupport (genT_sub_one_ne_zero P x)
  exact h₁.union h₂

/-- The point conductor as a normalized sum on the tripodal field of the given curve. -/
theorem logCond_eq_sum_tpd :
    logCond x = (∑ 𝔭 ∈ (badT_finite P x).toFinset,
      Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)) / deg x.1 := by
  rw [logCond_eq_sum]
  congr 1
  symm
  refine Finset.sum_equiv (FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1))
    (fun 𝔭 => ?_) (fun 𝔭 _ => ?_)
  · rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    change (𝔭 (genT P x) ≠ 1 ∨ 𝔭 (genT P x - 1) ≠ 1) ↔ tpdPlace P x 𝔭 ∈ badPlaces x.1
    rw [mem_badPlaces, tpdPlace_gen, tpdPlace_gen_sub_one]
  · rw [FinitePlace.mapEquiv_absNorm]

private theorem mem_badT_iff_valuation {w : FinitePlace (P.curve x).F} {𝔭 : FinitePlace (tpd P x)}
    (hw𝔭 : FinitePlace.LiesOver w 𝔭) : 𝔭 ∈ badT P x ↔
      w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
        w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1 := by
  have hpow (y : tpd P x) : w.maximalIdeal.valuation _ (algebraMap (tpd P x) (P.curve x).F y) = 1 ↔
      𝔭.maximalIdeal.valuation _ y = 1 := by
    rw [valuation_algebraMap_eq_pow hw𝔭]
    exact pow_eq_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hw𝔭)
  have hmap : algebraMap (tpd P x) (P.curve x).F (genT P x - 1) = genC' P x - 1 := by
    rw [map_sub, map_one, algebraMap_genT]
  change (𝔭 (genT P x) ≠ 1 ∨ 𝔭 (genT P x - 1) ≠ 1) ↔ _
  rw [← hmap, ← algebraMap_genT P x]
  simp only [ne_eq, apply_eq_one_iff_valuation, hpow]

/-- A conductor place lies in the support of the point conductor. -/
theorem mem_badT_of_isBadTpdOf {ℓ : ℕ} {𝔭 : FinitePlace (tpd P x)}
    (h : IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) 𝔭) : 𝔭 ∈ badT P x := by
  obtain ⟨w, ⟨v, hv, hwv⟩, hw𝔭⟩ := h
  have hmult : HasMultiplicativeReductionAt (P.curve x).E w := hv.2.2.2 w hwv
  have hj := one_lt_valuation_j_of_mult (P.curve x).E w hmult
  rw [curve_j_eq_legendreJ P x] at hj
  apply (mem_badT_iff_valuation P x hw𝔭).2
  by_contra hbad
  have ha : w.maximalIdeal.valuation _ (genC' P x) = 1 :=
    not_not.mp (fun hne => hbad (Or.inl hne))
  have hb : w.maximalIdeal.valuation _ (genC' P x - 1) = 1 :=
    not_not.mp (fun hne => hbad (Or.inr hne))
  exact (not_le.mpr hj)
    (valuation_legendreJ_le_one_of_eq_one _ (valuation_256_le_one w) ha hb)

/-- A place in the point conductor support of residue characteristic different from 2 and ℓ
has a multiplicative place above it over `VBadOf ℓ`. -/
theorem isBadTpdOf_of_mem_badT {ℓ : ℕ} {𝔭 : FinitePlace (tpd P x)} (h : 𝔭 ∈ badT P x)
    (h2 : residueChar 𝔭 ≠ 2) (hℓ : residueChar 𝔭 ≠ ℓ) :
    IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) 𝔭 := by
  obtain ⟨w, hw𝔭⟩ := FinitePlace.exists_liesOver (K := (P.curve x).F) 𝔭
  have hchar : residueChar w = residueChar 𝔭 := residueChar_eq_of_liesOver hw𝔭
  have hw2 : residueChar w ≠ 2 := fun hv => h2 (hchar.symm.trans hv)
  have h256 : w.maximalIdeal.valuation (P.curve x).F 256 = 1 := by
    have he : (256 : (P.curve x).F) = 2 ^ 8 := by norm_num
    rw [he, map_pow, valuation_two_eq_one_of_ne hw2, one_pow]
  have hl0 : genC' P x ≠ 0 := by
    rw [← algebraMap_genT P x]
    exact (map_ne_zero _).2 (genT_ne_zero P x)
  have hl1 : genC' P x - 1 ≠ 0 := by
    rw [← algebraMap_genT P x, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub]
    exact (map_ne_zero _).2 (genT_sub_one_ne_zero P x)
  have hj : 1 < w.maximalIdeal.valuation _ (P.curve x).E.j := by
    rw [curve_j_eq_legendreJ P x]
    exact one_lt_valuation_legendreJ_of_ne_one _ hl0 hl1 h256
      ((mem_badT_iff_valuation P x hw𝔭).1 h)
  have hmult : HasMultiplicativeReductionAt (P.curve x).E w :=
    (hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E w
      ((P.arith x).stable_reduction w)).2 (not_le.mpr hj)
  obtain ⟨v, hwv⟩ := (P.arith x).exists_liesOver w
  have hcharv : residueChar w = AbcAdaptation.Reference.Iut.residueChar v :=
    (P.arith x).residueChar_liesOver v w hwv
  have hv2 : AbcAdaptation.Reference.Iut.residueChar v ≠ 2 := fun hv => hw2 (hcharv.trans hv)
  have hvℓ : AbcAdaptation.Reference.Iut.residueChar v ≠ ℓ :=
    fun hv => hℓ ((hchar.symm.trans hcharv).trans hv)
  exact ⟨w, ⟨v, ⟨hv2, hvℓ, ⟨w, hwv⟩, fun w' hw' =>
    (P.arith x).mult_invariant v hv2 w w' hwv hw' hmult⟩, hwv⟩, hw𝔭⟩

/-- The normalized conductor degree on the tripodal field as a filtered sum. -/
theorem logConductorDegOf_eq_sum (ℓ : ℕ) :
    logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) =
      (∑ 𝔭 ∈ (badT_finite P x).toFinset.filter
        (IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ)),
        Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)) / deg x.1 := by
  unfold logConductorDegOf
  rw [← finrank_tpd P x, Finset.sum_filter]
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := (badT_finite P x).toFinset)]
  intro 𝔭 h𝔭
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h𝔭
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  exact mem_badT_of_isBadTpdOf P x h𝔭.1

theorem logCondGe : LogCondGeHyp P := by
  intro x ℓ _ _
  rw [logConductorDegOf_eq_sum P x ℓ, logCond_eq_sum_tpd P x]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun 𝔭 _ _ => Real.log_nonneg (one_le_absNorm_real 𝔭)

theorem logCondLe : LogCondLeHyp P := by
  intro x ℓ hℓ _
  rw [logConductorDegOf_eq_sum P x ℓ, logCond_eq_sum_tpd P x]
  let S := (badT_finite P x).toFinset
  let g (𝔭 : FinitePlace (tpd P x)) : ℝ := Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)
  let bad := IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ)
  let R := S.filter (fun 𝔭 => ¬ bad 𝔭)
  change (∑ 𝔭 ∈ S, g 𝔭) / deg x.1 ≤
    (∑ 𝔭 ∈ S.filter bad, g 𝔭) / deg x.1 + Real.log (2 * (ℓ : ℝ))
  have hres : ∀ 𝔭 ∈ R, residueChar 𝔭 = 2 ∨ residueChar 𝔭 = ℓ := by
    intro 𝔭 h𝔭
    have ⟨hS, hnot⟩ := Finset.mem_filter.mp h𝔭
    have hbad : 𝔭 ∈ badT P x := (badT_finite P x).mem_toFinset.mp hS
    by_cases h2 : residueChar 𝔭 = 2
    · exact Or.inl h2
    by_cases hpℓ : residueChar 𝔭 = ℓ
    · exact Or.inr hpℓ
    exact (hnot (isBadTpdOf_of_mem_badT P x hbad h2 hpℓ)).elim
  have h2 : ∑ 𝔭 ∈ R.filter (fun 𝔭 => residueChar 𝔭 = 2), g 𝔭 ≤ deg x.1 * Real.log 2 := by
    simpa only [finrank_tpd P x, Nat.cast_ofNat] using sum_log_absNorm_filter_le R 2
  have hsub : R.filter (fun 𝔭 => ¬ residueChar 𝔭 = 2) ⊆ R.filter (fun 𝔭 => residueChar 𝔭 = ℓ) := by
    intro 𝔭 h𝔭
    obtain ⟨hR, hne⟩ := Finset.mem_filter.mp h𝔭
    exact Finset.mem_filter.mpr ⟨hR, (hres 𝔭 hR).resolve_left hne⟩
  have hl : ∑ 𝔭 ∈ R.filter (fun 𝔭 => ¬ residueChar 𝔭 = 2), g 𝔭 ≤ deg x.1 * Real.log ℓ := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun 𝔭 _ _ => ?_)).trans ?_
    · exact Real.log_nonneg (one_le_absNorm_real 𝔭)
    · simpa only [finrank_tpd P x] using sum_log_absNorm_filter_le R ℓ
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hR : (∑ 𝔭 ∈ R, g 𝔭) / deg x.1 ≤ Real.log (2 * (ℓ : ℝ)) := by
    apply (div_le_iff₀ (deg_pos_real x.1)).2
    rw [Real.log_mul two_ne_zero hℓ0, add_mul, mul_comm (Real.log 2), mul_comm (Real.log (ℓ : ℝ)),
      ← Finset.sum_filter_add_sum_filter_not R (fun 𝔭 => residueChar 𝔭 = 2)]
    exact add_le_add h2 hl
  rw [← Finset.sum_filter_add_sum_filter_not S bad, add_div]
  exact add_le_add_right hR _

end AbcAdaptation.Tripod
