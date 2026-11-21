/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Lean
import B1SourceReplay
import Mathlib.Tactic.LinearCombination

/-!
Source commands from Iut/Tripod/{CurveFacts,TwoAdic,LogCond,Height}.lean
at iut revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
B1SourceReplay supplies the existing provider and height normalization.
-/

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero

section
variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- **IUT IV, Corollary 2.2(i)** ([GenEll], Proposition 3.4): `(1/6)·log(q_∀) ≈ ht_{𝒪(1)}`
on a compactly bounded subset. -/
def LegendreHeightHyp : Prop := ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan

end

/-- A compactly bounded subset has a nonnegative bound as soon as it is nonempty. -/
theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt} (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

/-- `v_w(256) ≤ 1` at every finite place. -/
theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _

end Iut.Tripod

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

/-! ### The sum of the local degrees over a rational prime -/

section LocalDeg

variable {K : Type*} [Field K] [NumberField K]

/-- `[K_w : ℚ_p] = e(𝔭_w/(p)) f(𝔭_w/(p))` for `p` the residue characteristic of `w`. -/
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : residueChar w = q) :
    localDeg K w = (Ideal.span {(q : ℤ)}).ramificationIdx' w.maximalIdeal.asIdeal *
      (Ideal.span {(q : ℤ)}).inertiaDeg' w.maximalIdeal.asIdeal := by
  subst hq
  rw [← under_int_eq]
  haveI : w.maximalIdeal.asIdeal.LiesOver (w.maximalIdeal.asIdeal.under ℤ) := inferInstance
  haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  unfold localDeg ramIdx inertDeg
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.maximalIdeal.asIdeal (under_int_ne_bot w),
    Ideal.inertiaDeg'_eq_inertiaDeg _ w.maximalIdeal.asIdeal]

/-- `∑_{w ∈ S, p_w = q} [K_w : ℚ_q] ≤ [K : ℚ]` for every finite set `S` of places of `K`
(from `∑_{w ∣ q} e_w f_w = [K : ℚ]`). -/
lemma sum_localDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
  classical
  by_cases hq : q.Prime
  · set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
    haveI hmax : p.IsMaximal := by
      haveI hprime : p.IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
          (Nat.prime_iff_prime_int.1 hq)
      exact IsPrime.to_maximal_ideal (by
        rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
    have hp0 : p ≠ ⊥ := by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0 (p := p)
    set T := S.filter (fun w => residueChar w = q) with hT
    have hover : ∀ w ∈ T, w.maximalIdeal.asIdeal.LiesOver p := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      rw [hp, ← hw.2]
      exact liesOver_span_residueChar w
    have hsub : T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 K) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr
        ⟨inferInstance, hover w hw⟩
    have hinj : Set.InjOn (fun w : FinitePlace K => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, localDeg K w
        = ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hT, Finset.mem_filter] at hw
          exact localDeg_eq_ramificationIdx'_mul_inertiaDeg' w hw.2
      _ = ∑ P ∈ T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ K := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

/-- `∑_{w ∈ S, p_w = q} f_w ≤ [K : ℚ]` for every finite set `S` of places of `K`. -/
lemma sum_inertDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), inertDeg K w ≤ Module.finrank ℚ K := by
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) (sum_localDeg_filter_le S q)
  unfold localDeg
  exact Nat.le_mul_of_pos_left _ (ramIdx_pos' w)

end LocalDeg

section General

variable {T : Type*} [Field T] [NumberField T]

/-- `v_w(2) = 1` at a place of residue characteristic `≠ 2`. -/
lemma valuation_two_eq_one_of_ne {w : FinitePlace T} (h2 : residueChar w ≠ 2) :
    w.maximalIdeal.valuation T 2 = 1 := by
  have : (2 : T) = algebraMap (𝓞 T) T 2 := by rw [map_ofNat]
  rw [this, valuation_eq_one_iff_notMem, two_mem_maximalIdeal_iff]
  exact h2

end General

section FinHeight

variable {T : Type*} [Field T] [NumberField T]

/-- **The archimedean part of the logarithmic height**:
`h_∞(y) = ∑_{v infinite} [T_v : ℝ] log⁺|y|_v`. -/
noncomputable def infHeight (y : T) : ℝ := ∑ v : InfinitePlace T, (v.mult : ℝ) * log⁺ (v y)

/-- `logHeight₁ y = h_∞(y) + h_fin(y)`. -/
lemma logHeight₁_eq_infHeight_add_finHeight (y : T) :
    Height.logHeight₁ y = infHeight y + finHeight y :=
  logHeight₁_eq y

lemma infHeight_nonneg (y : T) : 0 ≤ infHeight y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg

lemma finHeight_le_logHeight₁ (y : T) : finHeight y ≤ Height.logHeight₁ y := by
  rw [logHeight₁_eq_infHeight_add_finHeight]
  linarith [infHeight_nonneg y]

@[simp] lemma finHeight_zero : finHeight (0 : T) = 0 := by
  simp [finHeight]

end FinHeight

section LegendreJ

variable {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) {l : R}

/-- The right-hand side of the ultrametric comparison at a finite place:
`2(max(0, log v(λ)) + max(0, −log v(λ)) + max(0, −log v(λ − 1)))`. -/
def legendreBound (l : R) : ℤ :=
  2 * (max 0 (log (v l)) + max 0 (-log (v l)) + max 0 (-log (v (l - 1))))

lemma legendreBound_nonneg (l : R) : 0 ≤ legendreBound v l := by
  unfold legendreBound
  have h1 := le_max_left 0 (log (v l))
  have h2 := le_max_left 0 (-log (v l))
  have h3 := le_max_left 0 (-log (v (l - 1)))
  omega

variable (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- `v(legendreJ λ) ≠ 0 ↔ v(λ² − λ + 1) ≠ 0`. -/
lemma valuation_legendreJ_ne_zero_iff [NeZero (2 : R)] :
    v (legendreJ l) ≠ 0 ↔ v (l ^ 2 - l + 1) ≠ 0 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow]
  rw [div_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by norm_num),
    pow_ne_zero_iff (by norm_num), pow_ne_zero_iff (by norm_num)]
  simp only [(Valuation.ne_zero_iff v).mpr h256, (Valuation.ne_zero_iff v).mpr hl0,
    (Valuation.ne_zero_iff v).mpr hl1', ne_eq, not_false_eq_true, true_and, and_true]

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendreJ [NeZero (2 : R)] (hc : v (l ^ 2 - l + 1) ≠ 0) :
    log (v (legendreJ l)) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  have h256 : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit hl0 hl1 in
/-- **The ultrametric case analysis** for `λ`, `λ − 1`, `λ² − λ + 1` at a finite place. -/
lemma legendre_valuation_cases :
    (v l < 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) < 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) ≤ 1) ∨
    (1 < v l ∧ v (l - 1) = v l ∧ v (l ^ 2 - l + 1) = v l ^ 2) := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
  · left
    have hb : v (l - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
    refine ⟨hlt, hb, ?_⟩
    have hlt' : v (l * (l - 1)) < v 1 := by
      rw [map_mul, hb, mul_one, map_one]
      exact hlt
    rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
  · have hb' : v (l - 1) ≤ 1 := by
      have := Valuation.map_sub v l 1
      rwa [heq, map_one, max_self] at this
    rcases hb'.lt_or_eq with hb | hb
    · right; left
      refine ⟨heq, hb, ?_⟩
      have hlt' : v (l * (l - 1)) < v 1 := by
        rw [map_mul, heq, one_mul, map_one]
        exact hb
      rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
    · right; right; left
      refine ⟨heq, hb, ?_⟩
      rw [e]
      refine (Valuation.map_add v _ _).trans (max_le ?_ (map_one v).le)
      rw [map_mul, heq, hb, mul_one]
  · right; right; right
    have hb : v (l - 1) = v l :=
      Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
    refine ⟨hgt, hb, ?_⟩
    have e' : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
    have hlt' : v (1 - l) < v (l ^ 2) := by
      rw [Valuation.map_sub_swap, hb, map_pow]
      exact lt_self_pow₀ hgt (by norm_num)
    rw [e', Valuation.map_add_eq_of_lt_left v hlt', map_pow]

/-- **The upper bound** `max(0, log v(j)) ≤ legendreBound` for `v(256) ≤ 1`. -/
lemma max_log_valuation_legendreJ_le [NeZero (2 : R)] (h256 : v 256 ≤ 1) :
    max 0 (log (v (legendreJ l))) ≤ legendreBound v l := by
  refine max_le (legendreBound_nonneg v l) ?_
  by_cases hj : v (legendreJ l) = 0
  · rw [hj, log_zero]
    exact legendreBound_nonneg v l
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  have h256' : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendreJ v hl0 hl1 hc]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    have := le_max_left 0 (log (v l))
    have := le_max_right 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    have := le_max_right 0 (-log (v (l - 1)))
    omega
  · have hS : log (v (l ^ 2 - l + 1)) ≤ 0 := by
      have := (log_le_log hc one_ne_zero).mpr hc'
      simpa using this
    rw [ha, hb, log_one]
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    have := le_max_right 0 (log (v l))
    have := le_max_left 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    push_cast
    omega

/-- **The lower bound** `legendreBound ≤ max(0, log v(j))` for `v(256) = 1` and `j ≠ 0`. -/
lemma legendreBound_le_max_log_valuation_legendreJ [NeZero (2 : R)] (h256 : v 256 = 1)
    (hj : v (legendreJ l) ≠ 0) :
    legendreBound v l ≤ max 0 (log (v (legendreJ l))) := by
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [log_valuation_legendreJ v hl0 hl1 hc, h256, log_one]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    omega
  · rw [ha, hb, log_one]
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    omega

end LegendreJ

/-! ### The comparison at a finite place of a number field -/

section PlaceComparison

variable {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) {l : T}
  (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- The three terms of the comparison at a finite place, in terms of the valuation. -/
lemma posLog_terms_eq :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) =
      finWeight w * (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [posLog_apply_eq w hl0, posLog_apply_eq w (inv_ne_zero hl0),
    posLog_apply_eq w (inv_ne_zero hl1'), map_inv₀, map_inv₀, log_inv, log_inv]
  unfold legendreBound
  push_cast
  ring

/-- **`log⁺|j|_w ≤ 2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w)`** at every finite place. -/
theorem posLog_legendreJ_le :
    log⁺ (w (legendreJ l)) ≤ 2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) := by
  rw [posLog_terms_eq w hl0 hl1]
  by_cases hj : legendreJ l = 0
  · rw [hj, map_zero, Real.posLog_zero]
    exact mul_nonneg (finWeight_pos w).le (by exact_mod_cast legendreBound_nonneg _ l)
  rw [posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h := max_log_valuation_legendreJ_le (w.maximalIdeal.valuation T) hl0 hl1
    (Iut.Tripod.valuation_256_le_one w)
  have h' : ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) ≤
      (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

/-- **`2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w) ≤ log⁺|j|_w`** at a finite place of odd
residue characteristic, for `j ≠ 0`. -/
theorem posLog_legendreJ_ge (h2 : residueChar w ≠ 2) (hj : legendreJ l ≠ 0) :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) ≤ log⁺ (w (legendreJ l)) := by
  rw [posLog_terms_eq w hl0 hl1, posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h256 : w.maximalIdeal.valuation T 256 = 1 := by
    have : (256 : T) = 2 ^ 8 := by norm_num
    rw [this, map_pow, valuation_two_eq_one_of_ne h2, one_pow]
  have h := legendreBound_le_max_log_valuation_legendreJ (w.maximalIdeal.valuation T) hl0 hl1
    h256 ((Valuation.ne_zero_iff _).mpr hj)
  have h' : (legendreBound (w.maximalIdeal.valuation T) l : ℝ) ≤
      ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

end PlaceComparison

/-! ### `j = 0` -/

/-- If `j(λ) = 0` then `λ` is a sixth root of unity. -/
lemma pow_six_eq_one_of_legendreJ_eq_zero {R : Type*} [Field R] [NeZero (2 : R)] {l : R}
    (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hj : legendreJ l = 0) : l ^ 6 = 1 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hden : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  rw [legendreJ, div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by norm_num)] at hj
  rcases hj with (h | h) | h
  · exact absurd h h256
  · have h3 : l ^ 3 = -1 := by linear_combination (l + 1) * h
    calc l ^ 6 = (l ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3]; ring
  · exact absurd h hden

/-! ### The archimedean part on a set of bounded absolute values -/

/-- `h_∞(y) ≤ c·[T : ℚ]` if `log⁺|y|_w ≤ c` at every infinite place. -/
lemma infHeight_le_of_forall {T : Type*} [Field T] [NumberField T] {y : T} {c : ℝ}
    (h : ∀ w : InfinitePlace T, log⁺ (w y) ≤ c) :
    infHeight y ≤ c * Module.finrank ℚ T := by
  unfold infHeight
  calc ∑ w : InfinitePlace T, (w.mult : ℝ) * log⁺ (w y)
      ≤ ∑ w : InfinitePlace T, (w.mult : ℝ) * c :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (Nat.cast_nonneg _)
    _ = c * Module.finrank ℚ T := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, mul_comm]

/-- `log⁺ t ≤ |log t|`. -/
lemma posLog_le_abs_log (t : ℝ) : log⁺ t ≤ |Real.log t| := by
  rw [Real.posLog_apply]
  exact max_le (abs_nonneg _) (le_abs_self _)

/-- `log⁺ t⁻¹ ≤ |log t|`. -/
lemma posLog_inv_le_abs_log (t : ℝ) : log⁺ t⁻¹ ≤ |Real.log t| := by
  rw [Real.posLog_apply, Real.log_inv]
  exact max_le (abs_nonneg _) (neg_le_abs _)

end Iut

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real

variable (P : CurveProviders) (x : Pt)

/-! ### The bounds on a compactly bounded subset -/

variable {K : CompactlyBounded} {x : Pt}

/-- On `K`, the three archimedean terms are bounded by `c` at every infinite place. -/
lemma posLog_infinite_le (hx : x ∈ K.set) (w : InfinitePlace (fieldOf x.1)) :
    log⁺ (w (gen x.1)) ≤ K.c ∧ log⁺ (w (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (w (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.2 w
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

/-- On `K`, the three nonarchimedean terms are bounded by `c` at every finite place over the
support `V`. -/
lemma posLog_finite_le (hx : x ∈ K.set) (v : FinitePlace (fieldOf x.1))
    (hv : residueChar v ∈ K.V) :
    log⁺ (v (gen x.1)) ≤ K.c ∧ log⁺ (v (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (v (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.1 v hv
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

/-- **The archimedean parts are `O(d)` on `K`**: `logHeight₁ y ≤ h_fin(y) + c·d` for
`y ∈ {λ, λ⁻¹, (λ − 1)⁻¹}`. -/
lemma logHeight₁_le_finHeight_add (hx : x ∈ K.set) :
    Height.logHeight₁ (gen x.1) ≤ finHeight (gen x.1) + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1)⁻¹ ≤ finHeight (gen x.1)⁻¹ + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1 - 1)⁻¹ ≤ finHeight (gen x.1 - 1)⁻¹ + K.c * deg x.1 := by
  have key : ∀ y : fieldOf x.1, (∀ w : InfinitePlace (fieldOf x.1), log⁺ (w y) ≤ K.c) →
      Height.logHeight₁ y ≤ finHeight y + K.c * deg x.1 := by
    intro y hy
    rw [logHeight₁_eq_infHeight_add_finHeight, deg_eq_finrank]
    linarith [infHeight_le_of_forall hy]
  exact ⟨key _ fun w => (posLog_infinite_le hx w).1, key _ fun w => (posLog_infinite_le hx w).2.1,
    key _ fun w => (posLog_infinite_le hx w).2.2⟩

/-! ### The comparison of the finite parts -/

/-- A finite set of places of `ℚ(λ)` containing the supports of `log⁺|λ|_v`, `log⁺|λ⁻¹|_v`,
`log⁺|(λ − 1)⁻¹|_v` and `log⁺|j|_v`. -/
noncomputable def suppFinset (x : Pt) : Finset (FinitePlace (fieldOf x.1)) :=
  (Set.Finite.union
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1)) (hasFiniteSupport_posLog (gen x.1)⁻¹))
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1 - 1)⁻¹)
      (hasFiniteSupport_posLog (legendreJ (gen x.1))))).toFinset

lemma mem_suppFinset_of_ne {v : FinitePlace (fieldOf x.1)}
    (h : log⁺ (v (gen x.1)) ≠ 0 ∨ log⁺ (v (gen x.1)⁻¹) ≠ 0 ∨
      log⁺ (v (gen x.1 - 1)⁻¹) ≠ 0 ∨ log⁺ (v (legendreJ (gen x.1))) ≠ 0) :
    v ∈ suppFinset x := by
  rw [suppFinset, Set.Finite.mem_toFinset]
  simp only [Set.mem_union, Function.mem_support]
  tauto

lemma finHeight_gen_eq_sum (x : Pt) :
    finHeight (gen x.1) = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inl hv)

lemma finHeight_gen_inv_eq_sum (x : Pt) :
    finHeight (gen x.1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inl hv))

lemma finHeight_gen_sub_one_inv_eq_sum (x : Pt) :
    finHeight (gen x.1 - 1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1 - 1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inl hv)))

lemma finHeight_legendreJ_eq_sum (x : Pt) :
    finHeight (legendreJ (gen x.1)) = ∑ v ∈ suppFinset x, log⁺ (v (legendreJ (gen x.1))) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inr hv)))

/-- The sum of the three finite parts as a sum over `suppFinset`. -/
lemma two_mul_finHeight_sum_eq (x : Pt) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) =
      ∑ v ∈ suppFinset x,
        2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) := by
  rw [finHeight_gen_eq_sum, finHeight_gen_inv_eq_sum, finHeight_gen_sub_one_inv_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]

lemma gen_ne_one (x : Pt) : gen x.1 ≠ 1 := sub_ne_zero.mp (gen_sub_one_ne_zero x.2.2)

/-- **`h_fin(j) ≤ 2(h_fin(λ) + h_fin(λ⁻¹) + h_fin((λ − 1)⁻¹))`.** -/
theorem finHeight_legendreJ_le (x : Pt) :
    finHeight (legendreJ (gen x.1)) ≤
      2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) := by
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  exact Finset.sum_le_sum fun v _ => posLog_legendreJ_le v (gen_ne_zero x.2.1) (gen_ne_one x)

/-- The number of places of `ℚ(λ)` in a finite set `S` with residue characteristic in `V` is at
most `|V|·[ℚ(λ) : ℚ]`. -/
lemma card_filter_residueChar_mem_le (x : Pt) (S : Finset (FinitePlace (fieldOf x.1)))
    (V : Finset ℕ) :
    (S.filter (fun v => residueChar v ∈ V)).card ≤ V.card * deg x.1 := by
  classical
  have hsub : S.filter (fun v => residueChar v ∈ V) ⊆
      V.biUnion (fun q => S.filter (fun v => residueChar v = q)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨_, hv.2, Finset.mem_filter.mpr ⟨hv.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun q _ => ?_
  calc (S.filter (fun v => residueChar v = q)).card
      = ∑ v ∈ S.filter (fun v => residueChar v = q), 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ v ∈ S.filter (fun v => residueChar v = q), inertDeg (fieldOf x.1) v :=
        Finset.sum_le_sum fun v _ => inertDeg_pos' v
    _ ≤ Module.finrank ℚ (fieldOf x.1) := sum_inertDeg_filter_le S q
    _ = deg x.1 := (deg_eq_finrank x.1).symm

/-- **`2(h_fin(λ) + h_fin(λ⁻¹) + h_fin((λ − 1)⁻¹)) ≤ h_fin(j) + 6c|V|d`** on `K`, for `j ≠ 0`. -/
theorem finHeight_legendreJ_ge (hx : x ∈ K.set) (hj : legendreJ (gen x.1) ≠ 0) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) ≤
      finHeight (legendreJ (gen x.1)) + 6 * K.c * K.V.card * deg x.1 := by
  classical
  have hc := CompactlyBounded.c_nonneg hx
  have hg0 := gen_ne_zero x.2.1
  have hg1 := gen_ne_one x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  set S := suppFinset x with hS
  set A : FinitePlace (fieldOf x.1) → ℝ := fun v =>
    2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) with hA
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => residueChar v ∈ K.V)]
  have hA_le : ∀ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v ≤ 6 * K.c := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨h1, h2, h3⟩ := posLog_finite_le hx v hv.2
    rw [hA]
    dsimp only
    linarith
  have hA_le' : ∀ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V),
      A v ≤ log⁺ (v (legendreJ (gen x.1))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h2 : residueChar v ≠ 2 := fun h => hv.2 (h ▸ K.two_mem)
    exact posLog_legendreJ_ge v hg0 hg1 h2 hj
  have hcard := card_filter_residueChar_mem_le x S K.V
  have hcard' : ((S.filter (fun v => residueChar v ∈ K.V)).card : ℝ) ≤ K.V.card * deg x.1 := by
    exact_mod_cast hcard
  calc ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v +
        ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), A v
      ≤ ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), 6 * K.c +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) :=
        add_le_add (Finset.sum_le_sum hA_le) (Finset.sum_le_sum hA_le')
    _ = 6 * K.c * (S.filter (fun v => residueChar v ∈ K.V)).card +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 6 * K.c * (K.V.card * deg x.1) + ∑ v ∈ S, log⁺ (v (legendreJ (gen x.1))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hcard' (by positivity)) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.posLog_nonneg
    _ = _ := by ring

/-! ### The height comparison -/

/-- **IUT IV, Corollary 2.2(i) for the Legendre curves** (`LegendreHeightHyp P K`):
`(1/6)·log(q_∀(E_λ)) ≈ ht_{𝒪(1)}(λ)` on every compactly bounded subset `K`, with the explicit
constants `log 2 / 3` and `c|V| + c + log 2 / 3`. -/
theorem legendreHeight (P : CurveProviders) (K : CompactlyBounded) : LegendreHeightHyp P K := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  constructor
  · refine ⟨Real.log 2 / 3, fun x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h_eq_finHeight_div, htCan]
    have hd := deg_pos_real x.1
    have h1 := finHeight_legendreJ_le x
    have h2 := finHeight_le_logHeight₁ (gen x.1)
    have h3 := finHeight_le_logHeight₁ (gen x.1)⁻¹
    have h4 := finHeight_le_logHeight₁ (gen x.1 - 1)⁻¹
    rw [Height.logHeight₁_inv] at h3 h4
    have h5 : Height.logHeight₁ (gen x.1 - 1) ≤
        deg x.1 * Real.log 2 + Height.logHeight₁ (gen x.1) := by
      have := Height.logHeight₁_sub_le (gen x.1) 1
      rwa [Height.logHeight₁_one, add_zero, totalWeight_eq_finrank, ← deg_eq_finrank] at this
    have key : 1 / 6 * finHeight (legendreJ (gen x.1)) ≤
        Height.logHeight₁ (gen x.1) + Real.log 2 / 3 * deg x.1 := by linarith
    rw [div_add' _ _ _ hd.ne', ← mul_div_assoc]
    exact div_le_div_of_nonneg_right key hd.le
  · refine ⟨K.c * K.V.card + K.c + Real.log 2 / 3, fun x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h_eq_finHeight_div, htCan]
    have hd := deg_pos_real x.1
    have hc := CompactlyBounded.c_nonneg hx
    have hcV : 0 ≤ K.c * K.V.card := mul_nonneg hc (Nat.cast_nonneg _)
    by_cases hj : legendreJ (gen x.1) = 0
    · have hg6 : gen x.1 ^ 6 = 1 :=
        pow_six_eq_one_of_legendreJ_eq_zero (gen_ne_zero x.2.1) (gen_ne_one x) hj
      have h0 : Height.logHeight₁ (gen x.1) = 0 := by
        have := Height.logHeight₁_pow (gen x.1) 6
        rw [hg6, Height.logHeight₁_one] at this
        push_cast at this
        linarith
      rw [h0, hj, finHeight_zero, zero_div, mul_zero, zero_add]
      linarith
    have h1 := finHeight_legendreJ_ge hx hj
    obtain ⟨h2, h3, h4⟩ := logHeight₁_le_finHeight_add hx
    rw [Height.logHeight₁_inv] at h3 h4
    have h5 : Height.logHeight₁ (gen x.1) ≤
        deg x.1 * Real.log 2 + Height.logHeight₁ (gen x.1 - 1) := by
      have := Height.logHeight₁_add_le (gen x.1 - 1) 1
      rwa [sub_add_cancel, Height.logHeight₁_one, add_zero, totalWeight_eq_finrank,
        ← deg_eq_finrank] at this
    have key : Height.logHeight₁ (gen x.1) ≤
        1 / 6 * finHeight (legendreJ (gen x.1)) +
          (K.c * K.V.card + K.c + Real.log 2 / 3) * deg x.1 := by linarith
    rw [div_le_iff₀ hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']
    exact key

end Iut.Tripod

namespace TripodLegendreHeightSourceExpressions

open Lean Elab Term Meta

partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def encodeExpr : Expr → Except String Json
  | .bvar i => return node "bvar" [("index", toJson i)]
  | .sort u => return node "sort" [("level", ← encodeLevel u)]
  | .const n us => return node "const" [("name", encodeName n),
      ("levels", Json.arr (← us.toArray.mapM encodeLevel))]
  | .app f a => return node "app" [("fn", ← encodeExpr f), ("arg", ← encodeExpr a)]
  | .lam n t b bi => return node "lam" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .forallE n t b bi => return node "forall" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .letE n t v b nd => return node "let" [("name", encodeName n),
      ("type", ← encodeExpr t), ("value", ← encodeExpr v), ("body", ← encodeExpr b),
      ("nondependent", toJson nd)]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .mdata _ b => encodeExpr b
  | .proj n i b => return node "proj" [("name", encodeName n), ("index", toJson i),
      ("body", ← encodeExpr b)]
  | .fvar _ => throw "Free variable in compiler declaration type"
  | .mvar _ => throw "Expression metavariable in compiler declaration type"

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

abbrev AxiomCache := IO.Ref (Std.HashMap Name (Array Name))

-- The imported source environment is stable throughout this one export run.
-- Cache only successful collectAxioms results; errors still propagate normally.
def cachedAxioms (cache : AxiomCache) (name : Name) : MetaM (Array Name) := do
  if let some axs := (← cache.get)[name]? then return axs
  let axs ← collectAxioms name
  cache.modify fun entries => entries.insert name axs
  return axs

def expressionAxioms (cache : AxiomCache) (e : Expr) : MetaM (Array Name) := do
  let mut axs : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← cachedAxioms cache name do
      unless axs.contains ax do axs := axs.push ax
  return axs.qsort Name.lt

def kind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open actual Expr {label}"

def checkedValueType (label : String) (value type : Expr) : MetaM Expr := do
  requireClosed label value
  requireClosed s!"TYPE of {label}" type
  let inferred ← match Kernel.check (← getEnv) {} value with
    | .ok t => pure t
    | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} inferred type with
  | .ok true => pure ()
  | .ok false => throwError "Kernel actual value/TYPE mismatch {label}"
  | .error ex => throwKernelException ex
  return inferred

def comparisonFact (cache : AxiomCache) (name : Name) (referenceFile : String)
    (referenceLine : Nat) : MetaM Json := do
  let env ← getEnv
  let ci ← getConstInfo name
  unless ci.levelParams.isEmpty do throwError "Unexpected universe parameter for {name}"
  if (env.getModuleIdxFor? name).isSome then
    throwError "Expected {name} in the replay file"
  let some value := ci.value? (allowOpaque := true) | throwError "Missing value for {name}"
  let type ← checkedValueType name.toString value ci.type
  let axioms ← cachedAxioms cache name
  let typeAxioms ← expressionAxioms cache ci.type
  let valueAxioms ← expressionAxioms cache value
  for xs in #[axioms, typeAxioms, valueAxioms] do ensureStandard name.toString xs
  let names := fun ns : Array Name => Json.arr (ns.qsort Name.lt |>.map encodeName)
  let axiomStrings := fun ns : Array Name => toJson (ns.qsort Name.lt |>.map Name.toString)
  return Json.mkObj [
    ("record", toJson "fullActualFact"),
    ("name", toJson name.toString), ("nameExpr", encodeName name),
    ("owner", toJson env.mainModule.toString), ("ownerNameExpr", encodeName env.mainModule),
    ("kind", toJson (kind ci)), ("levelParams", names ci.levelParams.toArray),
    ("actualTypeExpr", ← checked (encodeExpr ci.type)),
    ("actualValueExpr", ← checked (encodeExpr value)),
    ("directTypeConstants", names ci.type.getUsedConstants),
    ("directValueConstants", names value.getUsedConstants),
    ("kernelInferredValueTypeExpr", ← checked (encodeExpr type)),
    ("valueRead", toJson true), ("kernelValueTypeMatchesActualTYPE", toJson true),
    ("axioms", axiomStrings axioms), ("typeAxioms", axiomStrings typeAxioms),
    ("valueAxioms", axiomStrings valueAxioms), ("hasSorryAx", toJson (axioms.contains `sorryAx)),
    ("referenceFile", toJson referenceFile), ("referenceLine", toJson referenceLine)]

def dependencyFact (cache : AxiomCache) (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  requireClosed name.toString ci.type
  let axioms ← cachedAxioms cache name
  let typeAxioms ← expressionAxioms cache ci.type
  ensureStandard name.toString axioms
  ensureStandard name.toString typeAxioms
  return Json.mkObj [
    ("name", toJson name.toString), ("nameExpr", encodeName name),
    ("levelParams", Json.arr (ci.levelParams.toArray.map encodeName)),
    ("actualTypeExpr", ← checked (encodeExpr ci.type)),
    ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
    ("typeAxioms", toJson (typeAxioms.map Name.toString))]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected Lean 4.35.0-rc3"
  let output ← absoluteEnv "TRIPOD_LEGENDRE_HEIGHT_SOURCE_FACTS"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let hyp ← comparisonFact cache ``Iut.Tripod.LegendreHeightHyp "Iut/Tripod/CurveFacts.lean" 403
  let comparison ← comparisonFact cache ``Iut.Tripod.legendreHeight "Iut/Tripod/Height.lean" 791
  let dependencies ← #[
    ``Iut.Tripod.finHeight_legendreJ_le,
    ``Iut.Tripod.finHeight_legendreJ_ge,
    ``Iut.Tripod.logHeight₁_le_finHeight_add,
    ``Iut.pow_six_eq_one_of_legendreJ_eq_zero].mapM (dependencyFact cache)
  IO.FS.writeFile output (hyp.compress ++ "\n" ++ comparison.compress ++ "\n")
  IO.FS.writeFile (output ++ ".dependencies.json") ((Json.arr dependencies).compress ++ "\n")
  logInfo "Exported both comparison declarations and the four dependency types"

end TripodLegendreHeightSourceExpressions
