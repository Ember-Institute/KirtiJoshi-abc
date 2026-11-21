/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceMapEquiv
import Definitions.Def_AbcAdaptation_Tripod_PlaceUnder
import Definitions.Def_AbcAdaptation_Tripod_RelativeDegreeTower
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

section FinitePlaceResidueTransport

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section
variable {k : Type*} [Field k] [NumberField k]

lemma natCast_mem_maximalIdeal_iff (v : FinitePlace k) {q : ℕ} (hq : q.Prime) :
    (q : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ AbcAdaptation.Reference.Iut.residueChar v = q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hq
end

section
variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']
variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_residueChar :
    AbcAdaptation.Reference.Iut.residueChar (FinitePlace.mapEquiv e v) = AbcAdaptation.Reference.Iut.residueChar v := by
  rw [← natCast_mem_maximalIdeal_iff _ (residueChar_prime v), FinitePlace.mapEquiv_maximalIdeal,
    Ideal.mem_comap, map_natCast]
  exact (natCast_mem_maximalIdeal_iff v (residueChar_prime v)).mpr rfl

end

end AbcAdaptation.Reference.Iut

end FinitePlaceResidueTransport

section TripodalPlaceTransport

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem genT_ne_zero : genT P x ≠ 0 := fun h => gen'_ne_zero x.2.1 (congrArg Subtype.val h)

theorem genT_sub_one_ne_zero : genT P x - 1 ≠ 0 := by
  intro h
  exact gen'_ne_one x.2.2 (congrArg Subtype.val (sub_eq_zero.mp h))

theorem tpdEquiv_symm_gen : (tpdEquiv P x).symm (gen x.1) = genT P x := by
  rw [← tpdEquiv_genT, AlgEquiv.symm_apply_apply]

noncomputable abbrev tpdPlace (𝔭 : FinitePlace (tpd P x)) : FinitePlace (fieldOf x.1) :=
  FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) 𝔭

theorem tpdPlace_gen (𝔭 : FinitePlace (tpd P x)) : tpdPlace P x 𝔭 (gen x.1) = 𝔭 (genT P x) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply]
  congr 1
  exact tpdEquiv_symm_gen P x

theorem tpdPlace_gen_sub_one (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 (gen x.1 - 1) = 𝔭 (genT P x - 1) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply, map_sub, map_one]
  congr 2
  exact tpdEquiv_symm_gen P x

theorem residueChar_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    AbcAdaptation.Reference.Iut.residueChar (tpdPlace P x 𝔭) = AbcAdaptation.Reference.Iut.residueChar 𝔭 :=
  FinitePlace.mapEquiv_residueChar _ _

end AbcAdaptation.Tripod

end TripodalPlaceTransport

section TripodalCompactValuation

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

lemma log_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

variable (P : CurveProviders) (x : Pt)

theorem abs_log_valuation_mul_le {K : CompactlyBounded} (hx : x ∈ K.set)
    (𝔭 : FinitePlace (tpd P x)) (h𝔭 : AbcAdaptation.Reference.Iut.residueChar 𝔭 ∈ K.V) :
    |((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) ≤ K.c ∧
      |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) ≤ K.c := by
  have hmem : AbcAdaptation.Reference.Iut.residueChar (tpdPlace P x 𝔭) ∈ K.V :=
    (residueChar_tpdPlace P x 𝔭).symm ▸ h𝔭
  have hb := hx.1 (tpdPlace P x 𝔭) hmem
  rw [tpdPlace_gen, tpdPlace_gen_sub_one, log_apply_eq _ (genT_ne_zero P x),
    log_apply_eq _ (genT_sub_one_ne_zero P x)] at hb
  have hpos : 0 ≤ (inertDeg (tpd P x) 𝔭 : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  obtain ⟨h1, h2⟩ := hb
  rw [abs_mul, abs_of_nonneg hpos] at h1 h2
  exact ⟨h1, h2⟩

end AbcAdaptation.Tripod

end TripodalCompactValuation

section TwoAdicLegendreValuation

namespace AbcAdaptation.Tripod

open WithZero WeierstrassCurve
open scoped WithZero

section
variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendre l).IsElliptic]

lemma valuation_legendre_ne_zero (hj : v (legendre l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  rw [legendre_j, map_div₀, map_mul, map_pow] at hj
  have hnum := (div_ne_zero_iff.mp hj).1
  exact ⟨(mul_ne_zero_iff.mp hnum).1,
    (pow_ne_zero_iff (by norm_num)).mp (mul_ne_zero_iff.mp hnum).2,
    (Valuation.ne_zero_iff v).mpr hl0, (Valuation.ne_zero_iff v).mpr hl1⟩

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendre_j (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  rw [legendre_j, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (2 : K)] [(legendre l).IsElliptic] in
/-- `log v(λ² − λ + 1) ≤ log v(λ) + log v(λ − 1)` or `≤ 0` (ultrametric inequality for
`λ² − λ + 1 = λ(λ − 1) + 1`). -/
lemma log_valuation_sq_sub_add_one_le (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0)
    (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨ log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have h : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [h] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with h1 | h1
  · left
    rw [map_mul] at h1
    rw [← log_mul hl hl1]
    exact (log_le_log hc (mul_ne_zero hl hl1)).mpr h1
  · right
    rw [map_one] at h1
    have := (log_le_log hc one_ne_zero).mpr h1
    simpa using this

/-- **The bound on `log v(j(E_λ))`**: if `v(256) ≤ 1` then
`log v(j) ≤ 2|log v(λ)| + 2|log v(λ − 1)|`. -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1) (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendre_j v hj]
  have ha := le_abs_self (log (v l))
  have ha' := neg_abs_le (log (v l))
  have hb := le_abs_self (log (v (l - 1)))
  have hb' := neg_abs_le (log (v (l - 1)))
  have ha0 := abs_nonneg (log (v l))
  have hb0 := abs_nonneg (log (v (l - 1)))
  rcases log_valuation_sq_sub_add_one_le v hc hvl hvl1 with h | h
  · linarith
  · linarith

end

end AbcAdaptation.Tripod

end TwoAdicLegendreValuation

section TatePoleOrder

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The norm of the Tate curve's `j`-invariant is the inverse norm of its parameter. -/
theorem norm_tateJ (t : TateParameter K) (h12 : (12 : K) ≠ 0) :
    ‖t.tateJ‖ = ‖(t.q : K)‖⁻¹ := by
  rw [tateJ, norm_div, norm_pow, t.norm_tateCurve_c₄, one_pow, t.norm_tateCurve_Δ h12,
    one_div]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma norm_q_eq_pow_orderNat (t : TateParameter K) {π : K} (hπ : IsUniformizer π) :
    ‖(t.q : K)‖ = ‖π‖ ^ (t.toOrdered hπ).orderNat := by
  have hpos := t.orderZ_pos hπ
  rw [show (t.toOrdered hπ).orderNat = (t.orderZ hπ).toNat from rfl,
    ← zpow_natCast, Int.toNat_of_nonneg hpos.le]
  exact t.norm_q_eq_zpow hπ

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TateCurvesTheta WithZero
open scoped WithZero

section
variable {k : Type*} [Field k] [NumberField k] (w : FinitePlace k)

lemma valued_eq_of_isUniformizer {π : localCompletion w} (hπ : IsUniformizer π) :
    Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer k
  have hπ₀' : Valued.v (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      exp (-1 : ℤ) := by
    rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', hπ₀]
  have hN : (1 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have hN0 : (0 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := zero_lt_one.trans hN
  have hπ' : Valued.v π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ.ne_zero
  set m : ℤ := log (Valued.v π)
  have hm : Valued.v π = exp m := (exp_log hπ').symm
  have hnorm := Tripod.norm_eq_zpow_of_valued w π m hm
  have hm0 : m < 0 := by
    have h := hπ.norm_lt_one
    rw [hnorm, zpow_lt_one_iff_right₀ hN] at h
    exact h
  have hunit : (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ₀'
    exact exp_ne_zero hπ₀'.symm
  obtain ⟨n, hn⟩ := hπ.generates (Units.mk0 _ hunit)
  rw [Units.val_mk0, Tripod.norm_eq_zpow_of_valued w _ _ hπ₀', hnorm, ← zpow_mul] at hn
  have hmn : (-1 : ℤ) = m * n := zpow_right_injective₀ hN0 hN.ne' hn
  have hm1 : m = -1 := by
    have hunit : IsUnit m := IsUnit.of_mul_eq_one (-n) (by rw [mul_neg, ← hmn]; norm_num)
    rcases Int.isUnit_iff.mp hunit with h | h
    · omega
    · exact h
  rw [hm, hm1]

variable {w}

/-- The valuation exponent of a Tate parameter is its negative normalized order. -/
lemma valued_tateParameter_q (t : TateParameter (localCompletion w)) {π : localCompletion w}
    (hπ : IsUniformizer π) :
    Valued.v (t.q : localCompletion w) = exp (-((t.toOrdered hπ).orderNat : ℤ)) := by
  have hq : (t.q : localCompletion w) ≠ 0 := t.q.ne_zero
  have hq' : Valued.v (t.q : localCompletion w) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  set m : ℤ := log (Valued.v (t.q : localCompletion w))
  have hm : Valued.v (t.q : localCompletion w) = exp m := (exp_log hq').symm
  have hN : (1 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have h1 := t.norm_q_eq_pow_orderNat hπ
  rw [Tripod.norm_eq_zpow_of_valued w _ m hm,
    Tripod.norm_eq_zpow_of_valued w π _ (valued_eq_of_isUniformizer w hπ)] at h1
  let N : ℝ := (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w
  have heq : N ^ m = N ^ ((-1 : ℤ) * ((t.toOrdered hπ).orderNat : ℤ)) := by
    calc
      N ^ m = (N ^ (-1 : ℤ)) ^ (t.toOrdered hπ).orderNat := h1
      _ = _ := by rw [zpow_mul, zpow_natCast]
  have he := zpow_right_injective₀ (zero_lt_one.trans hN) hN.ne' heq
  rw [hm, he, neg_one_mul]
end

namespace EllipticCurveData

variable (C : EllipticCurveData) {w : FinitePlace C.F}

/-- At a multiplicative place, the order of the Tate parameter is the pole order of `j`. -/
lemma valuation_j_eq_exp_qOrder (hw : w ∈ C.badAll) :
    w.maximalIdeal.valuation C.F C.E.j = exp ((C.tateInputs.qOrder w hw : ℕ) : ℤ) := by
  have hq : Valued.v ((C.tateInputs.tate w hw).q : localCompletion w) =
      exp (-((C.tateInputs.qOrder w hw : ℕ) : ℤ)) :=
    valued_tateParameter_q _ (C.tateInputs.unif_isUniformizer w hw)
  have hJ : (C.tateInputs.tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
    C.tateInputs.tateJ_eq w hw
  have hnorm : ‖(C.tateInputs.tate w hw).tateJ‖ =
      ‖((C.tateInputs.tate w hw).q : localCompletion w)‖⁻¹ :=
    (C.tateInputs.tate w hw).norm_tateJ (twelve_ne_zero w)
  have hq0 : ((C.tateInputs.tate w hw).q : localCompletion w) ≠ 0 :=
    (C.tateInputs.tate w hw).q.ne_zero
  have h1 : ‖(C.tateInputs.tate w hw).tateJ * ((C.tateInputs.tate w hw).q : localCompletion w)‖
      = 1 := by
    rw [norm_mul, hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)]
  rw [norm_eq_one_iff_valued, map_mul, hJ, hq, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation', exp_neg] at h1
  rw [eq_inv_of_mul_eq_one_left h1, inv_inv]

end EllipticCurveData
end AbcAdaptation.Reference.Iut

end TatePoleOrder

section CompactBound

namespace AbcAdaptation.Tripod

open NumberField

theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt}
    (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

end AbcAdaptation.Tripod

end CompactBound

section LocalDegrees

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _

section
variable {K : Type*} [Field K] [NumberField K]
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : AbcAdaptation.Reference.Iut.residueChar w = q) :
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
    ∑ w ∈ S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
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
    set T := S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = q) with hT
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

end

end AbcAdaptation.Tripod

end LocalDegrees

section TwoAdicLocalTerm

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

lemma term_le_aux {N A B E Fr Fp L D c : ℝ} (hN : N ≤ 2 * E * (A + B))
    (hA : A * (Fp * L) ≤ c) (hB : B * (Fp * L) ≤ c) (hE : 0 ≤ E) (hFr : 0 ≤ Fr) (hFp : 0 ≤ Fp)
    (hL : 0 ≤ L) (hD : 1 ≤ D) (hc : 0 ≤ c) :
    N * (Fp * Fr) * L ≤ 4 * c * (D * (E * Fr)) := by
  calc N * (Fp * Fr) * L = N * (Fr * (Fp * L)) := by ring
    _ ≤ 2 * E * (A + B) * (Fr * (Fp * L)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 2 * E * Fr * (A * (Fp * L) + B * (Fp * L)) := by ring
    _ ≤ 2 * E * Fr * (c + c) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = 4 * c * (1 * (E * Fr)) := by ring
    _ ≤ 4 * c * (D * (E * Fr)) := by gcongr

/-- **The local bound at a place over `2`**: for `w ∣ 𝔭` with `w` multiplicative and
`p_𝔭 = 2 ∈ V`, `h_w f_w log 2 ≤ 4c·[F_w : ℚ_2]`. -/
theorem term_le {K : CompactlyBounded} (hx : x ∈ K.set) {w : FinitePlace (P.curve x).F}
    (hw : w ∈ (P.curve x).badAll) (hw2 : AbcAdaptation.Reference.Iut.residueChar w = 2) :
    ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (AbcAdaptation.Reference.Iut.residueChar w) ≤
      4 * K.c * localDeg (P.curve x).F w := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder w with h𝔭
  have hw𝔭 : FinitePlace.LiesOver w 𝔭 := liesOver_placeUnder w
  have h𝔭2 : AbcAdaptation.Reference.Iut.residueChar 𝔭 = 2 :=
    (residueChar_eq_of_liesOver hw𝔭).symm.trans hw2
  have hc := CompactlyBounded.c_nonneg hx
  -- the order of the Tate parameter is `log v_w(j)`
  have hvj := (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : w.maximalIdeal.valuation _ (P.curve x).E.j ≠ 0 := by rw [hvj]; exact exp_ne_zero
  have hn : ((P.tate x).qOrder w hw : ℤ) ≤
      2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
        2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| := by
    have this : log (w.maximalIdeal.valuation _ (P.curve x).E.j) ≤
        2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
          2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| :=
      log_valuation_legendre_j_le (w.maximalIdeal.valuation (P.curve x).F)
        (l := genC' P x) (valuation_256_le_one w) hj0
    rwa [hvj, log_exp] at this
  -- the valuations at `w` are the `e(w/𝔭)`-th powers of those at `𝔭`
  set e : ℕ := relRamIdx w 𝔭 with he
  have ha : log (w.maximalIdeal.valuation _ (genC' P x)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x)) := by
    rw [← algebraMap_genT, valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  have hb : log (w.maximalIdeal.valuation _ (genC' P x - 1)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) := by
    rw [← algebraMap_genT, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
      valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast] at hn
  -- the bound of the compactly bounded subset at `𝔭`
  obtain ⟨hA, hB⟩ := abs_log_valuation_mul_le P x hx 𝔭 (by rw [h𝔭2]; exact K.two_mem)
  rw [h𝔭2] at hA hB
  -- the residue degrees and local degrees
  have hf : (inertDeg (P.curve x).F w : ℝ) = inertDeg (tpd P x) 𝔭 * relInertDeg w 𝔭 := by
    rw [inertDeg_eq_mul hw𝔭]; push_cast; ring
  have hd : (localDeg (P.curve x).F w : ℝ) = localDeg (tpd P x) 𝔭 * (e * relInertDeg w 𝔭) := by
    rw [localDeg_eq_mul hw𝔭]; push_cast; ring
  have hD : (1 : ℝ) ≤ localDeg (tpd P x) 𝔭 := by
    exact_mod_cast Nat.mul_pos (ramIdx_pos' 𝔭) (inertDeg_pos' 𝔭)
  have hn' : ((P.tate x).qOrder w hw : ℝ) ≤ 2 * e *
      (|((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| +
        |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)|) := by
    have h := (Int.cast_le (R := ℝ)).mpr hn
    push_cast at h
    linarith
  rw [hw2, hf, hd]
  exact term_le_aux hn' hA hB (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (log_natCast_nonneg _) hD hc

end AbcAdaptation.Tripod

end TwoAdicLocalTerm

section TwoAdicBound

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem twoAdicBound' (K : CompactlyBounded) : TwoAdicBoundHyp P K (4 * K.c) := by
  intro x hx
  classical
  have hc := CompactlyBounded.c_nonneg hx
  change (∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
      (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
        (inertDeg (P.curve x).F w : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar w))) /
      (Module.finrank ℚ (P.curve x).F : ℝ) ≤ 4 * K.c
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos)]
  calc ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
        (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
          (inertDeg (P.curve x).F w : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar w))
      ≤ ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
          4 * K.c * (localDeg (P.curve x).F w : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw
        split_ifs with h
        · exact term_le P x hx h hw.2
        · exact absurd hw.1 h
    _ = 4 * K.c * ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
          (localDeg (P.curve x).F w : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * K.c * (Module.finrank ℚ (P.curve x).F : ℝ) := by
        let S : Finset (FinitePlace (P.curve x).F) := (P.arith x).badAll_finite.toFinset
        have hcast : ((∑ w ∈ S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
            localDeg (P.curve x).F w : ℕ) : ℝ) ≤ (Module.finrank ℚ (P.curve x).F : ℝ) :=
          Nat.cast_le.mpr (sum_localDeg_filter_le S 2)
        have hsum := (Nat.cast_sum (R := ℝ) (S.filter fun w => AbcAdaptation.Reference.Iut.residueChar w = 2)
          (localDeg (P.curve x).F)).symm.trans_le hcast
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hc)

end AbcAdaptation.Tripod

end TwoAdicBound

section TwoAdicSolution

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution (P : CurveProviders) (K : CompactlyBounded) :
    TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  fun x hx => (twoAdicBound' P K x hx).trans (le_max_left _ _)

end TwoAdicSolution
