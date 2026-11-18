/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Solutions.Source_TripodFinitePlaceArithmetic

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
  have hN : (1 : ℝ) < (Tripod.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have hN0 : (0 : ℝ) < (Tripod.residueChar w : ℝ) ^ Tripod.inertDeg k w := zero_lt_one.trans hN
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
  have hN : (1 : ℝ) < (Tripod.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have h1 := t.norm_q_eq_pow_orderNat hπ
  rw [Tripod.norm_eq_zpow_of_valued w _ m hm,
    Tripod.norm_eq_zpow_of_valued w π _ (valued_eq_of_isUniformizer w hπ)] at h1
  let N : ℝ := (Tripod.residueChar w : ℝ) ^ Tripod.inertDeg k w
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

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut NumberField WithZero
open scoped Real WithZero

variable (P : CurveProviders) (x : Pt)

/-- The contribution of a multiplicative place to the finite height of `j`. -/
theorem posLog_j_eq_of_mem_badAll {w : FinitePlace (P.curve x).F} (hw : w ∈ (P.curve x).badAll) :
    log⁺ (w (P.curve x).E.j) =
      ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (residueChar w) := by
  have hvj : w.maximalIdeal.valuation _ (P.curve x).E.j = exp (((P.tate x).qOrder w hw : ℕ) : ℤ) :=
    (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : (P.curve x).E.j ≠ 0 := by
    intro h
    rw [h, map_zero] at hvj
    exact exp_ne_zero hvj.symm
  rw [posLog_apply_eq w hj0, hvj, log_exp, finWeight, max_eq_right (by positivity)]
  push_cast
  ring

end AbcAdaptation.Tripod
