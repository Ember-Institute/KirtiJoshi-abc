/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/CyclicIsogeny.lean (apply_genC_eq_one, log_apply_le,
and the archimedean part of main_bound) and Iut/Tripod/TwoAdic.lean
(one_lt_valuation_legendre_j)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Solutions.Source_TripodCyclicVeluTate
import Solutions.Source_TripodCyclicVeluTransport
import Solutions.Source_TripodLegendreValuationBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Cyclic

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum WithZero
open JoshiTeich.Act1Scene1.IutCyclicVelu (veluRatio)
open scoped Classical WithZero

attribute [local instance 1100] JoshiTeich.ReferenceIut.instDecidableEqIntermediateField

/-- Natural numbers have finite-place absolute value at most one. -/
lemma apply_natCast_le_one {F : Type*} [Field F] [NumberField F] (v : FinitePlace F) (n : ℕ) :
    v (n : F) ≤ 1 :=
  IsNonarchimedean.apply_natCast_le_one (f := v) (fun a b => FinitePlace.add_le v a b)

private lemma apply_eq_one_of_valuation_eq_one {F : Type*} [Field F] [NumberField F]
    (v : FinitePlace F) {y : F} (hy : v.maximalIdeal.valuation F y = 1) : v y = 1 := by
  rwa [← FinitePlace.norm_embedding_eq, norm_eq_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

private lemma one_lt_valuation_legendreJ {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    {l : F} (hl0 : l ≠ 0) (hl1 : l - 1 ≠ 0) (h256 : v 256 = 1)
    (h : v l ≠ 1 ∨ v (l - 1) ≠ 1) : 1 < v (legendreJ l) := by
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

variable (P : CurveProviders) (x : Pt)

private lemma apply_genC_eq_one {v : FinitePlace (P.curve x).F}
    (hv : v ∉ (P.curve x).badAll) (h₂ : residueChar v ≠ 2) :
    v (genC' P x) = 1 ∧ v (genC' P x - 1) = 1 := by
  have hle : v.maximalIdeal.valuation _ (P.curve x).E.j ≤ 1 := by
    by_contra h
    exact hv ((hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E v
      ((P.arith x).stable_reduction v)).mpr h)
  have h256 : v.maximalIdeal.valuation (P.curve x).F 256 = 1 := by
    rw [show (256 : (P.curve x).F) = 2 ^ 8 by norm_num, map_pow,
      valuation_two_eq_one_of_ne h₂, one_pow]
  have hval : v.maximalIdeal.valuation _ (genC' P x) = 1 ∧
      v.maximalIdeal.valuation _ (genC' P x - 1) = 1 := by
    by_contra h
    rw [not_and_or] at h
    rw [curve_j_eq_legendreJ P x] at hle
    exact (not_le.mpr (one_lt_valuation_legendreJ _ (genC'_ne_zero P x)
      (sub_ne_zero.mpr (genC'_ne_one P x)) h256 h)) hle
  exact ⟨apply_eq_one_of_valuation_eq_one v hval.1, apply_eq_one_of_valuation_eq_one v hval.2⟩

private lemma sqrtLam_ne_zero : sqrtLam' P x ≠ 0 := by
  intro h
  apply genC'_ne_zero P x
  rw [← sqrtLam'_sq P x, h, zero_pow two_ne_zero]

private lemma sqrtOneSubLam_ne_zero : sqrtOneSubLam' P x ≠ 0 := by
  intro h
  have hs := sqrtOneSubLam'_sq P x
  rw [h, zero_pow two_ne_zero] at hs
  exact genC'_ne_one P x (sub_eq_zero.mp hs.symm).symm

private lemma log_of_sq {r a : ℝ} (h : r ^ 2 = a) : Real.log r = Real.log a / 2 := by
  rw [← h, Real.log_pow]
  norm_num <;> ring

variable {ℓ : ℕ} (hℓ : ℓ.Prime)
variable (H : AddSubgroup (Affine.Point (Affine.baseChange (P.curve x).E (P.curve x).Fbar)))
variable [Fintype (HL P x hℓ H)] {ρ : (P.curve x).F}
variable (hρ : algebraMap (P.curve x).F (L P x hℓ) ρ =
  veluRatio (HL P x hℓ H) (T₁ P x hℓ) (R₁ P x hℓ) *
    veluRatio (HL P x hℓ H) (T₂ P x hℓ) (R₂ P x hℓ))

include hρ in
private lemma log_finite_crude_le (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hρ0 : ρ ≠ 0)
    (v : FinitePlace (P.curve x).F) :
    Real.log (v ρ) ≤ 4 * Real.log (max 1 (v (genC' P x))) -
      Real.log (v (genC' P x)) / 2 - Real.log (v (genC' P x - 1)) / 2 +
        4 * -Real.log (v (4 : (P.curve x).F)) + 4 * -Real.log (v (ℓ : (P.curve x).F)) := by
  have hvρ : 0 < v ρ := FinitePlace.pos_iff.mpr hρ0
  have hv₁ : 0 < v (sqrtLam' P x) := FinitePlace.pos_iff.mpr (sqrtLam_ne_zero P x)
  have hv₂ : 0 < v (sqrtOneSubLam' P x) := FinitePlace.pos_iff.mpr (sqrtOneSubLam_ne_zero P x)
  have h4 : (4 : (P.curve x).F) ≠ 0 := by norm_num
  have hℓ0 : (ℓ : (P.curve x).F) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hv4 : 0 < v (4 : (P.curve x).F) := FinitePlace.pos_iff.mpr h4
  have hvℓ : 0 < v (ℓ : (P.curve x).F) := FinitePlace.pos_iff.mpr hℓ0
  have hs₁ : v (sqrtLam' P x) ^ 2 = v (genC' P x) := by rw [← map_pow, sqrtLam'_sq]
  have hs₂ : v (sqrtOneSubLam' P x) ^ 2 = v (genC' P x - 1) := by
    rw [← map_pow, sqrtOneSubLam'_sq, ← map_neg_eq_map v, neg_sub]
  have hb := finite_crude P x hℓ H hρ hH hℓ2 v
  have h4ℓ : v (((4 * ℓ : ℕ) : (P.curve x).F)) = v (4 : (P.curve x).F) * v (ℓ : (P.curve x).F) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, map_mul]
  rw [h4ℓ] at hb
  have hp := mul_pos hv₁ hv₂
  have hn := pow_pos (mul_pos hv4 hvℓ) 4
  have hlog := Real.log_le_log (mul_pos hvρ (mul_pos hp hn)) hb
  rw [Real.log_mul hvρ.ne' (mul_pos hp hn).ne', Real.log_mul hp.ne' hn.ne',
    Real.log_mul hv₁.ne' hv₂.ne', Real.log_pow, Real.log_pow, Real.log_mul hv4.ne' hvℓ.ne',
    log_of_sq hs₁, log_of_sq hs₂] at hlog
  norm_num at hlog
  linarith only [hlog]

include hρ in
/-- The logarithmic estimate at a finite place, including the Tate contribution
at odd multiplicative places and the additional terms over two. -/
theorem log_apply_le (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2)
    (hgraph : IsGraphLineOdd P x hℓ hℓ2 H) (hρ0 : ρ ≠ 0) (v : FinitePlace (P.curve x).F) :
    Real.log (v ρ) ≤
      (if v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2 then
          -(((ℓ : ℝ) - 1) / 4 * Real.log (v (P.curve x).E.j)) else 0) +
        (if residueChar v = 2 then
          9 / 2 * |Real.log (v (genC' P x))| + 1 / 2 * |Real.log (v (genC' P x - 1))| +
            4 * -Real.log (v (4 : (P.curve x).F)) else 0) +
        4 * -Real.log (v (ℓ : (P.curve x).F)) := by
  by_cases htate : v ∈ (P.curve x).badAll ∧ residueChar v ≠ 2
  · simp only [if_pos htate, if_neg htate.2, add_zero]
    have hnonneg := neg_nonneg.mpr (Real.log_nonpos (apply_nonneg v (ℓ : (P.curve x).F))
      (apply_natCast_le_one v ℓ))
    have hvρ : 0 < v ρ := FinitePlace.pos_iff.mpr hρ0
    have hj : 0 < v (P.curve x).E.j := by
      rw [← FinitePlace.norm_embedding_eq]
      exact zero_lt_one.trans ((P.curve x).one_lt_norm_j htate.1)
    have hρpow := pow_pos hvρ 4
    have hjpow := pow_pos hj (ℓ - 1)
    have hlog := Real.log_le_log (mul_pos hρpow hjpow)
      (finite_tate P x hℓ H hρ hH hℓ2 hgraph htate.1 htate.2)
    rw [Real.log_mul hρpow.ne' hjpow.ne', Real.log_pow, Real.log_pow, Real.log_one,
      Nat.cast_sub hℓ.one_lt.le, Nat.cast_one] at hlog
    norm_num at hlog
    nlinarith only [hlog, hnonneg]
  · rw [if_neg htate, zero_add]
    have hb := log_finite_crude_le P x hℓ H hρ hH hℓ2 hρ0 v
    by_cases h₂ : residueChar v = 2
    · rw [if_pos h₂]
      have hmax : Real.log (max 1 (v (genC' P x))) ≤ |Real.log (v (genC' P x))| := by
        rcases le_total (v (genC' P x)) 1 with h | h
        · rw [max_eq_left h, Real.log_one]
          exact abs_nonneg _
        · rw [max_eq_right h]
          exact le_abs_self _
      linarith only [hb, hmax, neg_abs_le (Real.log (v (genC' P x))),
        neg_abs_le (Real.log (v (genC' P x - 1)))]
    · simp only [if_neg h₂, zero_add]
      obtain ⟨hl₁, hl₂⟩ := apply_genC_eq_one P x (fun hv => htate ⟨hv, h₂⟩) h₂
      have hv2 : v (2 : (P.curve x).F) = 1 :=
        apply_eq_one_of_valuation_eq_one v (valuation_two_eq_one_of_ne h₂)
      have hv4 : v (4 : (P.curve x).F) = 1 := by
        rw [show (4 : (P.curve x).F) = 2 * 2 by norm_num, map_mul, hv2, one_mul]
      rw [hl₁, hl₂, hv4, max_self, Real.log_one] at hb
      linarith only [hb]

include hρ in
/-- The logarithmic archimedean estimate with the original constant C₀. -/
theorem log_infinite_bound (hH : Nat.card H = ℓ) (hℓ2 : ℓ ≠ 2) (hρ0 : ρ ≠ 0) {c C₀ : ℝ}
    (hC₀1 : 1 ≤ C₀) (hC₀ : LegendreTorsionXBound c C₀) (v : InfinitePlace (P.curve x).F)
    (hv₁ : |Real.log (v (genC' P x))| ≤ c) (hv₂ : |Real.log (v (genC' P x - 1))| ≤ c) :
    Real.log (v ρ) ≤ 2 * Real.log (32 * C₀) + 6 * Real.log ℓ + c := by
  have hvρ : 0 < v ρ := InfinitePlace.pos_iff.mpr hρ0
  have hs₁ : 0 < v (sqrtLam' P x) := InfinitePlace.pos_iff.mpr (sqrtLam_ne_zero P x)
  have hs₂ : 0 < v (sqrtOneSubLam' P x) := InfinitePlace.pos_iff.mpr (sqrtOneSubLam_ne_zero P x)
  have hsq₁ : v (sqrtLam' P x) ^ 2 = v (genC' P x) := by rw [← map_pow, sqrtLam'_sq]
  have hsq₂ : v (sqrtOneSubLam' P x) ^ 2 = v (genC' P x - 1) := by
    rw [← map_pow, sqrtOneSubLam'_sq, ← neg_sub (genC' P x) 1, infinitePlace_apply_neg]
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hcpos : 0 < 32 * C₀ := mul_pos (by norm_num) (zero_lt_one.trans_le hC₀1)
  have hb : v ρ * (v (sqrtLam' P x) * v (sqrtOneSubLam' P x)) ≤
      (2 * (ℓ : ℝ) * (C₀ * (4 * (ℓ : ℝ)) ^ 2)) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      infinite_bound P x hℓ H hρ hH hℓ2 hC₀ v hv₁ hv₂
  have hlog := Real.log_le_log (mul_pos hvρ (mul_pos hs₁ hs₂)) hb
  have heq : 2 * (ℓ : ℝ) * (C₀ * (4 * (ℓ : ℝ)) ^ 2) =
      (32 * C₀) * (ℓ : ℝ) ^ 3 := by ring
  rw [Real.log_mul hvρ.ne' (mul_pos hs₁ hs₂).ne', Real.log_mul hs₁.ne' hs₂.ne',
    heq, Real.log_pow, Real.log_mul hcpos.ne' (pow_pos hℓpos 3).ne', Real.log_pow,
    log_of_sq hsq₁, log_of_sq hsq₂] at hlog
  norm_num at hlog
  linarith only [hlog, hv₁, hv₂, neg_abs_le (Real.log (v (genC' P x))),
    neg_abs_le (Real.log (v (genC' P x - 1)))]

end AbcAdaptation.Tripod.Cyclic
