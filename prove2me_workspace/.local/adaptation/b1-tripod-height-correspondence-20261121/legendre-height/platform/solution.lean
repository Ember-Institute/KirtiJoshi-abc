/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by the current reference adaptation:
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
Source: Iut/Tripod/Height.lean:791. The numerical estimates below
reuse the existing adaptations of the source lemmas.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp
import Definitions.Def_TripodLegendreHeightBasics
import Theorems.Thm_AbcAdaptation_Tripod_h_eq_finHeight_div
import Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteLowerBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreArchimedeanTripleBound
import Theorems.Thm_AbcAdaptation_Tripod_legendreZeroJRootOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference NumberField

private lemma finHeight_legendreJ_le (x : Pt) :
    finHeight (legendreJ (gen x.1)) ≤
      2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) :=
  legendreFiniteUpperBound x

private lemma finHeight_legendreJ_ge {K : CompactlyBounded} {x : Pt}
    (hx : x ∈ K.set) (hj : legendreJ (gen x.1) ≠ 0) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) ≤
      finHeight (legendreJ (gen x.1)) + 6 * K.c * K.V.card * deg x.1 :=
  legendreFiniteLowerBound K x hx hj

private lemma logHeight₁_le_finHeight_add {K : CompactlyBounded} {x : Pt}
    (hx : x ∈ K.set) :
    Height.logHeight₁ (gen x.1) ≤ finHeight (gen x.1) + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1)⁻¹ ≤ finHeight (gen x.1)⁻¹ + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1 - 1)⁻¹ ≤ finHeight (gen x.1 - 1)⁻¹ + K.c * deg x.1 :=
  legendreArchimedeanTripleBound K x hx

private lemma pow_six_eq_one_of_legendreJ_eq_zero {x : Pt}
    (_hl0 : gen x.1 ≠ 0) (_hl1 : gen x.1 ≠ 1)
    (hj : legendreJ (gen x.1) = 0) : gen x.1 ^ 6 = 1 :=
  legendreZeroJRootOfUnity x hj

theorem solution (P : CurveProviders) (K : CompactlyBounded) : LegendreHeightHyp P K := by
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
