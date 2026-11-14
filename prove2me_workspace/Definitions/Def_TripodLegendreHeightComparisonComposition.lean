/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
/- Full source parent composition, adapted from Iut/Tripod/Height.lean:791-840.
Uncompiled draft. The mathematical frontier is exactly four stated source lemmas.
The source provider rewrite h_eq_finHeight_div is unnecessary because our
auxiliaryHeight is definitionally the already rewritten finHeight(j)/deg.
-/
import Definitions.Def_TripodLegendreHeightBasics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open NumberField

namespace AbcAdaptation.Tripod

theorem canonicalLegendreHeightComparison_of_source_children
    (hUpper : LegendreFiniteUpperBound)
    (hLower : LegendreFiniteLowerBound)
    (hArch : LegendreArchimedeanTripleBound)
    (hZero : LegendreZeroJRootOfUnity) : CanonicalLegendreHeightComparison := by
  intro K
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have upper : ∀ x : Pt,
      (1 / 6 : ℝ) * auxiliaryHeight x ≤ htCan x + Real.log 2 / 3 := by
    intro x
    rw [auxiliaryHeight, htCan]
    have hd := deg_pos_real x.1
    have h1 := hUpper x
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
  have lower : ∀ x : Pt, x ∈ K.set →
      htCan x ≤ (1 / 6 : ℝ) * auxiliaryHeight x +
        (K.c * K.V.card + K.c + Real.log 2 / 3) := by
    intro x hx
    rw [auxiliaryHeight, htCan]
    have hd := deg_pos_real x.1
    have hc := CompactlyBounded.c_nonneg hx
    have hcV : 0 ≤ K.c * K.V.card := mul_nonneg hc (Nat.cast_nonneg _)
    by_cases hj : legendreJ (gen x.1) = 0
    · have hg6 : gen x.1 ^ 6 = 1 := hZero x hj
      have h0 : Height.logHeight₁ (gen x.1) = 0 := by
        have := Height.logHeight₁_pow (gen x.1) 6
        rw [hg6, Height.logHeight₁_one] at this
        push_cast at this
        linarith
      rw [h0, hj, finHeight_zero, zero_div, mul_zero, zero_add]
      linarith
    have h1 := hLower K x hx hj
    obtain ⟨h2, h3, h4⟩ := hArch K x hx
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
  refine ⟨max (Real.log 2 / 3) (K.c * K.V.card + K.c + Real.log 2 / 3), ?_⟩
  intro x hx
  rw [abs_le]
  constructor
  · have hl := lower x hx
    have hb := le_max_right (Real.log 2 / 3) (K.c * K.V.card + K.c + Real.log 2 / 3)
    linarith
  · have hu := upper x
    have hb := le_max_left (Real.log 2 / 3) (K.c * K.V.card + K.c + Real.log 2 / 3)
    linarith

end AbcAdaptation.Tripod
