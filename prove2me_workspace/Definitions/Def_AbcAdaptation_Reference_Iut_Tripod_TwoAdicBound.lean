/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicLocalTerm
import Solutions.Source_TripodFinitePrimeCounting
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem twoAdicBound' (K : CompactlyBounded) : TwoAdicBoundHyp P K (4 * K.c) := by
  intro x hx
  classical
  have hc := CompactlyBounded.c_nonneg hx
  change (∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
      (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
        (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))) /
      (Module.finrank ℚ (P.curve x).F : ℝ) ≤ 4 * K.c
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos)]
  calc ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
        (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
          (inertDeg (P.curve x).F w : ℝ) * Real.log (residueChar w))
      ≤ ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          4 * K.c * (localDeg (P.curve x).F w : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw
        split_ifs with h
        · exact term_le P x hx h hw.2
        · exact absurd hw.1 h
    _ = 4 * K.c * ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => residueChar w = 2),
          (localDeg (P.curve x).F w : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * K.c * (Module.finrank ℚ (P.curve x).F : ℝ) := by
        let S : Finset (FinitePlace (P.curve x).F) := (P.arith x).badAll_finite.toFinset
        have hcast : ((∑ w ∈ S.filter (fun w => residueChar w = 2),
            localDeg (P.curve x).F w : ℕ) : ℝ) ≤ (Module.finrank ℚ (P.curve x).F : ℝ) :=
          Nat.cast_le.mpr (sum_localDeg_filter_le S 2)
        have hsum := (Nat.cast_sum (R := ℝ) (S.filter fun w => residueChar w = 2)
          (localDeg (P.curve x).F)).symm.trans_le hcast
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hc)

/-- **The `2`-adic bound** in the form `TwoAdicBoundHyp P K (max (4c) 0)`, with a nonnegative
bound. -/
theorem twoAdicBound (K : CompactlyBounded) : TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  fun x hx => (twoAdicBound' P K x hx).trans (le_max_left _ _)

end AbcAdaptation.Tripod
