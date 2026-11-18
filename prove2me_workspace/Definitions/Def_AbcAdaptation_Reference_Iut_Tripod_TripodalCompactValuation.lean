/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TripodalPlaceTransport
import Solutions.Source_TripodFinitePlaceArithmetic
import Definitions.Def_TripodLegendreHeightBasics

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
    (𝔭 : FinitePlace (tpd P x)) (h𝔭 : residueChar 𝔭 ∈ K.V) :
    |((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c ∧
      |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (residueChar 𝔭)) ≤ K.c := by
  have hb := hx.1 (tpdPlace P x 𝔭) (by rwa [residueChar_tpdPlace])
  rw [tpdPlace_gen, tpdPlace_gen_sub_one, log_apply_eq _ (genT_ne_zero P x),
    log_apply_eq _ (genT_sub_one_ne_zero P x)] at hb
  have hpos : 0 ≤ (inertDeg (tpd P x) 𝔭 : ℝ) * Real.log (residueChar 𝔭) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  obtain ⟨h1, h2⟩ := hb
  rw [abs_mul, abs_of_nonneg hpos] at h1 h2
  exact ⟨h1, h2⟩

end AbcAdaptation.Tripod
