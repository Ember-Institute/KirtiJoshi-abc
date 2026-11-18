/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicLegendreValuation
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TripodalCompactValuation
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeDegreeTower
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

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
    (hw : w ∈ (P.curve x).badAll) (hw2 : residueChar w = 2) :
    ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (residueChar w) ≤
      4 * K.c * localDeg (P.curve x).F w := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder w with h𝔭
  have hw𝔭 : FinitePlace.LiesOver w 𝔭 := liesOver_placeUnder w
  have h𝔭2 : residueChar 𝔭 = 2 := by rw [← residueChar_eq_of_liesOver hw𝔭, hw2]
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
