/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Exact c2 parent reduction draft. theorem110 is the Open semantic child.
   Public helpers refer to accepted platform nodes; this file has no c2 import. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22
import Theorems.Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection
import Theorems.Thm_AbcAdaptation_Reference_Iut_epsilonE_le
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_half_of_pos
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_self_of_pos
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_bound_ell
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_le_four_mul_sqrt_sqrt
import Theorems.Thm_AbcAdaptation_Reference_Iut_log_ell_bound
import Theorems.Thm_AbcAdaptation_Reference_Iut_p5_height_bound
import Theorems.Thm_AbcAdaptation_Reference_Iut_c2_final
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_theorem110
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators
open AbcAdaptation.Reference
open AbcAdaptation.Reference.Iut
open Finset Real
universe u v w

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

private lemma eStar_cast : (inv.eStar : ℝ) = 552960 * inv.emod := by
  simp only [eStar]; push_cast; ring

end AbcAdaptation.Reference.Iut.Theorem110Invariants

namespace AbcAdaptation.Reference.Iut.LocalHeightData

private lemma height_eq_add (L : LocalHeightData) (a b : ℕ) (hab : a ≠ b) :
    L.height = L.heightEq a + L.heightEq b + L.heightOther a b := by
  classical
  unfold height heightEq heightOther
  rw [← add_div, ← add_div]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not L.bad (fun v => L.p v = a),
    ← Finset.sum_filter_add_sum_filter_not (L.bad.filter fun v => ¬ L.p v = a)
      (fun v => L.p v = b), Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  exact Finset.sum_congr (Finset.filter_congr fun v _ =>
    ⟨fun h => h.2, fun h => ⟨fun h' => hab (h'.symm.trans h), h⟩⟩) fun _ _ => rfl

end AbcAdaptation.Reference.Iut.LocalHeightData

theorem solution
    {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d)
    {P : Corollary312VariantData.{u, v} AG TG → Prop} (hd : 1 ≤ d)
    (ex : ThetaDataExistence P I) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d) (hxe : x ∉ I.excCore)
    (hH : I.threshold cheb ≤ I.h x) :
    1 / 6 * I.h x ≤ (1 + epsilonE (deltaBound d) (I.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) + (40 * pnt.η + I.B / 3) ∧
      epsilonE (deltaBound d) (I.h x) ≤ 1 ∧
      0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x := by
  classical
  -- notation and the size of `h`
  obtain ⟨L, hLdef⟩ : ∃ L, L = I.localData x hx := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = I.h x := ⟨_, rfl⟩
  rw [← hhdef] at hH ⊢
  have hδ : (2 : ℝ) ≤ deltaBound d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold deltaBound; nlinarith
  have hδ1 : (1 : ℝ) ≤ deltaBound d := by linarith
  have hLh : L.height = h := by rw [hLdef, hhdef]; exact I.localData_height x hx
  have hξ2 : cheb.ξ ^ 2 ≤ h := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hH)
  have hT : 49 + 8 * max I.TK 0 + I.B ≤ h :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hH)
  have hB0 := I.B_nonneg
  have hP5 : (I.B + 11 + 2 * deltaBound d) ^ 4 + 1 ≤ h :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hH)
  have hε1 : ((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4)) ^ 4 + 1 ≤ h :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hH)
  have hξ5 := cheb.five_le
  have hh25 : 25 ≤ h := by nlinarith
  have hh1 : 1 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  -- consume the fourth-power thresholds now, and drop them from the context
  have hε1' : epsilonE (deltaBound d) h ≤ 1 := epsilonE_le hδ1 one_pos (by
    have : ((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4) / 1) ^ 4 ≤ h := by
      rw [div_one]; linarith
    exact this) hh1
  have hP5big : ¬ h ≤ (I.B + 11 + 2 * deltaBound d) ^ 4 := fun hle => by linarith
  clear hε1 hP5 hH
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt h := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hrdef ▸ Real.sqrt_nonneg _
  have hrr : r * r = h := hrdef ▸ Real.mul_self_sqrt hh0.le
  have hξr : cheb.ξ ≤ r := by
    rw [hrdef]; exact Real.le_sqrt_of_sq_le hξ2
  have hr5 : 5 ≤ r := hξ5.trans hξr
  have hr7 : 7 ≤ r := by nlinarith [le_max_left I.TK 0, le_max_right I.TK 0]
  have hlog1 : 1 ≤ Real.log (2 * deltaBound d * h) := by
    have : Real.exp 1 ≤ 2 * deltaBound d * h := by
      have := Real.exp_one_lt_d9; nlinarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  -- the prime `ℓ` ((P1)–(P3))
  have hdeg : (L.deg : ℝ) ≤ deltaBound d := by
    have := I.localData_deg_le x hx
    rw [hLdef]; unfold deltaBound; exact_mod_cast this
  obtain ⟨ℓ, hℓp, hℓlo, hℓhi, hP2, hP3⟩ :=
    L.exists_prime_selection cheb (deltaBound d) hδ hdeg (by rw [hLh, ← hrdef]; exact hξr)
  rw [hLh, ← hrdef] at hℓlo hℓhi hP3
  have hℓ5 : (5 : ℝ) ≤ ℓ := hr5.trans hℓlo
  have hℓ7r : (7 : ℝ) ≤ ℓ := hr7.trans hℓlo
  have hℓ7 : 7 ≤ ℓ := by exact_mod_cast hℓ7r
  have hℓ2 : ℓ ≠ 2 := by omega
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  -- (P4): no `ℓ`-cyclic subgroup scheme, since `h` is large
  have hP4 : ¬ I.HasCyclicSubgroup x ℓ := by
    intro hcyc
    have hb := I.cyclic_bound x hx ℓ hℓp hℓ7 (hLdef ▸ hP2) hcyc
    rw [← hhdef, ← hLdef] at hb
    have h₂ : L.heightEq 2 ≤ I.B := hLdef ▸ I.heightEq_two_le x hx
    set g := h - L.heightEq 2 with hg
    have hlogℓ : Real.log ℓ ≤ ℓ - 2 := by
      have := log_le_half_of_pos (by linarith : (0:ℝ) < ℓ); linarith
    -- `(ℓ-2)/24 · g ≤ 2 log ℓ + T_K ≤ 2(ℓ-2) + T_K`, so `g ≤ 48 + 24 T_K/(ℓ-2) ≤ 48 + 8 T_K`,
    -- where `g = h − log(q₂) ≥ h − B_K`
    have hTK : I.TK ≤ max I.TK 0 := le_max_left _ _
    have hmax0 : 0 ≤ max I.TK 0 := le_max_right _ _
    have hℓ2' : (5 : ℝ) ≤ ℓ - 2 := by linarith
    have h1 : (ℓ - 2 : ℝ) * g ≤ 24 * (2 * (ℓ - 2) + max I.TK 0) := by
      have : (ℓ - 2 : ℝ) / 24 * g ≤ 2 * (ℓ - 2) + max I.TK 0 := by linarith
      linarith
    have h2 : 24 * (2 * (ℓ - 2) + max I.TK 0) ≤ (ℓ - 2 : ℝ) * (48 + 8 * max I.TK 0) := by
      nlinarith
    have := le_of_mul_le_mul_left (h1.trans h2) (by linarith : (0:ℝ) < ℓ - 2)
    linarith
  -- (P5): some bad place away from `2` and `ℓ`, since `h` is large
  have hℓup : (ℓ : ℝ) ≤ 20 * deltaBound d ^ 2 * h ^ 2 := by
    have h1 : Real.log (2 * deltaBound d * h) ≤ 2 * deltaBound d * h :=
      log_le_self_of_pos (by positivity)
    have h2 : r ≤ h := by nlinarith [mul_nonneg hr0 (by linarith : (0:ℝ) ≤ r - 1)]
    calc (ℓ : ℝ) ≤ 10 * deltaBound d * r * Real.log (2 * deltaBound d * h) := hℓhi
      _ ≤ 10 * deltaBound d * r * (2 * deltaBound d * h) := by gcongr
      _ = 20 * deltaBound d ^ 2 * (r * h) := by ring
      _ ≤ 20 * deltaBound d ^ 2 * (h * h) := by gcongr
      _ = 20 * deltaBound d ^ 2 * h ^ 2 := by ring
  have hlogℓ6 : Real.log ℓ ≤ 6 * Real.log (2 * deltaBound d * h) :=
    (Real.log_le_log (by linarith) hℓup).trans (log_bound_ell hδ1 hh1)
  -- the part of the height over `ℓ` is at most `√h · log ℓ`
  have hheightℓ : L.heightEq ℓ ≤ r * Real.log ℓ := by
    have hbound : ∀ v ∈ L.bad.filter (fun v => L.p v = ℓ),
        (L.hv v : ℝ) * L.f v * Real.log (L.p v) ≤ r * Real.log ℓ * L.f v := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [hv.2]
      have := hP3 v hv.1 hv.2
      have hf : (0 : ℝ) ≤ L.f v := by positivity
      nlinarith [mul_nonneg hf hlogℓ0]
    unfold LocalHeightData.heightEq
    rw [div_le_iff₀ (by exact_mod_cast L.one_le_deg)]
    calc ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), (L.hv v : ℝ) * L.f v * Real.log (L.p v)
        ≤ ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), r * Real.log ℓ * L.f v :=
          Finset.sum_le_sum hbound
      _ = r * Real.log ℓ * ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), (L.f v : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ r * Real.log ℓ * L.deg := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast L.sum_f_le ℓ
  have hsplit := L.height_eq_add 2 ℓ hℓ2.symm
  rw [hLh] at hsplit
  have hP5' : ∃ v ∈ L.bad, L.p v ≠ 2 ∧ L.p v ≠ ℓ := by
    by_contra hnone
    push Not at hnone
    have hother : L.heightOther 2 ℓ = 0 := by
      unfold LocalHeightData.heightOther
      rw [Finset.filter_false_of_mem, Finset.sum_empty, zero_div]
      intro v hv ⟨h1, h2⟩
      exact h2 (hnone v hv h1)
    -- `h ≤ B + √h·log ℓ ≤ B + (3 + 2δ)√h + 8 h^{3/4}`, contradicting `h ≥ (B+11+2δ)⁴+1`
    have hB2 : L.heightEq 2 ≤ I.B := hLdef ▸ I.heightEq_two_le x hx
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt r := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := hsdef ▸ Real.sqrt_nonneg _
    have hss : s * s = r := hsdef ▸ Real.mul_self_sqrt hr0
    have hlogh : Real.log h ≤ 4 * s := by
      have := log_le_four_mul_sqrt_sqrt hh1
      rw [← hrdef, ← hsdef] at this; exact this
    have hlogℓ' : Real.log ℓ ≤ 3 + 2 * deltaBound d + 8 * s :=
      log_ell_bound hδ1 hh1 (by linarith) hℓup hlogh
    have hmain : h ≤ I.B + r * Real.log ℓ := by linarith
    exact hP5big (p5_height_bound I.B_nonneg hδ1 hr0 hrr hs0 hss hh1 hlogℓ' hmain)
  -- (P6) and the Θ-data
  have hP6 : I.SL2Image x ℓ := by
    subst hLdef
    exact I.sl2_of x hx ℓ hℓp (by exact_mod_cast hℓ5) hP2 hP4 hP5'
  obtain ⟨X, inv, hPX, cert, ⟨est⟩, hXℓ, hXd, hXq, hDiff, hCond1, hCond2⟩ :=
    ex.thetaData x hx hxe ℓ hℓp hℓ7 (hLdef ▸ hP2) (by rw [← hLdef, ← hhdef, ← hrdef]; exact hP3)
      (hLdef ▸ hP5') hP6
  rw [← hLdef] at hXq
  -- Theorem 1.10
  have h110 := inv.theorem110 cert est pnt (h312 X hPX)
  rw [hXℓ, hXq] at h110
  -- the numerical factors of Theorem 1.10 in terms of `δ`
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdmod : 20 * (X.dmod : ℝ) ≤ deltaBound d := by
    have : (X.dmod : ℝ) ≤ d := by exact_mod_cast hXd
    unfold deltaBound; linarith
  have heStar : (inv.eStar : ℝ) ≤ deltaBound d := by
    have h1 : (inv.emod : ℝ) ≤ X.dmod := by exact_mod_cast inv.emod_le_dmod
    have h2 : (X.dmod : ℝ) ≤ d := by exact_mod_cast hXd
    rw [inv.eStar_cast]; unfold deltaBound; linarith
  have hDF0 : 0 ≤ inv.logDtpd + inv.logFtpd := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  -- `h ≤ log(q) + B + 6·√h·log(2δh)`
  have hlogQ : h ≤ L.heightOther 2 ℓ + I.B + 6 * (r * Real.log (2 * deltaBound d * h)) := by
    have hB2 : L.heightEq 2 ≤ I.B := hLdef ▸ I.heightEq_two_le x hx
    have := mul_le_mul_of_nonneg_left hlogℓ6 hr0
    linarith
  have hLC0 : 0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  refine ⟨?_, hε1', hLC0⟩
  exact c2_final (by linarith) hrr hlog1 hδ1 hℓlo hℓhi hdmod heStar hDF0 I.B_nonneg
    (by linarith [pnt.one_lt_η]) h110 hlogQ hDiff hCond1 (by rw [epsilonE, hrdef]) hε1'
