/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/
import Solutions.Source_FermatLocalValuedPlace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source.Local

open Filter Topology

section Limit

variable {K : Type*} [Field K] {E : Type*} [NormedField E]
variable {x : ℕ → EPlace K E} {ξ : K → Option E}

/-- Limits of values are additive. -/
theorem limit_add (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f + g) = some (α + β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f + g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n + b n, ?_, hla.add hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_add hna hnb

/-- Limits of values are multiplicative. -/
theorem limit_mul (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f g : K} {α β : E}
    (hf : ξ f = some α) (hg : ξ g = some β) : ξ (f * g) = some (α * β) := by
  have hf' := h f
  have hg' := h g
  rw [hf, tendstoP1_some_iff'] at hf'
  rw [hg, tendstoP1_some_iff'] at hg'
  obtain ⟨a, ha, hla⟩ := hf'
  obtain ⟨b, hb, hlb⟩ := hg'
  refine (h (f * g)).unique (tendstoP1_some_iff'.mpr ⟨fun n => a n * b n, ?_, hla.mul hlb⟩)
  filter_upwards [ha, hb] with n hna hnb
  exact (x n).val_mul hna hnb

theorem limit_neg (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {α : E}
    (hf : ξ f = some α) : ξ (-f) = some (-α) := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h (-f)).unique (tendstoP1_some_iff'.mpr ⟨fun n => -a n, ?_, hla.neg⟩)
  filter_upwards [ha] with n hna
  exact (x n).val_neg hna

theorem limit_one (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 1 = some 1 :=
  (h 1).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 1,
    Eventually.of_forall fun n => (x n).val_one, tendsto_const_nhds⟩)

theorem limit_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ξ 0 = some 0 :=
  (h 0).unique (tendstoP1_some_iff'.mpr ⟨fun _ => 0,
    Eventually.of_forall fun n => (x n).val_zero, tendsto_const_nhds⟩)

/-- `ξ f = 0` implies `ξ f⁻¹ = ∞`. -/
theorem limit_inv_of_eq_zero (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf0 : f ≠ 0) (hf : ξ f = some 0) : ξ f⁻¹ = none := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  refine (h f⁻¹).unique fun R => ?_
  have hsmall : ∀ᶠ n in atTop, ‖a n‖ < (max R 1)⁻¹ := by
    have := (tendsto_norm_zero.comp hla).eventually (gt_mem_nhds (a := (max R 1)⁻¹)
      (by positivity))
    simpa using this
  filter_upwards [ha, hsmall] with n hn hsm α hα
  by_cases h0 : a n = 0
  · rw [h0] at hn
    rw [(x n).val_inv_of_eq_zero hf0 hn] at hα
    cases hα
  · rw [(x n).val_inv_of_ne_zero hn h0] at hα
    cases hα
    rw [norm_inv]
    have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr h0
    have h1 : 1 ≤ max R 1 := le_max_right _ _
    have h2 : max R 1 < ‖a n‖⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) hpos]
      exact hsm
    exact lt_of_le_of_lt (le_max_left _ _) h2

/-- `ξ f = ∞` implies `ξ f⁻¹ = 0`. -/
theorem limit_inv_of_eq_none (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K}
    (hf : ξ f = none) : ξ f⁻¹ = some 0 := by
  have hf' := h f
  rw [hf] at hf'
  refine (h f⁻¹).unique (fun ε hε => ?_)
  filter_upwards [hf' ε⁻¹] with n hn
  cases hv : (x n).val f with
  | none => exact ⟨0, (x n).val_inv_of_eq_none hv, by simpa using hε⟩
  | some α =>
    have hα := hn α hv
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp only [norm_zero] at hα
      have : 0 < ε⁻¹ := inv_pos.mpr hε
      linarith
    refine ⟨α⁻¹, (x n).val_inv_of_ne_zero hv hα0, ?_⟩
    rw [sub_zero, norm_inv]
    exact (inv_lt_comm₀ hε (norm_pos_iff.mpr hα0)).mp hα

/-- **The limit valuation subring** `O_ξ = {f | ξ f ≠ ∞}`. -/
def limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) : ValuationSubring K where
  carrier := {f | ξ f ≠ none}
  add_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_add h hα hβ]
  zero_mem' := by simp [limit_zero h]
  mul_mem' {f g} hf hg := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hg
    simp [limit_mul h hα hβ]
  one_mem' := by simp [limit_one h]
  neg_mem' {f} hf := by
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hf
    simp [limit_neg h hα]
  mem_or_inv_mem' f := by
    by_cases hf : ξ f = none
    · right
      simp [limit_inv_of_eq_none h hf]
    · exact Or.inl hf

theorem mem_limitSubring (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} :
    f ∈ limitSubring h ↔ ξ f ≠ none := Iff.rfl

/-- **Bounds away from `0`, `1`, `∞`**: if `ξ f ∉ {0, 1, ∞}`, then eventually
`|log ‖f(x n)‖|` and `|log ‖f(x n) − 1‖|` are bounded. -/
theorem eventually_abs_log_le (h : ∀ f, TendstoP1 (fun n => (x n).val f) (ξ f)) {f : K} {β : E}
    (hf : ξ f = some β) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (x n).val f = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hf' := h f
  rw [hf, tendstoP1_some_iff'] at hf'
  obtain ⟨a, ha, hla⟩ := hf'
  have hb0 : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
  have hb1 : 0 < ‖β - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hβ1)
  set δ := min ‖β‖ ‖β - 1‖ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hclose : ∀ᶠ n in atTop, ‖a n - β‖ < δ := by
    have := (Metric.tendsto_nhds.mp hla) δ hδpos
    simpa [dist_eq_norm] using this
  refine ⟨max (|Real.log (‖β‖ / 2)|) (|Real.log (‖β‖ * 2)|) +
    max (|Real.log (‖β - 1‖ / 2)|) (|Real.log (‖β - 1‖ * 2)|), ?_⟩
  filter_upwards [ha, hclose] with n hn hc
  have hδ1 : δ ≤ ‖β‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ ‖β - 1‖ / 2 := by
    rw [hδ]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlog : ∀ {t A B : ℝ}, 0 < A → A ≤ t → t ≤ B → |Real.log t| ≤ max |Real.log A| |Real.log B| :=
    fun {t A B} hA hAt htB => abs_le_max_abs_abs (Real.log_le_log hA hAt)
      (Real.log_le_log (hA.trans_le hAt) htB)
  have hnear : ∀ {u v : E}, ‖u - v‖ < ‖v‖ / 2 → ‖v‖ / 2 ≤ ‖u‖ ∧ ‖u‖ ≤ ‖v‖ * 2 := by
    intro u v huv
    have h1 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
      calc ‖v‖ = ‖u - (u - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - v‖ := norm_sub_le _ _
    have h2 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
      calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
        _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
    constructor <;> nlinarith [norm_nonneg v, norm_nonneg (u - v)]
  obtain ⟨h1, h2⟩ := hnear (u := a n) (v := β) (lt_of_lt_of_le hc hδ1)
  have hc' : ‖(a n - 1) - (β - 1)‖ < ‖β - 1‖ / 2 := by
    rw [sub_sub_sub_cancel_right]
    exact lt_of_lt_of_le hc hδ2
  obtain ⟨h3, h4⟩ := hnear hc'
  refine ⟨a n, hn, ?_, ?_, ?_, ?_⟩
  · have := hlog (by positivity) h1 h2
    have h0 : 0 ≤ max |Real.log (‖β - 1‖ / 2)| |Real.log (‖β - 1‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · have := hlog (by positivity) h3 h4
    have h0 : 0 ≤ max |Real.log (‖β‖ / 2)| |Real.log (‖β‖ * 2)| :=
      le_max_of_le_left (abs_nonneg _)
    linarith
  · intro h0
    rw [h0, norm_zero] at h1
    linarith
  · intro h0
    rw [h0, sub_self, norm_zero] at h3
    linarith

end Limit


end AbcAdaptation.Tripod.Fermat.Proper.Source.Local
