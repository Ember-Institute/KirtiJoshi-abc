/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 31–41, and OrbicurveCores/S1/LocalForm.lean
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Complex Filter
open scoped Topology

/-- The branching orders over the modular `j`-line. -/
noncomputable def sig (w : ℂ) : ℕ := if w = 0 then 3 else if w = 1728 then 2 else 1

theorem sig_pos (w : ℂ) : 0 < sig w := by
  unfold sig
  split_ifs <;> norm_num

/-- A local normal form is a constant plus a power of a local analytic coordinate. -/
def HasLocalForm (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z = 0 ∧ deriv g z ≠ 0 ∧
    ∀ᶠ z' in 𝓝 z, f z' = f z + g z' ^ n

private theorem exists_analyticAt_pow_eq {φ : ℂ → ℂ} {z : ℂ}
    (hφ : AnalyticAt ℂ φ z) (h0 : φ z ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z ∧ ψ z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, ψ x ^ n = φ x := by
  let c : ℂ := φ z ^ ((n : ℂ)⁻¹)
  have hc : c ^ n = φ z := Complex.cpow_nat_inv_pow _ hn
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hc
    exact h0 hc.symm
  have hq : AnalyticAt ℂ (fun x ↦ φ x / φ z) z := hφ.div_const
  have hq1 : φ z / φ z ∈ slitPlane := by rw [div_self h0]; exact one_mem_slitPlane
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨fun x ↦ c * exp (log (φ x / φ z) / n), ?_, mul_ne_zero hc0 (exp_ne_zero _), ?_⟩
  · exact analyticAt_const.mul ((hq.clog hq1).div_const.cexp')
  · filter_upwards [hφ.continuousAt.eventually_ne h0] with x hx
    rw [mul_pow, ← exp_nat_mul, hc, mul_div_cancel₀ _ hnC, exp_log (div_ne_zero hx h0),
      mul_div_cancel₀ _ h0]

theorem HasLocalForm.analyticAt {f : ℂ → ℂ} {z : ℂ} {n : ℕ} (h : HasLocalForm f z n) :
    AnalyticAt ℂ f z := by
  obtain ⟨g, hg, -, -, hf⟩ := h
  exact (analyticAt_const.add (hg.pow n)).congr (hf.mono fun _ h ↦ h.symm)

/-- A nonzero derivative gives a local normal form of order one. -/
theorem hasLocalForm_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hd : deriv f z ≠ 0) :
    HasLocalForm f z 1 := by
  refine ⟨fun x ↦ f x - f z, hf.sub analyticAt_const, sub_self _, ?_, ?_⟩
  · rwa [deriv_sub_const]
  · exact Eventually.of_forall fun x ↦ by rw [pow_one, add_sub_cancel]

/-- Absorb a nonvanishing analytic factor into the power of a local coordinate. -/
theorem hasLocalForm_of_eq_pow_mul {f P φ : ℂ → ℂ} {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hP : AnalyticAt ℂ P z) (hP0 : P z = 0) (hP' : deriv P z ≠ 0)
    (hφ : AnalyticAt ℂ φ z) (hφ0 : φ z ≠ 0)
    (hf : ∀ᶠ x in 𝓝 z, f x = f z + P x ^ n * φ x) : HasLocalForm f z n := by
  obtain ⟨ψ, hψ, hψ0, hψn⟩ := exists_analyticAt_pow_eq hφ hφ0 hn
  refine ⟨fun x ↦ P x * ψ x, hP.mul hψ, by simp [hP0], ?_, ?_⟩
  · have hd := hP.differentiableAt.hasDerivAt.mul hψ.differentiableAt.hasDerivAt
    rw [show (fun x ↦ P x * ψ x) = P * ψ from rfl, hd.deriv, hP0, zero_mul, add_zero]
    exact mul_ne_zero hP' hψ0
  · filter_upwards [hf, hψn] with x hx hψx
    rw [hx, mul_pow, hψx]

/-- Precomposition with a local analytic coordinate preserves the order. -/
theorem HasLocalForm.comp {f q : ℂ → ℂ} {z : ℂ} {n : ℕ} (hf : HasLocalForm f (q z) n)
    (hq : AnalyticAt ℂ q z) (hq' : deriv q z ≠ 0) : HasLocalForm (f ∘ q) z n := by
  obtain ⟨g, hg, hg0, hg', hfg⟩ := hf
  refine ⟨g ∘ q, hg.comp hq, hg0, ?_, hq.continuousAt.eventually hfg⟩
  rw [deriv_comp z hg.differentiableAt hq.differentiableAt]
  exact mul_ne_zero hg' hq'

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
