/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Unipotent.lean
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Solutions.Source_ReferenceIutCanLiftUnipotent

set_option autoImplicit false

open Filter Topology OnePoint
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

lemma tendsto_uU_zero {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun j ↦ SL2R.uU (t j)) atTop (𝓝 1) := by
  have := (SL2R.continuous_uU.tendsto 0).comp ht
  rwa [show SL2R.uU 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [SL2R.uU]] at this

open UnipotentRigidity in
/-- **No continuous extension over `ℚ_p`.** A homomorphism `SL(2, ℝ) → PGL(2, ℚ_p)` with
`Φ(u₂)` the translation by `2` cannot have `g ↦ Φ(g) y` continuous. -/
theorem padic_contradiction {p : ℕ} [Fact p.Prime] [DecidableEq ℚ_[p]]
    {Φ : SL(2, ℝ) → GL (Fin 2) ℚ_[p]}
    (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint ℚ_[p], Φ (g * h) • y = Φ g • Φ h • y)
    (hcont : ∀ y : OnePoint ℚ_[p], Continuous fun g ↦ Φ g • y) (h2 : IsTransl Φ 2 2) :
    False := by
  set q : ℕ → ℚ := fun j ↦ 2 / (p : ℚ) ^ j
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : Tendsto (fun j ↦ ((q j : ℚ) : ℝ)) atTop (𝓝 0) := by
    simp only [q, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (p : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hp)).const_mul 2
    simpa [div_eq_mul_inv, inv_pow] using this
  have hlim := ((hcont ((0 : ℚ_[p]) : OnePoint ℚ_[p])).tendsto 1).comp (tendsto_uU_zero hq)
  simp only [Function.comp_def, smul_one' hΦ] at hlim
  have e : ∀ j, Φ (SL2R.uU ((q j : ℚ) : ℝ)) • ((0 : ℚ_[p]) : OnePoint ℚ_[p]) =
      (((q j : ℚ) : ℚ_[p]) : OnePoint ℚ_[p]) := by
    intro j
    rw [smul_uU_rat hΦ h2 (q j), transl_smul_coe, zero_add]
  simp only [e] at hlim
  have hlim' : Tendsto (fun j ↦ ((q j : ℚ) : ℚ_[p])) atTop (𝓝 0) :=
    (OnePoint.isOpenEmbedding_coe (X := ℚ_[p])).isInducing.tendsto_nhds_iff.2 hlim
  have hn := (continuous_norm.tendsto _).comp hlim'
  simp only [Function.comp_def, norm_zero] at hn
  have h2p : (0 : ℝ) < ‖(2 : ℚ_[p])‖ := norm_pos_iff.2 two_ne_zero
  obtain ⟨j, hj⟩ := (hn.eventually (gt_mem_nhds h2p)).exists
  apply lt_irrefl ‖(2 : ℚ_[p])‖
  calc ‖(2 : ℚ_[p])‖ ≤ ‖(((q j : ℚ) : ℚ_[p]))‖ := by
        simp only [q, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, norm_div,
          norm_pow, _root_.Padic.norm_p]
        rw [inv_pow, div_inv_eq_mul]
        exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hp.le)
    _ < ‖(2 : ℚ_[p])‖ := hj

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
