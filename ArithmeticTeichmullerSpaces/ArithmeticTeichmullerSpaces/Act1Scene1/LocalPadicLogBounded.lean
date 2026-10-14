/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: only the discrete norm gap and uniform principal-unit log bound;
independent namespace, existing logarithm and exact imports.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogHomomorphism
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
source-id: JT-SCENE1-LOCAL-PADIC-LOG-BOUNDED
source: discrete local-field logarithm bounds used for Kummer nonvanishing.
fidelity: proves a uniform bound for the existing ordinary logarithm over
all principal units, using the discrete valuation group. No bound is supplied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable {p : ℕ}

/-- **Discreteness**: there is `ρ < 1` with `‖a‖ ≤ ρ` for every `a` with `‖a‖ < 1` (the norm
of a uniformizer, when one exists; in general `‖p‖^{1/e}` with `v(p) = ofAdd (-e)`). -/
theorem exists_lt_one_forall_norm_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ a : k, ‖a‖ < 1 → ‖a‖ ≤ ρ := by
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hvp : Valued.v (p : k) ≠ 0 := (Valuation.ne_zero_iff _).2 hp0
  have hvp1 : Valued.v (p : k) < 1 := Valued.toNormedField.norm_lt_one_iff.1 hpk
  obtain ⟨γ, hγ⟩ : ∃ γ : Multiplicative ℤ, Valued.v (p : k) = γ :=
    ⟨WithZero.unzero hvp, (WithZero.coe_unzero hvp).symm⟩
  have hγ1 : γ < 1 := by
    rw [← WithZero.coe_lt_coe, ← hγ, WithZero.coe_one]
    exact hvp1
  have hγ2 : Multiplicative.toAdd γ < 0 := by
    rwa [← Multiplicative.toAdd_lt, toAdd_one] at hγ1
  set e : ℕ := (-Multiplicative.toAdd γ).toNat with he
  have he' : (e : ℤ) = -Multiplicative.toAdd γ := Int.toNat_of_nonneg (by omega)
  have he0 : 0 < e := by omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast he0
  have hp0' : 0 ≤ ‖(p : k)‖ := norm_nonneg _
  refine ⟨‖(p : k)‖ ^ ((e : ℝ)⁻¹), Real.rpow_nonneg hp0' _,
    Real.rpow_lt_one hp0' hpk (by positivity), fun a ha => ?_⟩
  rw [Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hp0' hepos, Real.rpow_natCast, ← norm_pow,
    Valued.toNormedField.norm_le_iff, Valuation.map_pow]
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [map_zero, zero_pow he0.ne']
    exact zero_le
  · have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    have hva : Valued.v a < 1 := Valued.toNormedField.norm_lt_one_iff.1 ha
    obtain ⟨δ, hδ⟩ : ∃ δ : Multiplicative ℤ, Valued.v a = δ :=
      ⟨WithZero.unzero h0, (WithZero.coe_unzero h0).symm⟩
    have hδ1 : Multiplicative.toAdd δ < 0 := by
      have : δ < 1 := by
        rw [← WithZero.coe_lt_coe, ← hδ, WithZero.coe_one]
        exact hva
      rwa [← Multiplicative.toAdd_lt, toAdd_one] at this
    rw [hδ, hγ, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_pow,
      nsmul_eq_mul, he']
    nlinarith

/-- The logarithm is uniformly bounded on the principal units. -/
theorem exists_forall_norm_padicLog_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : k, ‖x - 1‖ < 1 → ‖padicLog x‖ ≤ M := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_lt_one_forall_norm_le hp hpk
  have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ N * ρ ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one N (abs_lt.2 ⟨by linarith, hρ1⟩)).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun x hx =>
    norm_padicLog_le_of_forall_le (le_max_right _ _) fun n => ?_⟩
  calc ‖logTerm x n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1) := norm_logTerm_le hN x n
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ρ ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hρ _ hx) _) (by positivity)
    _ ≤ M := hM ⟨n, rfl⟩
    _ ≤ max M 0 := le_max_left _ _

end
end JoshiTeich.Act1Scene1.LocalPadicLog
