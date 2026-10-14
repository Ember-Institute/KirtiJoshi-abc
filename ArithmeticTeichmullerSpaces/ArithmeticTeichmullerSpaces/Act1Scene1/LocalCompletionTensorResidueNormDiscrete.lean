/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/ResidueField.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt discrete spectral values and least attainable radius proofs
to actual tensor residue fields, using the constructed spectral norm.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueNorm

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-RESIDUE-DISCRETE-RADII
source: reviewed reference ResidueField 240--313, minpoly degree bound and
the p-adic valuation of its nonzero constant coefficient.
fidelity: proves discrete spectral values and a least attainable norm above
any positive radius. No caller-supplied discreteness certificate or hull law.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open Polynomial
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι) (I : MaximalSpectrum P.Tensor)

def residueExponent : ℕ := (Module.finrank ℚ_[p] (P.Tensor ⧸ I.asIdeal)).factorial

theorem exists_residueNorm_pow_eq_zpow {y : P.Tensor ⧸ I.asIdeal} (hy : y ≠ 0) :
    ∃ k : ℤ, P.residueNorm I y ^ P.residueExponent I = (p : ℝ) ^ k := by
  set f := minpoly ℚ_[p] y
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hpow : P.residueNorm I y ^ f.natDegree = ‖f.coeff 0‖ := by
    unfold residueNorm
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg _) hn]
  have h0 : f.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  obtain ⟨d, hd⟩ : f.natDegree ∣ P.residueExponent I :=
    Nat.dvd_factorial (minpoly.natDegree_pos hint) (minpoly.natDegree_le y)
  refine ⟨-(f.coeff 0).valuation * d, ?_⟩
  rw [hd, pow_mul, hpow, Padic.norm_eq_zpow_neg_valuation h0, ← zpow_natCast, ← zpow_mul]

theorem exists_least_residueNorm_ge {M : ℝ} (hM : 0 < M) :
    ∃ b : P.Tensor ⧸ I.asIdeal, b ≠ 0 ∧ M ≤ P.residueNorm I b ∧
      ∀ y : P.Tensor ⧸ I.asIdeal, y ≠ 0 → M ≤ P.residueNorm I y →
        P.residueNorm I b ≤ P.residueNorm I y := by
  classical
  let D := P.residueExponent I
  have hD0 : D ≠ 0 := Nat.factorial_ne_zero _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let Z : ℤ → Prop := fun k => ∃ y : P.Tensor ⧸ I.asIdeal,
    y ≠ 0 ∧ M ≤ P.residueNorm I y ∧ P.residueNorm I y ^ D = (p : ℝ) ^ k
  have hZne : ∃ k, Z k := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hp1
    let y : P.Tensor ⧸ I.asIdeal := algebraMap ℚ_[p] _ ((p : ℚ_[p]) ^ n)⁻¹
    have hy0 : y ≠ 0 := by
      change algebraMap ℚ_[p] _ ((p : ℚ_[p]) ^ n)⁻¹ ≠ 0
      rw [_root_.map_ne_zero]
      exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
    have hyn : P.residueNorm I y = (p : ℝ) ^ n := by
      rw [P.residueNorm_algebraMap, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
    obtain ⟨k, hk⟩ := P.exists_residueNorm_pow_eq_zpow I hy0
    exact ⟨k, y, hy0, hyn ▸ hn.le, hk⟩
  have hZbdd : ∃ k₀ : ℤ, ∀ k, Z k → k₀ ≤ k := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hM D)
      (inv_lt_one_of_one_lt₀ hp1 : (p : ℝ)⁻¹ < 1)
    refine ⟨-n, ?_⟩
    rintro k ⟨y, -, hMy, hk⟩
    have hlt : (p : ℝ) ^ (-(n : ℤ)) < (p : ℝ) ^ k := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, ← hk]
      exact hn.trans_le (pow_le_pow_left₀ hM.le hMy D)
    exact ((zpow_lt_zpow_iff_right₀ hp1).mp hlt).le
  obtain ⟨lb, ⟨b, hb0, hMb, hb⟩, hlb⟩ := Int.exists_least_of_bdd hZbdd hZne
  refine ⟨b, hb0, hMb, fun y hy0 hMy => ?_⟩
  obtain ⟨k, hk⟩ := P.exists_residueNorm_pow_eq_zpow I hy0
  have hle : (p : ℝ) ^ lb ≤ (p : ℝ) ^ k :=
    zpow_le_zpow_right₀ hp1.le (hlb k ⟨y, hy0, hMy, hk⟩)
  rw [← hb, ← hk] at hle
  exact (pow_le_pow_iff_left₀ (P.residueNorm_nonneg I _) (P.residueNorm_nonneg I _) hD0).mp hle

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
